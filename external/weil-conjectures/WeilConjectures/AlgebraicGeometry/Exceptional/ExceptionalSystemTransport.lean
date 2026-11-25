/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemInterfaces
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSiteOriginComparison
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalProperOpenOriginComparison
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalProOriginExactLinear
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalOriginAdjunctionEvaluation

/-! # Exceptional adjunction on strict pro-etale coefficient systems

The geometric existence theorem transports the actual etale adjunction.
-/

@[expose] public noncomputable section

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace CategoryTheory
universe a b x y av bv xv yv
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
  {F : A ⥤ B} {G : B ⥤ A}
private def reverseHom (adj : F ⊣ G) (M : B) (Q : A)
    [IsIso (adj.counit.app M)] [IsIso (adj.unit.app Q)] :
    (G.obj M ⟶ Q) ≃ (M ⟶ F.obj Q) where
  toFun u := inv (adj.counit.app M) ≫ F.map u
  invFun k := G.map k ≫ inv (adj.unit.app Q)
  left_inv u := by
    have he : G.map (inv (adj.counit.app M)) = adj.unit.app (G.obj M) := by
      apply (cancel_mono (G.map (adj.counit.app M))).mp
      simp only [← Functor.map_comp, IsIso.inv_hom_id, Functor.map_id]
      exact (adj.right_triangle_components M).symm
    simp only [Functor.map_comp, he, Category.assoc]
    have hn := adj.unit.naturality u
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    rw [← Category.assoc, ← hn]
    simp
  right_inv k := by
    have he : F.map (inv (adj.unit.app Q)) = adj.counit.app (F.obj Q) := by
      apply (cancel_epi (F.map (adj.unit.app Q))).mp
      simp only [← Functor.map_comp, IsIso.hom_inv_id, Functor.map_id]
      exact (adj.left_triangle_components Q).symm
    simp only [Functor.map_comp, he]
    have hn := adj.counit.naturality k
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    rw [hn]
    simp

variable {X : Type x} [Category.{xv} X] {Y : Type y} [Category.{yv} Y]
  {CX : A ⥤ X} {VX : X ⥤ A} {CY : B ⥤ Y} {VY : Y ⥤ B}
  (adj : F ⊣ G) (adjX : CX ⊣ VX) (adjY : CY ⊣ VY)
  (FP : X ⥤ Y) (PX : ObjectProperty X) (PY : ObjectProperty Y)
  (kappa : VX ⋙ F ⋙ CY ⟶ FP)
  (hleft : ∀ M, PX M → PY (FP.obj M))
  (hright : ∀ N, PY N → PX ((VY ⋙ G ⋙ CX).obj N))
  (hk : ∀ M, PX M → IsIso (kappa.app M))
  (hc : ∀ M, PX M → IsIso (adjX.counit.app M))
  (hu : ∀ N, PY N → IsIso (adjX.unit.app (G.obj (VY.obj N))))

private def originEquiv (M : PX.FullSubcategory) (N : PY.FullSubcategory) :
    ((PY.lift (PX.ι ⋙ FP) (fun M ↦ hleft M.obj M.property)).obj M ⟶ N) ≃
      (M ⟶ (PX.lift (PY.ι ⋙ (VY ⋙ G ⋙ CX))
        (fun N ↦ hright N.obj N.property)).obj N) := by
  letI := hk M.obj M.property
  have := hc M.obj M.property
  letI := hu N.obj N.property
  exact PY.fullyFaithfulι.homEquiv.trans
    ((asIso (kappa.app M.obj)).symm.homFromEquiv.trans
      ((adjY.homEquiv _ _).trans ((adj.homEquiv _ _).trans
        ((reverseHom adjX M.obj (G.obj (VY.obj N.obj))).trans
          (PX.fullyFaithfulι.homEquiv (X := M)
            (Y := (PX.lift (PY.ι ⋙ (VY ⋙ G ⋙ CX))
              (fun N ↦ hright N.obj N.property)).obj N)).symm))))

private theorem originEquiv_left
    {M M' : PX.FullSubcategory} {N : PY.FullSubcategory} (f : M ⟶ M')
    (h : (PY.lift (PX.ι ⋙ FP) (fun M ↦ hleft M.obj M.property)).obj M' ⟶ N) :
    originEquiv adj adjX adjY FP PX PY kappa hleft hright hk hc hu M N
      ((PY.lift (PX.ι ⋙ FP) (fun M ↦ hleft M.obj M.property)).map f ≫ h) =
    f ≫ originEquiv adj adjX adjY FP PX PY kappa hleft hright hk hc hu M' N h := by
  have := hc M.obj M.property
  have := hc M'.obj M'.property
  apply ObjectProperty.hom_ext
  change inv (adjX.counit.app M.obj) ≫ CX.map
    (adj.homEquiv _ _ (adjY.homEquiv _ _
      (kappa.app M.obj ≫ FP.map f.hom ≫ h.hom))) = _
  have hn := kappa.naturality f.hom
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, ← hn, Category.assoc,
    adjY.homEquiv_naturality_left, adj.homEquiv_naturality_left, CX.map_comp]
  change inv (adjX.counit.app M.obj) ≫ CX.map (VX.map f.hom) ≫ _ = _
  have hn := adjX.counit.naturality f.hom
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  have hi : inv (adjX.counit.app M.obj) ≫ CX.map (VX.map f.hom) =
      f.hom ≫ inv (adjX.counit.app M'.obj) := by
    have := hc M.obj M.property
    have := hc M'.obj M'.property
    apply (cancel_mono (adjX.counit.app M'.obj)).mp
    simpa only [Category.assoc, IsIso.inv_hom_id_assoc, IsIso.inv_hom_id,
      Category.comp_id] using congrArg (inv (adjX.counit.app M.obj) ≫ ·) hn
  rw [← Category.assoc, hi, Category.assoc]
  rfl

private theorem originEquiv_right
    {M : PX.FullSubcategory} {N N' : PY.FullSubcategory}
    (h : (PY.lift (PX.ι ⋙ FP) (fun M ↦ hleft M.obj M.property)).obj M ⟶ N)
    (f : N ⟶ N') :
    originEquiv adj adjX adjY FP PX PY kappa hleft hright hk hc hu M N' (h ≫ f) =
    originEquiv adj adjX adjY FP PX PY kappa hleft hright hk hc hu M N h ≫
      (PX.lift (PY.ι ⋙ (VY ⋙ G ⋙ CX))
        (fun N ↦ hright N.obj N.property)).map f := by
  have := hc M.obj M.property
  apply ObjectProperty.hom_ext
  change inv (adjX.counit.app M.obj) ≫ CX.map
    (adj.homEquiv _ _ (adjY.homEquiv _ _ (kappa.app M.obj ≫ h.hom ≫ f.hom))) = _
  rw [← Category.assoc, adjY.homEquiv_naturality_right,
    adj.homEquiv_naturality_right, CX.map_comp, ← Category.assoc]
  rfl

private def originAdjunction :
    PY.lift (PX.ι ⋙ FP) (fun M ↦ hleft M.obj M.property) ⊣
      PX.lift (PY.ι ⋙ (VY ⋙ G ⋙ CX)) (fun N ↦ hright N.obj N.property) :=
  Adjunction.mkOfHomEquiv {
    homEquiv := originEquiv adj adjX adjY FP PX PY kappa hleft hright hk hc hu
    homEquiv_naturality_left_symm := by
      intro M' M N f h
      apply (originEquiv adj adjX adjY FP PX PY kappa hleft hright hk hc hu M' N).injective
      rw [Equiv.apply_symm_apply,
        originEquiv_left adj adjX adjY FP PX PY kappa hleft hright hk hc hu,
        Equiv.apply_symm_apply]
    homEquiv_naturality_right :=
      originEquiv_right adj adjX adjY FP PX PY kappa hleft hright hk hc hu }

private theorem originAdjunction_transpose (M : PX.FullSubcategory) (N : PY.FullSubcategory)
    (h : (PY.lift (PX.ι ⋙ FP) (fun M ↦ hleft M.obj M.property)).obj M ⟶ N) :
    CX.map (adj.homEquiv (VX.obj M.obj) (VY.obj N.obj)
      (adjY.unit.app (F.obj (VX.obj M.obj)) ≫ VY.map (kappa.app M.obj ≫ h.hom))) =
    adjX.counit.app M.obj ≫
      ((originAdjunction adj adjX adjY FP PX PY kappa hleft hright hk hc hu).homEquiv
        M N h).hom := by
  have := hc M.obj M.property
  simp only [originAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  change _ = adjX.counit.app M.obj ≫
    (originEquiv adj adjX adjY FP PX PY kappa hleft hright hk hc hu M N h).hom
  change _ = adjX.counit.app M.obj ≫ inv (adjX.counit.app M.obj) ≫ _
  rw [IsIso.hom_inv_id_assoc]
  rw [adjY.homEquiv_unit]
  rfl
private def makeOriginAdjunction :
    ExceptionalOriginAdjunction adj adjX adjY FP PX PY kappa where
  leftStable := hleft
  rightStable := hright
  adjunction := originAdjunction adj adjX adjY FP PX PY kappa hleft hright hk hc hu
  transpose := originAdjunction_transpose adj adjX adjY FP PX PY kappa hleft hright hk hc hu
end CategoryTheory

namespace AlgebraicGeometry
variable {O : Type (u + 1)} [CommRing O] {ell : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  {S : StrictEtaleCompactSupport O ell c}
  (G : StrictEtaleExceptionalAdjoint O ell c S)
  (CX : ExceptionalSystemSiteComparison O ell X S.PX)
  (CY : ExceptionalSystemSiteComparison O ell Y S.PY)

private theorem exceptionalSystemRight_lowerBound
    (hX : ExceptionalSystemSiteEquivalence CX)
    (hY : ExceptionalSystemSiteEquivalence CY) :
    ∃ c_f : ℕ, ∀ (a : ℤ) N, CY.origin N → N.IsGE a →
      ((exceptionalSystemRight G CX CY).obj N).IsGE (a - c_f) := by
  obtain ⟨d, hd⟩ := G.property.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨d, ?_⟩
  intro a N _hN ha
  exact hX.inverseBound (a - d) _ (hd a _ (hY.directBound a N ha))

private theorem exceptionalSystemRight_normalized
    (hX : ExceptionalSystemSiteEquivalence CX)
    (hY : ExceptionalSystemSiteEquivalence CY) (N) (hN : CY.origin N)
    (hn : IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
      O ell CY.proEvaluation N) :
    IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
      O ell CX.proEvaluation ((exceptionalSystemRight G CX CY).obj N) := by
  obtain ⟨a, ha⟩ := hN.1
  have hV := hY.directBound a N ha
  obtain ⟨hG, hnorm⟩ := G.property.2.2.2.2.2.2.2.2.2.2.2 _
    ⟨a, hV⟩ (hY.directNormalized N hN hn)
  intro m n h
  exact hX.inverseNormalized _ hG (fun {_ _} h ↦ hnorm h) h

end AlgebraicGeometry
