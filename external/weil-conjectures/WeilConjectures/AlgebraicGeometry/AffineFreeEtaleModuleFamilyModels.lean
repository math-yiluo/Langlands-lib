/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import WeilConjectures.AlgebraicGeometry.AffineEtaleBaseChangeSystem
import WeilConjectures.AlgebraicGeometry.AffineEtaleDescentData
import WeilConjectures.ConstructibleSheaf.FreeLifting
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.Data.Finset.Order

/-!
# Common-stage models of finite affine etale free families

Source: Stacks Project, Tags 09YU (3), 095N and 03S6.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
private noncomputable def evalEquiv (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ) ⟶ F) ≃ F.obj.obj (op W) :=
  ((sheafificationAdjunction _ _).homEquiv _ _).trans
    (((ModuleCat.adj Λ).whiskerRight X.Etaleᵒᵖ).homEquiv _ _ |>.trans
      uliftYonedaEquiv)

private lemma evalEquiv_comp (W : X.Etale)
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (a : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ) ⟶ F) (b : F ⟶ G) :
    evalEquiv W G (a ≫ b) = b.hom.app (op W) (evalEquiv W F a) := by
  unfold evalEquiv
  simp only [Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_right]
  erw [Adjunction.homEquiv_naturality_right]
  exact uliftYonedaEquiv_comp _ _

/-- Extension by zero of the constant rank-one module represents evaluation. -/
noncomputable def shriekEvalEquiv (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) W.hom inferInstance).obj
      ((constantSheaf W.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ Λ)) ⟶ F) ≃ F.obj.obj (op W) := by
  let T : W.left.Etale := Etale.mk (𝟙 W.left)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ _
  let e : (MorphismProperty.Over.map ⊤ W.prop).obj T ≅ W :=
    MorphismProperty.Over.isoMk (Iso.refl W.left) (by simp [T])
  let adj := (Etale.etaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} Λ) W.hom W.prop).ofNatIsoRight
      (Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) W.hom W.prop)
  exact (adj.homEquiv _ _).trans
    (((constantSheafAdj W.left.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT).homEquiv _ _).trans
      ((ModuleCat.homEquiv.trans
        (LinearMap.ringLmapEquivSelf Λ ℕ _).toEquiv).trans
          (F.obj.mapIso e.op).symm.toLinearEquiv.toEquiv))

/-- The section equivalence is natural under postcomposition. -/
lemma shriekEvalEquiv_comp (W : X.Etale)
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (a : (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) W.hom inferInstance).obj
      ((constantSheaf W.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ Λ)) ⟶ F) (b : F ⟶ G) :
    shriekEvalEquiv W G (a ≫ b) = b.hom.app (op W) (shriekEvalEquiv W F a) := by
  let adj := (Etale.etaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} Λ) W.hom W.prop).ofNatIsoRight
      (Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) W.hom W.prop)
  let adjc := constantSheafAdj W.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (MorphismProperty.Over.mkIdTerminal @Etale W.left)
  have h1 := adj.homEquiv_naturality_right a b
  have h2 := adjc.homEquiv_naturality_right (adj.homEquiv _ _ a)
    ((Etale.localizationRestriction (ModuleCat.{u + 1} Λ) W.hom W.prop).map b)
  dsimp only [shriekEvalEquiv, Equiv.trans_apply]
  rw [h1, h2]
  let e : (MorphismProperty.Over.map ⊤ W.prop).obj (Etale.mk (𝟙 W.left)) ≅ W :=
    MorphismProperty.Over.isoMk (Iso.refl W.left) (by simp)
  let z := adjc.homEquiv _ _ (adj.homEquiv _ _ a)
  change G.obj.map e.op.inv (b.hom.app _ (z 1)) =
    b.hom.app _ (F.obj.map e.op.inv (z 1))
  exact congrArg (fun k ↦ k (z 1)) (b.hom.naturality e.op.inv).symm

private noncomputable def freeYonedaEvalEquiv (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ) ⟶ F) ≃
      F.obj.obj (op W) :=
  Sheaf.freeYonedaHomEquiv.trans (ModuleCat.homEquiv.trans
    (LinearMap.ringLmapEquivSelf Λ ℕ _).toEquiv)

private lemma freeYonedaEvalEquiv_comp (W : X.Etale)
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (a : Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ) ⟶ F) (b : F ⟶ G) :
    freeYonedaEvalEquiv W G (a ≫ b) = b.hom.app (op W) (freeYonedaEvalEquiv W F a) := by
  change Sheaf.freeYonedaHomEquiv (a ≫ b) 1 =
    b.hom.app (op W) (Sheaf.freeYonedaHomEquiv a 1)
  rw [Etale.freeYonedaHomEquiv_comp]
  rfl

private noncomputable def shriekFreeYonedaIso (W : X.Etale) :
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) W.hom inferInstance).obj
      ((constantSheaf W.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ Λ)) ≅ Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ) :=
  let e (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    (shriekEvalEquiv W F).trans (freeYonedaEvalEquiv W F).symm
  Coyoneda.ext _ _ (fun f ↦ e _ f) (fun f ↦ (e _).symm f)
    (fun f ↦ by simp) (fun f ↦ by simp) (fun f g ↦ by
      apply (shriekEvalEquiv W _).injective
      simp only [e, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
        freeYonedaEvalEquiv_comp, shriekEvalEquiv_comp])

private noncomputable def freeModelIso (W : X.Etale) :
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ) ≅
        Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ) :=
  let e (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    (evalEquiv W F).trans (freeYonedaEvalEquiv W F).symm
  Coyoneda.ext _ _ (fun f ↦ e _ f) (fun f ↦ (e _).symm f)
    (fun f ↦ by simp) (fun f ↦ by simp) (fun f g ↦ by
      apply (evalEquiv W _).injective
      simp only [e, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
        freeYonedaEvalEquiv_comp, evalEquiv_comp])

/-- Two finite affine etale families admit free-sum models at one stage.
This statement descends objects only; it makes no assertion about arrows between them.

Source: Stacks Project, Tag 09YU (3), essential surjectivity of the affine etale site
using 095N, and Tag 03S6.
(blueprint: lem-weil-pbc-affine-free-etale-family-models).

Proof:
1. Regard each U and V as an object of the full affine etale site. Apply the essential
   object-descent clause of `affineEtale_descent_data` to each of these finitely
   many objects. Nonemptiness and directedness give a common upper bound i, even
   when both families are empty. Move every object to i by the site's transition
   functors. The cartesian squares and composition comparisons identify its base
   change to the limit with the original U or V. Affineness is preserved because
   the scheme transitions and limit projections are affine.
2. For an affine etale object W, its sheaf P(W) represents evaluation on W: compose
   the sheafification adjunction, the free-module adjunction and ulift Yoneda.
   The etale lower shriek of the constant rank-one module represents the same
   evaluation, by the shriek/pullback and constant-sheaf adjunctions. The natural
   equivalences of represented functors give their unique comparison isomorphism.
   Inverse image of P(W) is P of the base-changed object: apply the upperStar/lowerStar
   adjunction and use that lowerStar evaluates on the base-changed etale object.
   This is also `Etale.upperStarFreeYonedaIso` after comparing the two free models.
3. Inverse image preserves coproducts since it is a left adjoint. Combine its
   coproduct comparison with the comparisons in step 2 to obtain eU and eV.
   In these stage models use the lower shriek of the constant rank-one module.
   This is the free sheaf by step 2. The witnesses WU and WV, their affine proofs,
   and eU and eV give the asserted common-stage models. Empty sums are handled
   by preservation of the initial object. -/
theorem exists_affine_free_etaleModule_family_models
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (n m : ℕ) (U : Fin n → c.pt.Etale) (V : Fin m → c.pt.Etale)
    (hU : ∀ k : Fin n, IsAffine (U k).left)
    (hV : ∀ k : Fin m, IsAffine (V k).left) :
    let P : c.pt.Etale → Sheaf c.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
      fun W ↦ (presheafToSheaf c.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ)
    ∃ (i : I) (WU : Fin n → (D.obj (op i)).Etale)
      (WV : Fin m → (D.obj (op i)).Etale),
      let Q : (D.obj (op i)).Etale →
          Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
        fun W ↦ (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) W.hom inferInstance).obj
          ((constantSheaf W.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ Λ))
      (∀ k, IsAffine (WU k).left) ∧ (∀ k, IsAffine (WV k).left) ∧
      Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).obj
        (∐ fun k : Fin n ↦ Q (WU k)) ≅ (∐ fun k : Fin n ↦ P (U k))) ∧
      Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).obj
        (∐ fun k : Fin m ↦ Q (WV k)) ≅ (∐ fun k : Fin m ↦ P (V k))) := by
  classical
  intro P
  obtain ⟨T, v, p, q, gamma, delta,
    _, h1, hpb, _, _, _, _, h7, _, _, h10, _, h12, _, _⟩ :=
    exists_affineEtale_baseChange_system D c hc
  obtain ⟨hdesc, _⟩ := affineEtale_descent_data D c hc T v p q gamma delta
    h1 hpb h7 h10 h12
  let Z : Fin n ⊕ Fin m → c.pt.FullAffineEtale :=
    Sum.elim (fun k ↦ ⟨U k, hU k⟩) (fun k ↦ ⟨V k, hV k⟩)
  choose idx M e using fun k ↦ hdesc (Z k)
  obtain ⟨i, hi⟩ := (Finset.univ.image idx).exists_le
  have h (k : Fin n ⊕ Fin m) : idx k ≤ i := hi _ (Finset.mem_image.mpr ⟨k, by simp, rfl⟩)
  let N (k : Fin n ⊕ Fin m) := (T (idx k) i (h k)).obj (M k)
  let W (k : Fin n ⊕ Fin m) := (N k).obj
  have ei (k : Fin n ⊕ Fin m) : (v i).obj (N k) ≅ Z k :=
    (delta (idx k) i (h k)).app (M k) ≪≫ Classical.choice (e k)
  have eW (k : Fin n ⊕ Fin m) : (c.π.app (op i)).Etale.obj (W k) ≅ (Z k).obj := by
    let hp := hpb i (N k)
    let a : ((v i).obj (N k)).obj ≅ (c.π.app (op i)).Etale.obj (W k) :=
      MorphismProperty.Over.isoMk hp.isoPullback (by
        change hp.isoPullback.hom ≫ pullback.snd _ _ = _
        exact hp.isoPullback_hom_snd)
    exact a.symm ≪≫ (fullAffineEtaleInclusion c.pt).mapIso (ei k)
  let Q : (D.obj (op i)).Etale →
      Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    fun Z ↦ (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) Z.hom inferInstance).obj
      ((constantSheaf Z.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ Λ))
  let L := Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))
  have eq (k : Fin n ⊕ Fin m) : L.obj (Q (W k)) ≅ P ((Z k).obj) :=
    L.mapIso (shriekFreeYonedaIso (W k)) ≪≫
      Etale.upperStarFreeYonedaIso (c.π.app (op i)) (W k) ≪≫
      Etale.freeYonedaMapIso (eW k) ≪≫ (freeModelIso ((Z k).obj)).symm
  refine ⟨i, fun k ↦ W (.inl k), fun k ↦ W (.inr k),
    fun k ↦ (N (.inl k)).property, fun k ↦ (N (.inr k)).property, ?_, ?_⟩
  · exact ⟨PreservesCoproduct.iso L (fun k : Fin n ↦ Q (W (.inl k))) ≪≫
      Sigma.mapIso (fun k ↦ eq (.inl k))⟩
  · exact ⟨PreservesCoproduct.iso L (fun k : Fin m ↦ Q (W (.inr k))) ≪≫
      Sigma.mapIso (fun k ↦ eq (.inr k))⟩

end AlgebraicGeometry.Scheme
