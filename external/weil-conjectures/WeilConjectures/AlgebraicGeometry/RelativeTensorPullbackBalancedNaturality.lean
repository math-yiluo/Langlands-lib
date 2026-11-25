/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.AlgebraicGeometry.InverseImageModuleFunctor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.BalancedTensorComparisonIsIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Naturality of the ordinary balanced tensor comparison

Source: Stacks Project, Cohomology, Lemma 20.27.4 (Tag 08DE), proof.
(blueprint: lem-pc-relative-tensor-pullback-balanced-naturality)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory MonoidalCategory TopologicalSpace
open scoped ChangeOfRings


namespace SheafOfModules

noncomputable section

variable {Z : TopCat.{u}}
  {R B : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u}}

set_option hygiene false in
local notation "𝓡" E =>
  (sheafCompose (Opens.grothendieckTopology Z) (forget₂ CommRingCat.{u} RingCat.{u})).obj E
set_option hygiene false in
local notation "𝓻" a =>
  (sheafCompose (Opens.grothendieckTopology Z) (forget₂ CommRingCat.{u} RingCat.{u})).map a

private def balancedPure (R : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u})
    (M N : SheafOfModules.{u} (𝓡 R)) :
    M.val ⊗ N.val ⟶
      ((monoidalCategory R).tensorObj M N).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 R).obj)).unit.app (M.val ⊗ N.val) ≫
    (tensorObjIsoSheafification M N).inv.val

private def balancedUnit (α : R ⟶ B) (N : SheafOfModules.{u} (𝓡 R)) :
    changeOfRingsPresheaf.{u, u, u} α N ⟶
      (PresheafOfModules.restrictScalars (𝟙 (𝓡 B).obj)).obj
        (changeOfRings.{u, u, u} α N).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
    (changeOfRingsPresheaf.{u, u, u} α N)

set_option maxHeartbeats 800000 in
-- Bilinearity involves both coefficient-ring actions and the module sheafification unit.
private def balancedPairing (α : R ⟶ B)
    (M : SheafOfModules.{u} (𝓡 B)) (N : SheafOfModules.{u} (𝓡 R))
    (W : (Opens Z)ᵒᵖ) :
    ((restrictScalars (𝓻 α)).obj M).val.obj W →ₗ[R.obj.obj W]
      N.val.obj W →ₗ[R.obj.obj W]
        ((restrictScalars (𝓻 α)).obj
          ((monoidalCategory B).tensorObj M (changeOfRings.{u, u, u} α N))).val.obj W :=
  LinearMap.mk₂ (R.obj.obj W)
    (fun m n ↦ (balancedPure B M (changeOfRings.{u, u, u} α N)).app W
      (m ⊗ₜ[B.obj.obj W] (balancedUnit α N).app W
        ((1 : B.obj.obj W) ⊗ₜ[R.obj.obj W, (α.hom.app W).hom] n)))
    (by intros; rw [TensorProduct.add_tmul, map_add])
    (by
      intro r m n
      change (balancedPure B M (changeOfRings.{u, u, u} α N)).app W
        ((α.hom.app W r • (show M.val.obj W from m)) ⊗ₜ[B.obj.obj W] _) = _
      rw [← TensorProduct.smul_tmul', map_smul]
      rfl)
    (by intros; rw [TensorProduct.tmul_add, map_add, TensorProduct.tmul_add, map_add])
    (by
      intro r m n
      let : Module (R.obj.obj W) (B.obj.obj W) := Module.compHom _ (α.hom.app W).hom
      change (balancedPure B M (changeOfRings.{u, u, u} α N)).app W
        ((show M.val.obj W from m) ⊗ₜ[B.obj.obj W]
          (balancedUnit α N).app W
            ((1 : B.obj.obj W) ⊗ₜ[R.obj.obj W] (r • n))) = _
      rw [TensorProduct.tmul_smul]
      change (balancedPure B M (changeOfRings.{u, u, u} α N)).app W
        ((show M.val.obj W from m) ⊗ₜ[B.obj.obj W]
          (balancedUnit α N).app W ((α.hom.app W r) •
            ((1 : B.obj.obj W) ⊗ₜ[R.obj.obj W, (α.hom.app W).hom] n))) = _
      rw [map_smul, TensorProduct.tmul_smul (R := B.obj.obj W) (R' := B.obj.obj W)
        (M := M.val.obj W)
        (N := (changeOfRings.{u, u, u} α N).val.obj W), map_smul]
      rfl)

private theorem balancedPairing_natural (α : R ⟶ B)
    (M : SheafOfModules.{u} (𝓡 B)) (N : SheafOfModules.{u} (𝓡 R))
    {U V : (Opens Z)ᵒᵖ} (i : U ⟶ V)
    (m : ((restrictScalars (𝓻 α)).obj M).val.obj U) (n : N.val.obj U) :
    balancedPairing α M N V (((restrictScalars (𝓻 α)).obj M).val.map i m) (N.val.map i n) =
      (((restrictScalars (𝓻 α)).obj
        ((monoidalCategory B).tensorObj M (changeOfRings.{u, u, u} α N))).val.map i
          (balancedPairing α M N U m n)) := by
  have hn := PresheafOfModules.naturality_apply (balancedUnit α N) i
    ((1 : B.obj.obj U) ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] n)
  change (balancedUnit α N).app V (changeOfRingsMap.{u, u, u} α N i _) = _ at hn
  erw [Classical.choose_spec (exists_changeOfRingsMap.{u, u, u} α N i)] at hn
  simp only [map_one] at hn
  have hp := PresheafOfModules.naturality_apply
    (balancedPure B M (changeOfRings.{u, u, u} α N)) i
      (m ⊗ₜ[B.obj.obj U] (balancedUnit α N).app U
        ((1 : B.obj.obj U) ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] n))
  change (balancedPure B M (changeOfRings.{u, u, u} α N)).app V
    (M.val.map i m ⊗ₜ[B.obj.obj V]
      (changeOfRings.{u, u, u} α N).val.map i ((balancedUnit α N).app U _)) = _ at hp
  change (balancedPure B M (changeOfRings.{u, u, u} α N)).app V
    (M.val.map i m ⊗ₜ[B.obj.obj V] (balancedUnit α N).app V _) = _
  rw [hn]
  exact hp

@[irreducible] private def balancedMap (α : R ⟶ B)
    (M : SheafOfModules.{u} (𝓡 B)) (N : SheafOfModules.{u} (𝓡 R)) :
    (monoidalCategory R).tensorObj ((restrictScalars (𝓻 α)).obj M) N ⟶
      (restrictScalars (𝓻 α)).obj
        ((monoidalCategory B).tensorObj M (changeOfRings.{u, u, u} α N)) :=
  Classical.choose (tensor_bilinear_universal R ((restrictScalars (𝓻 α)).obj M) N
    ((restrictScalars (𝓻 α)).obj
      ((monoidalCategory B).tensorObj M (changeOfRings.{u, u, u} α N)))
    (balancedPairing α M N) (balancedPairing_natural α M N))

private theorem balancedMap_pure (α : R ⟶ B)
    (M : SheafOfModules.{u} (𝓡 B)) (N : SheafOfModules.{u} (𝓡 R))
    (W : (Opens Z)ᵒᵖ) (m : M.val.obj W) (n : N.val.obj W) :
    (balancedMap α M N).val.app W
      ((balancedPure R ((restrictScalars (𝓻 α)).obj M) N).app W
        (m ⊗ₜ[R.obj.obj W] n)) = balancedPairing α M N W m n := by
  unfold balancedMap
  exact (Classical.choose_spec (tensor_bilinear_universal R ((restrictScalars (𝓻 α)).obj M) N
    ((restrictScalars (𝓻 α)).obj
      ((monoidalCategory B).tensorObj M (changeOfRings.{u, u, u} α N)))
    (balancedPairing α M N) (balancedPairing_natural α M N))).1 W m n

private theorem balancedPure_natural
    (R : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u})
    {M M' N N' : SheafOfModules.{u} (𝓡 R)} (f : M ⟶ M') (g : N ⟶ N') :
    balancedPure R M N ≫ ((monoidalCategory R).tensorHom f g).val =
      (f.val ⊗ₘ g.val) ≫ balancedPure R M' N' := by
  let := monoidalCategory R
  let S := PresheafOfModules.sheafification (𝟙 (𝓡 R).obj)
  have h : (f ⊗ₘ g) ≫ (tensorObjIsoSheafification M' N').hom =
      (tensorObjIsoSheafification M N).hom ≫ S.map (f.val ⊗ₘ g.val) := by
    erw [tensorHom_def, Category.assoc,
      whiskerLeft_tensorObjIsoSheafification_hom (R := R) M' g,
      ← Category.assoc, whiskerRight_tensorObjIsoSheafification_hom (R := R) f N,
      Category.assoc, ← Functor.map_comp, ← tensorHom_def]
  have h' : (tensorObjIsoSheafification M N).inv ≫ (f ⊗ₘ g) =
      S.map (f.val ⊗ₘ g.val) ≫ (tensorObjIsoSheafification M' N').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hv := congrArg SheafOfModules.Hom.val h'
  change (tensorObjIsoSheafification M N).inv.val ≫ (f ⊗ₘ g).val =
    (S.map (f.val ⊗ₘ g.val)).val ≫ (tensorObjIsoSheafification M' N').inv.val at hv
  have hn := (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 R).obj)).unit.naturality
    (f.val ⊗ₘ g.val)
  change (f.val ⊗ₘ g.val) ≫ _ = _ ≫ (S.map (f.val ⊗ₘ g.val)).val at hn
  unfold balancedPure
  erw [Category.assoc, hv, ← Category.assoc, ← hn]
  rfl

private theorem balancedPure_tensorHom_app
    (R : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u})
    {M M' N N' : SheafOfModules.{u} (𝓡 R)} (f : M ⟶ M') (g : N ⟶ N')
    (W : (Opens Z)ᵒᵖ) (m : M.val.obj W) (n : N.val.obj W) :
    ((monoidalCategory R).tensorHom f g).val.app W
        ((balancedPure R M N).app W (m ⊗ₜ[R.obj.obj W] n)) =
      (balancedPure R M' N').app W
        (f.val.app W m ⊗ₜ[R.obj.obj W] g.val.app W n) :=
  congrArg (fun t ↦ (t.app W).hom (m ⊗ₜ[R.obj.obj W] n)) (balancedPure_natural R f g)

private theorem balancedPure_ext
    (R : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u})
    (M N P : SheafOfModules.{u} (𝓡 R))
    {f g : (monoidalCategory R).tensorObj M N ⟶ P}
    (h : ∀ (W : (Opens Z)ᵒᵖ) (m : M.val.obj W) (n : N.val.obj W),
      f.val.app W ((balancedPure R M N).app W (m ⊗ₜ[R.obj.obj W] n)) =
        g.val.app W ((balancedPure R M N).app W (m ⊗ₜ[R.obj.obj W] n))) : f = g := by
  apply (cancel_epi (tensorObjIsoSheafification M N).inv).mp
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 (𝓡 R).obj)).injective
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  exact h W m n

private theorem balancedUnit_map (α : R ⟶ B)
    {N N' : SheafOfModules.{u} (𝓡 R)} (g : N ⟶ N')
    (W : (Opens Z)ᵒᵖ) (n : N.val.obj W) :
    (changeOfRingsHom.{u, u, u} α N g).val.app W ((balancedUnit α N).app W
      ((1 : B.obj.obj W) ⊗ₜ[R.obj.obj W, (α.hom.app W).hom] n)) =
      (balancedUnit α N').app W ((1 : B.obj.obj W) ⊗ₜ[R.obj.obj W, (α.hom.app W).hom]
        (g.val.app W n)) := by
  let p : changeOfRingsPresheaf.{u, u, u} α N ⟶ changeOfRingsPresheaf.{u, u, u} α N' :=
    { app := fun W ↦ (ModuleCat.extendScalars (α.hom.app W).hom).map (g.val.app W)
      naturality := changeOfRingsHom_naturality.{u, u, u} α N g }
  have hn := (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.naturality p
  have hx := congrArg (fun t ↦ (t.app W).hom
    ((1 : B.obj.obj W) ⊗ₜ[R.obj.obj W, (α.hom.app W).hom] n)) hn
  change (balancedUnit α N').app W
    ((ModuleCat.extendScalars (α.hom.app W).hom).map (g.val.app W) _) =
      (changeOfRingsHom.{u, u, u} α N g).val.app W ((balancedUnit α N).app W _) at hx
  rw [ModuleCat.ExtendScalars.map_tmul] at hx
  exact hx.symm

-- Compose the sectionwise naturality equalities without rewriting the nested sheaf terms.
private theorem balancedMap_natural (α : R ⟶ B)
    {M M' : SheafOfModules.{u} (𝓡 B)} {N N' : SheafOfModules.{u} (𝓡 R)}
    (f : M ⟶ M') (g : N ⟶ N') :
    (monoidalCategory R).tensorHom ((restrictScalars (𝓻 α)).map f) g ≫
        balancedMap α M' N' =
      balancedMap α M N ≫ (restrictScalars (𝓻 α)).map
        ((monoidalCategory B).tensorHom f (changeOfRingsHom.{u, u, u} α N g)) := by
  apply balancedPure_ext R ((restrictScalars (𝓻 α)).obj M) N
  intro W m n
  refine (congrArg (fun x ↦ (balancedMap α M' N').val.app W x)
    (balancedPure_tensorHom_app R ((restrictScalars (𝓻 α)).map f) g W m n)).trans ?_
  refine (balancedMap_pure α M' N' W (f.val.app W m) (g.val.app W n)).trans ?_
  symm
  refine (congrArg (fun x ↦
    ((monoidalCategory B).tensorHom f (changeOfRingsHom.{u, u, u} α N g)).val.app W x)
      (balancedMap_pure α M N W m n)).trans ?_
  refine (balancedPure_tensorHom_app B f (changeOfRingsHom.{u, u, u} α N g) W m
    ((balancedUnit α N).app W
      ((1 : B.obj.obj W) ⊗ₜ[R.obj.obj W, (α.hom.app W).hom] n))).trans ?_
  exact congrArg (fun x ↦ (balancedPure B M' (changeOfRings.{u, u, u} α N')).app W
    (f.val.app W m ⊗ₜ[B.obj.obj W] x)) (balancedUnit_map α g W n)

private theorem balancedChangeHom_id (α : R ⟶ B) (N : SheafOfModules.{u} (𝓡 R)) :
    changeOfRingsHom.{u, u, u} α N (𝟙 N) = 𝟙 (changeOfRings.{u, u, u} α N) := by
  unfold changeOfRingsHom
  have h : (show changeOfRingsPresheaf.{u, u, u} α N ⟶ changeOfRingsPresheaf.{u, u, u} α N
      from { app := fun W ↦
               (ModuleCat.extendScalars (α.hom.app W).hom).map ((𝟙 N : N ⟶ N).val.app W)
             naturality := changeOfRingsHom_naturality.{u, u, u} α N (𝟙 N) }) = 𝟙 _ := by
    apply PresheafOfModules.hom_ext
    intro W
    exact (ModuleCat.extendScalars (α.hom.app W).hom).map_id (N.val.obj W)
  exact (congrArg (PresheafOfModules.sheafification (𝟙 (𝓡 B).obj)).map h).trans
    ((PresheafOfModules.sheafification (𝟙 (𝓡 B).obj)).map_id _)

private theorem balancedForget_map (α : R ⟶ B)
    {M N : SheafOfModules.{u} (𝓡 B)} (a : M ⟶ N) :
    (toSheaf (𝓡 R)).map ((restrictScalars (𝓻 α)).map a) = (toSheaf (𝓡 B)).map a := rfl

private theorem balancedMap_isIso (α : R ⟶ B)
    (M : SheafOfModules.{u} (𝓡 B)) (N : SheafOfModules.{u} (𝓡 R)) :
    IsIso (balancedMap α M N) :=
  balancedTensorComparison_isIso α M N (balancedMap α M N) (balancedMap_pure α M N)

end
end SheafOfModules

private theorem inverse_naturality {C : Type*} [Category C]
    {A A' B B' : C} (e : A ≅ B) (e' : A' ≅ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : b ≫ e'.inv = e.inv ≫ a) : a ≫ e'.hom = e.hom ≫ b := by
  apply (cancel_mono e'.inv).1
  rw [Category.assoc, e'.hom_inv_id, Category.comp_id, Category.assoc, h,
    ← Category.assoc, e.hom_inv_id, Category.id_comp]

namespace AlgebraicGeometry.Scheme

-- Comparing tensors over two rings requires explicit coefficient-forgetting reductions.
/-- The balanced tensor identity for ordinary module sheaves is natural in both variables.
Source: Stacks Project, Cohomology, Lemma 20.27.4 (Tag 08DE), proof.

Proof: write R = f-inverse O_S and B = O_X. On sections, the balanced map
M tensor_B (B tensor_R N) -> M restricted to R tensor_R N sends
m tensor (b tensor n) to (b*m) tensor n. Its inverse sends m tensor n to
m tensor (1 tensor n). Additivity and the B- and R-balancing relations make
both maps well defined. Their composites are the identity on pure tensors,
and pure tensors generate the section tensor products. Both maps commute
with restrictions. Tensoring with module sheafification agrees with
sheafifying the tensor presheaf, so replacing the scalar-extension presheaf
by its sheafification preserves this comparison. Underlying module
sheafification is abelian sheafification, independent of the coefficient ring.
The sheafification universal property therefore gives inverse maps of
abelian sheaves. The construction is natural in each variable:
a B-linear map commutes with multiplication by b, and an R-linear map
commutes with forming b tensor n. Transport the second factor along hG;
hGmap identifies its morphisms with the tensor pullback morphisms. Thus the
two displayed naturality equalities hold. This works for arbitrary modules,
including zero modules, zero coefficient rings, and the empty scheme. No
complex, differential, coproduct, flatness or derived category is involved.
(blueprint: lem-pc-relative-tensor-pullback-balanced-naturality) -/
theorem exists_relativeTensorPullback_balanced_natural
    {X S : Scheme.{u}} (f : X ⟶ S)
    (G : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hG : ∀ M, G.obj M = Modules.tensorPullbackObj f M)
    (hGmap : ∀ {M N} (a : M ⟶ N),
      G.map a = eqToHom (hG M) ≫ Modules.tensorPullbackMap f a ≫ eqToHom (hG N).symm) :
    let R := ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (TopCat.Sheaf.inverseImageRing f.base S.sheaf))
    let U := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
    let V := SheafOfModules.toSheaf R
    let H := SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).map (Modules.tensorPullbackRingMap f))
    let I := TopCat.Sheaf.inverseImageModuleFunctor f.base S.sheaf
    let T := @curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)
    let T' := @curriedTensor _ _ (SheafOfModules.monoidalCategory
      (TopCat.Sheaf.inverseImageRing f.base S.sheaf))
    ∃ e : ∀ M N, U.obj ((T.obj M).obj (G.obj N)) ≅
        V.obj ((T'.obj (H.obj M)).obj (I.obj N)),
      (∀ M M' (a : M ⟶ M') N,
        U.map ((T.map a).app (G.obj N)) ≫ (e M' N).hom =
          (e M N).hom ≫ V.map ((T'.map (H.map a)).app (I.obj N))) ∧
      (∀ M N N' (b : N ⟶ N'),
        U.map ((T.obj M).map (G.map b)) ≫ (e M N').hom =
          (e M N).hom ≫ V.map ((T'.obj (H.obj M)).map (I.map b))) := by
  classical
  have hG' : G = Modules.tensorPullback f :=
    CategoryTheory.Functor.ext hG (fun _ _ a ↦ hGmap a)
  subst G
  dsimp only
  let R := ((sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (TopCat.Sheaf.inverseImageRing f.base S.sheaf))
  let U := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
  let V := SheafOfModules.toSheaf R
  let H := SheafOfModules.restrictScalars
    ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).map (Modules.tensorPullbackRingMap f))
  let I := TopCat.Sheaf.inverseImageModuleFunctor f.base S.sheaf
  let T := @curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)
  let T' := @curriedTensor _ _ (SheafOfModules.monoidalCategory
    (TopCat.Sheaf.inverseImageRing f.base S.sheaf))
  let c (M : X.Modules) (N : S.Modules) :=
    SheafOfModules.balancedMap (Modules.tensorPullbackRingMap f) M (I.obj N)
  have hc (M : X.Modules) (N : S.Modules) : IsIso (c M N) :=
    SheafOfModules.balancedMap_isIso (Modules.tensorPullbackRingMap f) M (I.obj N)
  let e (M : X.Modules) (N : S.Modules) :
      U.obj ((T.obj M).obj ((Modules.tensorPullback f).obj N)) ≅
        V.obj ((T'.obj (H.obj M)).obj (I.obj N)) :=
    (V.mapIso (asIso (c M N))).symm
  refine ⟨e, ?_, ?_⟩
  · intro M M' a N
    have hn := SheafOfModules.balancedMap_natural (Modules.tensorPullbackRingMap f)
      a (𝟙 (I.obj N))
    have hv := congrArg V.map hn
    dsimp only [V, R] at hv
    simp only [Functor.map_comp] at hv
    simp only [SheafOfModules.balancedChangeHom_id, tensorHom_id] at hv
    rw [SheafOfModules.balancedForget_map] at hv
    have hn' : V.map ((T'.map (H.map a)).app (I.obj N)) ≫ V.map (c M' N) =
        V.map (c M N) ≫ U.map ((T.map a).app ((Modules.tensorPullback f).obj N)) := by
      exact hv
    exact inverse_naturality (e M N) (e M' N)
      (U.map ((T.map a).app ((Modules.tensorPullback f).obj N)))
      (V.map ((T'.map (H.map a)).app (I.obj N))) hn'
  · intro M N N' b
    have hn := SheafOfModules.balancedMap_natural (Modules.tensorPullbackRingMap f)
      (𝟙 M) (I.map b)
    have hv := congrArg V.map hn
    dsimp only [V, R] at hv
    simp only [Functor.map_comp] at hv
    simp only [CategoryTheory.Functor.map_id, id_tensorHom] at hv
    rw [SheafOfModules.balancedForget_map] at hv
    have hn' : V.map ((T'.obj (H.obj M)).map (I.map b)) ≫ V.map (c M N') =
        V.map (c M N) ≫ U.map ((T.obj M).map ((Modules.tensorPullback f).map b)) := by
      exact hv
    exact inverse_naturality (e M N) (e M N')
      (U.map ((T.obj M).map ((Modules.tensorPullback f).map b)))
      (V.map ((T'.obj (H.obj M)).map (I.map b))) hn'

end AlgebraicGeometry.Scheme
