/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarAbelianExtFactorization
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # The comparison obtained by forgetting the inverse-image unit

Source: Stacks Project, Tag 0096, lemma-pullback-pushforward-adjoint.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme
open Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Sheaf.monoidalCategory

private theorem coeffAdj (k : Type u) [Field k] :
    (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).IsLeftAdjoint := by
  let r : ℤ →+* k := Int.castRingHom k
  let U := ModuleCat.restrictScalars.{u} r
  let V := forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}
  have : U.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u} r).isLeftAdjoint
  exact inferInstanceAs (U ⋙ V).IsLeftAdjoint
attribute [local instance] coeffAdj
private noncomputable def scalarForgetAdj (k : Type u) [Field k] (X : Scheme.{u}) :
    scalarAbelianForget k X ⊣ sheafCompose (Opens.grothendieckTopology X)
      (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).rightAdjoint :=
  ((Adjunction.ofIsLeftAdjoint (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u})).whiskerRight
    X.Opensᵒᵖ).restrictFullyFaithful
      (fullyFaithfulSheafToPresheaf _ _) (fullyFaithfulSheafToPresheaf _ _)
      (Iso.refl _) (Iso.refl _)


/-- The abelian adjunct of the forgotten scalar inverse-image adjunction unit.
Source: Stacks Project, Tag 0096.
(blueprint: new-sc-scalar-forget-pullback-comparison-isIso). -/
noncomputable def scalarForgetPullbackComparison (k : Type u) [Field k]
    {X Y : Scheme.{u}} (a : Y ⟶ X) :
    scalarAbelianForget k X ⋙ (Opens.map a.base).sheafPullback AddCommGrpCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) ⟶
      scalarInverseImage (k := k) a ⋙ scalarAbelianForget k Y where
  app F :=
    (((Opens.map a.base).sheafAdjunctionContinuous AddCommGrpCat.{u} _ _).homEquiv
      _ _).symm ((scalarAbelianForget k X).map
        (((Opens.map a.base).sheafAdjunctionContinuous (ModuleCat.{u} k) _ _).unit.app F))
  naturality {F G} f := by
    let b := (Opens.map a.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
    let s := (Opens.map a.base).sheafAdjunctionContinuous (ModuleCat.{u} k)
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
    apply (b.homEquiv _ _).injective
    dsimp only [Functor.comp_map]
    rw [b.homEquiv_naturality_left, b.homEquiv_naturality_right]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change (scalarAbelianForget k X).map f ≫ (scalarAbelianForget k X).map
      (s.unit.app G) = (scalarAbelianForget k X).map (s.unit.app F) ≫
        (scalarAbelianForget k X).map
          ((Opens.map a.base).sheafPushforwardContinuous (ModuleCat.{u} k) _ _ |>.map
            ((scalarInverseImage a).map f))
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg ((scalarAbelianForget k X).map) (s.unit.naturality f)

/-- Adjunction compatibility holds before asserting invertibility of the comparison.
Source: Stacks Project, Tag 0096.
(blueprint: new-sc-scalar-forget-pullback-comparison-isIso). -/
theorem scalarForgetPullbackComparison_adjunct (k : Type u) [Field k]
    {X Y : Scheme.{u}} (a : Y ⟶ X) (F : KSheaf X k) (G : KSheaf Y k)
    (q : (scalarInverseImage a).obj F ⟶ G) :
    (((Opens.map a.base).sheafAdjunctionContinuous AddCommGrpCat.{u} _ _).homEquiv
      _ _) ((scalarForgetPullbackComparison k a).app F ≫ (scalarAbelianForget k Y).map q) =
      (scalarAbelianForget k X).map
        ((((Opens.map a.base).sheafAdjunctionContinuous (ModuleCat.{u} k) _ _).homEquiv
          _ _) q) := by
  let b := (Opens.map a.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  let s := (Opens.map a.base).sheafAdjunctionContinuous (ModuleCat.{u} k)
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  change b.homEquiv _ _
    ((b.homEquiv _ _).symm ((scalarAbelianForget k X).map (s.unit.app F)) ≫
      (scalarAbelianForget k Y).map q) = (scalarAbelianForget k X).map (s.homEquiv _ _ q)
  rw [b.homEquiv_naturality_right, Equiv.apply_symm_apply, s.homEquiv_unit,
    Functor.map_comp]
  rfl

/-- Forgetting scalars commutes with inverse image.
Source: Stacks Project, Tag 0096; uniqueness of left adjoints.
(blueprint: new-sc-scalar-forget-pullback-comparison-isIso).

Proof: Scalar forgetting is restriction along integers followed by the equivalence
between integer modules and abelian groups, hence has a coextension right adjoint.
Both coefficient functors preserve sheaves, so the coefficient adjunction restricts
to sheaf categories. Its right adjoint commutes with pushforward, since both are
pointwise. Thus the two composite left adjoints have the same right adjoint.
The uniqueness isomorphism is the comparison constructed above: applying the
composite adjunction to its component gives the composite unit, by naturality
of the coefficient unit and the adjunct formula. This proves invertibility without
any nonemptiness assumption or restriction on characteristic. -/
theorem scalarForgetPullbackComparison_isIso (k : Type u) [Field k]
    {X Y : Scheme.{u}} (a : Y ⟶ X) : IsIso (scalarForgetPullbackComparison k a) := by
  let b := (Opens.map a.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  let s := (Opens.map a.base).sheafAdjunctionContinuous (ModuleCat.{u} k)
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  let x := scalarForgetAdj k X
  let y := scalarForgetAdj k Y
  let j := (x.comp b).ofNatIsoRight (Iso.refl _)
  let e := j.leftAdjointUniq (s.comp y)
  have he (F : KSheaf X k) :
      (scalarForgetPullbackComparison k a).app F = e.hom.app F := by
    apply (j.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    dsimp only [j]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
    simp only [Iso.refl_hom, NatTrans.id_app, Category.comp_id]
    change x.homEquiv _ _ (b.homEquiv _ _
      ((scalarForgetPullbackComparison k a).app F)) = (s.comp y).unit.app F
    have ht := scalarForgetPullbackComparison_adjunct k a F _ (𝟙 _)
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at ht
    rw [s.homEquiv_unit] at ht
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at ht
    erw [ht]
    rw [x.homEquiv_unit, Adjunction.comp_unit_app]
    change x.unit.app F ≫ _ = s.unit.app F ≫ _
    erw [← x.unit.naturality (s.unit.app F)]
    congr 1
  have ht : scalarForgetPullbackComparison k a = e.hom := NatTrans.ext (funext he)
  rw [ht]
  infer_instance

end AlgebraicGeometry.Scheme
