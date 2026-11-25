/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarUnitCohomologyCoordinates
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.ScalarCupCoefficientNaturality
import WeilConjectures.AlgebraicGeometry.ScalarCupUnitIdentities
import WeilConjectures.AlgebraicGeometry.ScalarUnitClassPullback

/-! # External cup with one after identifying the unit coefficients

Source: Stacks Project, Varieties, Tag 0BED; Cohomology, cup products.
(blueprint: lem-sc-external-cup-unit-coefficient-identities).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

noncomputable local instance (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} X.ringCatSheaf) :=
  SheafOfModules.monoidalCategory X.sheaf

/-- Identifying the two pulled-back unit coefficients and applying the tensor unitor
turns external cup with the degree-zero class of one into scalar projection pullback.
Source: Stacks Project, Tag 0BED, maps preceding varieties-equation-kunneth-on-cech;
Cohomology, section-cup-product; Tag 01F7, functoriality.
(blueprint: lem-sc-external-cup-unit-coefficient-identities).

Proof: Compute scalar cohomology on a common acyclic resolution and represent the
canonical degree-zero unit class by the augmentation of the section one. The scalar
Ext comparison sends it to the degree-zero scalar-unit morphism, by evaluation at one
in the constant-sheaf adjunction. Projection inverse image followed by the coefficient
map preserves this class: its adjunction formula is the tensor-pullback unit formula,
and the structure-sheaf ring map sends one to one. The tensor pairing on a computing
resolution extends the sectionwise tensor map. Composing with the two adjoint unit
maps and the tensor unitor sends s tensor one and one tensor s to s. Consequently
pairing a cycle with the unit cocycle gives its pulled-back cycle. The same formula
holds on boundaries, so it descends to cohomology. The derived Ext tensor construction
of scalarCohomologyCup computes this pairing, independently of the resolution lifts;
apply the acyclic-resolution characterization of cup products. In degrees (1,0) and
(0,1) there is no interchange sign. These give the two displayed identities, before
any module-to-abelian comparison and without any Kunneth or spanning assertion. -/
theorem external_cup_unit_coefficient_identities (k : Type u) [Field k]
    (X Y : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) :
    let F := SheafOfModules.unit X.ringCatSheaf
    let G := SheafOfModules.unit Y.ringCatSheaf
    let p := pullback.fst f g ≫ f
    let m := (tensorPullbackObjUnitToUnit (pullback.fst f g) ⊗ₘ
      tensorPullbackObjUnitToUnit (pullback.snd f g)) ≫
        (λ_ (SheafOfModules.unit (CategoryTheory.Limits.pullback f g).ringCatSheaf)).hom
    (∀ a : scalarCohomology f F 1,
      scalarCohomologyMap p m 1
          (externalCup f g F G 1 0 a (scalarUnitCohomologyClass g)) =
        scalarCohomologyMap p (tensorPullbackObjUnitToUnit (pullback.fst f g)) 1
          (scalarCohomologyPullback f p (pullback.fst f g) rfl F 1 a)) ∧
    (∀ b : scalarCohomology g G 1,
      scalarCohomologyMap p m 1
          (externalCup f g F G 0 1 (scalarUnitCohomologyClass f) b) =
        scalarCohomologyMap p (tensorPullbackObjUnitToUnit (pullback.snd f g)) 1
          (scalarCohomologyPullback g p (pullback.snd f g) pullback.condition.symm G 1 b)) := by
  dsimp only
  let P := CategoryTheory.Limits.pullback f g
  let p := pullback.fst f g ≫ f
  let U := SheafOfModules.unit P.ringCatSheaf
  let ex := tensorPullbackObjUnitToUnit (pullback.fst f g)
  let ey := tensorPullbackObjUnitToUnit (pullback.snd f g)
  have map_comp {M N Q : P.Modules} (v : M ⟶ N) (w : N ⟶ Q)
      (n : ℕ) (x : scalarCohomology p M n) :
      scalarCohomologyMap p (v ≫ w) n x =
        scalarCohomologyMap p w n (scalarCohomologyMap p v n x) := by
    simp only [scalarCohomologyMap, Functor.map_comp, ModuleCat.hom_comp,
      LinearMap.comp_apply]
  obtain ⟨huR, huL⟩ := scalar_cup_unit_identities k P p
  constructor
  · intro a
    unfold externalCup
    rw [map_comp]
    erw [scalarCup_coefficient_naturality k P p _ _ U U ex ey 1 0]
    rw [scalar_unit_class_pullback k Y P g p (pullback.snd f g) pullback.condition.symm]
    exact huR _
  · intro b
    unfold externalCup
    rw [map_comp]
    erw [scalarCup_coefficient_naturality k P p _ _ U U ex ey 0 1]
    rw [scalar_unit_class_pullback k X P f p (pullback.fst f g) rfl]
    exact huL _

end AlgebraicGeometry.Scheme.Modules
