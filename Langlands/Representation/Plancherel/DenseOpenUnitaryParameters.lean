import Langlands.Representation.Plancherel.RationalUnitaryOperatorCancellation

/-! # Dense open regions in ambient and unitary parameters -/

noncomputable section

set_option hygiene false
set_option quotPrecheck false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.UnramifiedOperatorFamily

universe u uI

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (H : GroupScheme (Spec (CommRingCat.of F))) [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

local instance denseOpenParameterTopology : TopologicalSpace (rationalPoints H) := rationalPointTopology F H.X
local notation "ν" => fun a => (rationalNormCharacters H a).toMul
local notation "X" => unramifiedCharacters ν
local notation "R" => unramifiedRegularFunctions ν
local notation "u" => unitaryToUnramified H

/-- An ambient open set that is dense both in the parameter group and after
restriction to the unitary subgroup. -/
structure IsDenseOpenUnitaryRegion (U : Set X) : Prop where
  isOpen : IsOpen U
  dense : Dense U
  unitary_dense : Dense ((u) ⁻¹' U)

omit [LocallyOfFiniteType H.X.hom] in
/-- Two such regions have a common region of the same kind. -/
theorem IsDenseOpenUnitaryRegion.inter {U V : Set X}
    (hU : IsDenseOpenUnitaryRegion H U) (hV : IsDenseOpenUnitaryRegion H V) :
    IsDenseOpenUnitaryRegion H (U ∩ V) := by
  have hc : Continuous u := continuous_subtype_val.subtype_mk (fun z => z.property.1)
  exact ⟨hU.isOpen.inter hV.isOpen, hU.dense.inter_of_isOpen_right hV.dense hV.isOpen,
    hU.unitary_dense.inter_of_isOpen_right hV.unitary_dense (hV.isOpen.preimage hc)⟩

omit [LocallyOfFiniteType H.X.hom] in
/-- Finite families of the regions admit a dense open intersection in both groups. -/
theorem isDenseOpenUnitaryRegion_biInter {I : Type uI} (s : Finset I) (V : I → Set X)
    (h : ∀ i ∈ s, IsDenseOpenUnitaryRegion H (V i)) :
    IsDenseOpenUnitaryRegion H (⋂ i ∈ s, V i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (show IsDenseOpenUnitaryRegion H Set.univ from ⟨isOpen_univ, dense_univ,
      by simpa only [Set.preimage_univ] using dense_univ⟩)
  | insert i s hi ih =>
    rw [Finset.set_biInter_insert]
    exact (h i (Finset.mem_insert_self _ _)).inter H (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- A nonzero regular function cuts out such a region. -/
theorem isDenseOpenUnitaryRegion_nonzero (hH : IsConnectedReductive H) (b : R) (hb : b ≠ 0) :
    IsDenseOpenUnitaryRegion H {z | b.val z ≠ 0} :=
  ⟨isOpen_ne_fun (continuous_unramifiedRegularFunction ν b) continuous_const,
    rationalUnramifiedRegular_dense_nonzero H (continuous_rationalValuationImageProjection H) hH b hb,
    ActualCommonLeviV3.dense_rationalUnitaryRegularRestriction_ne_zero H hH b hb⟩

end Langlands.Plancherel.UnramifiedOperatorFamily
