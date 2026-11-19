import Langlands.Algebra.BrauerComparison.SeparableCohomology
import Langlands.ClassFieldTheory.Local.SpectralUnramifiedInvariant
import Langlands.ClassFieldTheory.Local.FiniteUnramifiedDegree
import Langlands.ClassFieldTheory.Local.SeparableUnramifiedInflation

noncomputable section

open CategoryTheory Langlands.LocalGalois.Separable ValuativeRel

namespace Langlands.ClassFieldTheory.Local

universe u

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- An open normal subgroup with an arithmetic-unramified fixed field. -/
structure SeparableUnramifiedStage where
  subgroup : OpenNormalSubgroup Gal(SeparableClosure F/F)
  unramified : ArithmeticUnramified F (IntermediateField.fixedField subgroup.toSubgroup)

namespace SeparableUnramifiedStage

variable {F}

abbrev field (S : SeparableUnramifiedStage F) : IntermediateField F (SeparableClosure F) :=
  IntermediateField.fixedField S.subgroup.toSubgroup

instance finiteDimensional (S : SeparableUnramifiedStage F) : FiniteDimensional F S.field :=
  fixedField_openNormal_finiteDimensional F (SeparableClosure F) S.subgroup

instance isGalois (S : SeparableUnramifiedStage F) : IsGalois F S.field :=
  IsGalois.of_fixedField_normal_subgroup S.subgroup.toSubgroup

/-- Realize a finite Galois unramified intermediate field as a stage. -/
def ofIntermediate (E : IntermediateField F (SeparableClosure F)) [FiniteDimensional F E]
    [IsGalois F E] (hE : ArithmeticUnramified F E) : SeparableUnramifiedStage F := by
  let H : OpenNormalSubgroup Gal(SeparableClosure F/F) :=
    ⟨⟨E.fixingSubgroup, (InfiniteGalois.isOpen_iff_finite E).mpr inferInstance⟩, inferInstance⟩
  refine ⟨H, ?_⟩
  change ArithmeticUnramified F (IntermediateField.fixedField E.fixingSubgroup)
  rwa [InfiniteGalois.fixedField_fixingSubgroup]

@[simp]
theorem field_ofIntermediate (E : IntermediateField F (SeparableClosure F)) [FiniteDimensional F E]
    [IsGalois F E] (hE : ArithmeticUnramified F E) : (ofIntermediate E hE).field = E :=
  InfiniteGalois.fixedField_fixingSubgroup E

/-- Inflation to absolute continuous cohomology, by actual fixed-field inclusion. -/
def inflation (S : SeparableUnramifiedStage F) : relativeCohomology F S.field 2 →+ Langlands.BrauerComparison.separableH2 F :=
  (fixedFieldUnitInflation F (SeparableClosure F) S.subgroup 2).hom.toAddMonoidHom

theorem inflation_injective (S : SeparableUnramifiedStage F) : Function.Injective S.inflation :=
  (fixedFieldUnitInflation_H2_exactness F (SeparableClosure F) S.subgroup).1

/-- The finite invariant on the fixed field of the stage. -/
def invariant (S : SeparableUnramifiedStage F) : relativeCohomology F S.field 2 →+ RationalModIntegers :=
  spectralUnramifiedInvariant F S.field S.unramified

private theorem inertia_le (S : SeparableUnramifiedStage F) :
    separableInertia F ≤ S.subgroup.toSubgroup := by
  have h := IntermediateField.fixingSubgroup_antitone
    ((finiteUnramifiedMaximality F S.field).mpr S.unramified)
  rw [fixingSubgroup_inertiaFixedField] at h
  change separableInertia F ≤
    (IntermediateField.fixedField (FixedFieldRefinement.closed F (SeparableClosure F) S.subgroup).toSubgroup).fixingSubgroup
    at h
  rwa [InfiniteGalois.fixingSubgroup_fixedField] at h

/-- Taking the intersection of two open normal subgroups gives a common stage. -/
def common (S T : SeparableUnramifiedStage F) : SeparableUnramifiedStage F := by
  let H := S.subgroup ⊓ T.subgroup
  let E := IntermediateField.fixedField H.toSubgroup
  let : FiniteDimensional F E := fixedField_openNormal_finiteDimensional F (SeparableClosure F) H
  have hH : separableInertia F ≤ H.toSubgroup := le_inf S.inertia_le T.inertia_le
  exact ⟨H, (finiteUnramifiedMaximality F E).mp (IntermediateField.fixedField_le hH)⟩

theorem common_le_left (S T : SeparableUnramifiedStage F) : (S.common T).subgroup ≤ S.subgroup :=
  inf_le_left

theorem common_le_right (S T : SeparableUnramifiedStage F) : (S.common T).subgroup ≤ T.subgroup :=
  inf_le_right

variable (S T : SeparableUnramifiedStage F) (h : T.subgroup ≤ S.subgroup)

/-- Relative inflation to a larger unramified fixed field. -/
def refineInflation : relativeCohomology F S.field 2 →+ relativeCohomology F T.field 2 := by
  let := FixedFieldRefinement.inclusionAlgebra h
  let := FixedFieldRefinement.baseTower h
  exact (relativeInflation F S.field T.field 2).hom.toAddMonoidHom

theorem inflation_refineInflation (x : relativeCohomology F S.field 2) :
    T.inflation (S.refineInflation T h x) = S.inflation x := by
  let := FixedFieldRefinement.inclusionAlgebra h
  let := FixedFieldRefinement.baseTower h
  exact congrArg (fun f => f x) (fixedFieldUnitInflation_refinement (K := F)
    (L := SeparableClosure F) h 2)

theorem invariant_refineInflation (x : relativeCohomology F S.field 2) :
    T.invariant (S.refineInflation T h x) = S.invariant x :=
  spectralUnramifiedInvariant_inflation F S.field T.field
    (FixedFieldRefinement.fixedField_le h) S.unramified T.unramified x

end SeparableUnramifiedStage

open SeparableUnramifiedStage

private def IsInvariantValue (x : Langlands.BrauerComparison.separableH2 F) (q : RationalModIntegers) : Prop :=
  ∃ S : SeparableUnramifiedStage F, ∃ a : relativeCohomology F S.field 2,
    S.inflation a = x ∧ S.invariant a = q

private theorem invariantValue_exists (x : Langlands.BrauerComparison.separableH2 F) : ∃ q, IsInvariantValue F x q := by
  obtain ⟨H, hH, a, ha⟩ := exists_unramified_fixedFieldUnitInflation F x
  let S : SeparableUnramifiedStage F := ⟨H, hH⟩
  exact ⟨S.invariant a, S, a, ha, rfl⟩

private theorem invariantValue_unique {x : Langlands.BrauerComparison.separableH2 F} {q r : RationalModIntegers}
    (hq : IsInvariantValue F x q) (hr : IsInvariantValue F x r) : q = r := by
  obtain ⟨S, a, ha, rfl⟩ := hq
  obtain ⟨T, b, hb, rfl⟩ := hr
  let U := S.common T
  let a' := S.refineInflation U (S.common_le_left T) a
  let b' := T.refineInflation U (S.common_le_right T) b
  have ha' : U.inflation a' = x := (S.inflation_refineInflation U _ a).trans ha
  have hb' : U.inflation b' = x := (T.inflation_refineInflation U _ b).trans hb
  have hab : a' = b' := U.inflation_injective (ha'.trans hb'.symm)
  calc
    S.invariant a = U.invariant a' := (S.invariant_refineInflation U _ a).symm
    _ = U.invariant b' := congrArg U.invariant hab
    _ = T.invariant b := T.invariant_refineInflation U _ b

private theorem invariantValue_add {x y : Langlands.BrauerComparison.separableH2 F} {q r : RationalModIntegers}
    (hq : IsInvariantValue F x q) (hr : IsInvariantValue F y r) :
    IsInvariantValue F (x + y) (q + r) := by
  obtain ⟨S, a, ha, rfl⟩ := hq
  obtain ⟨T, b, hb, rfl⟩ := hr
  let U := S.common T
  let a' := S.refineInflation U (S.common_le_left T) a
  let b' := T.refineInflation U (S.common_le_right T) b
  refine ⟨U, a' + b', ?_, ?_⟩
  · rw [map_add]
    exact congrArg₂ (· + ·) ((S.inflation_refineInflation U _ a).trans ha)
      ((T.inflation_refineInflation U _ b).trans hb)
  · rw [map_add]
    exact congrArg₂ (· + ·) (S.invariant_refineInflation U _ a) (T.invariant_refineInflation U _ b)

private def absoluteInvariantHom : Langlands.BrauerComparison.separableH2 F →+ RationalModIntegers where
  toFun x := (invariantValue_exists F x).choose
  map_zero' := by
    obtain ⟨_, S, _, _, _⟩ := invariantValue_exists F 0
    exact invariantValue_unique F (invariantValue_exists F 0).choose_spec
      ⟨S, 0, map_zero S.inflation, map_zero S.invariant⟩
  map_add' x y := invariantValue_unique F (invariantValue_exists F (x + y)).choose_spec
    (invariantValue_add F (invariantValue_exists F x).choose_spec
      (invariantValue_exists F y).choose_spec)

private theorem absoluteInvariantHom_stage (S : SeparableUnramifiedStage F)
    (x : relativeCohomology F S.field 2) :
    absoluteInvariantHom F (S.inflation x) = S.invariant x :=
  invariantValue_unique F (invariantValue_exists F _).choose_spec ⟨S, x, rfl, rfl⟩

private theorem absoluteInvariantHom_injective : Function.Injective (absoluteInvariantHom F) := by
  intro x y hxy
  obtain ⟨q, S, a, ha, hq⟩ := invariantValue_exists F (x - y)
  have hz : S.invariant a = 0 := by
    rw [← absoluteInvariantHom_stage F S a, ha, map_sub, hxy, sub_self]
  have ha0 : a = 0 := spectralUnramifiedInvariant_injective F S.field S.unramified
    (hz.trans (map_zero S.invariant).symm)
  apply sub_eq_zero.mp
  rw [← ha, ha0, map_zero]

private theorem absoluteInvariantHom_surjective : Function.Surjective (absoluteInvariantHom F) := by
  intro q
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℚ)) q
  change rationalClass r = q at hr
  let E := finiteUnramifiedFieldOfDegree F r.den r.pos
  let hE := finiteUnramifiedFieldOfDegree_unramified F r.den r.pos
  let S := SeparableUnramifiedStage.ofIntermediate E hE
  have hdeg : Module.finrank F S.field = r.den :=
    (IntermediateField.equivOfEq (field_ofIntermediate E hE)).toLinearEquiv.finrank_eq.trans
      (finiteUnramifiedFieldOfDegree_finrank F r.den r.pos)
  have hq : q ∈ S.invariant.range := by
    change q ∈ (spectralUnramifiedInvariant F S.field S.unramified).range
    rw [spectralUnramifiedInvariant_range, hdeg]
    have h := (denominatorEquiv r.den r.pos (r.num : ZMod r.den)).property
    simpa only [denominatorEquiv_intCast, Rat.num_div_den, hr] using h
  obtain ⟨a, ha⟩ := hq
  exact ⟨S.inflation a, (absoluteInvariantHom_stage F S a).trans ha⟩

/-- The absolute local invariant for actual separable-closure unit cohomology. -/
def separableLocalInvariant : Langlands.BrauerComparison.separableH2 F ≃+ RationalModIntegers :=
  AddEquiv.ofBijective (absoluteInvariantHom F)
    ⟨absoluteInvariantHom_injective F, absoluteInvariantHom_surjective F⟩

/-- Inflation from an actual unramified stage identifies the absolute and finite values. -/
theorem separableLocalInvariant_inflation (S : SeparableUnramifiedStage F)
    (x : relativeCohomology F S.field 2) :
    separableLocalInvariant F (S.inflation x) = spectralUnramifiedInvariant F S.field S.unramified x :=
  absoluteInvariantHom_stage F S x

end Langlands.ClassFieldTheory.Local
