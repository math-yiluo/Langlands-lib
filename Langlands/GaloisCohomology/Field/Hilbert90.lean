import Langlands.GaloisCohomology.Field.AdditiveHilbert90
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Langlands.GaloisCohomology

open Langlands.ProfiniteCohomology
open CategoryTheory CategoryTheory.Limits groupCohomology IntermediateField ClassFieldTheory.Local

universe u



variable {K L : Type u} [Field K] [Field L] [Algebra K L]

section Units

variable (H : Subgroup Gal(L/K))

theorem mem_fixedField_of_mem_invariants_unitsModule {v : Additive Lˣ}
    (hv : v ∈ Representation.invariants ((unitsModule K L).ρ.comp H.subtype)) :
    ((Additive.toMul v : Lˣ) : L) ∈ fixedField H :=
  (mem_fixedField_iff _ _).2 fun σ hσ =>
    congrArg (fun w : Additive Lˣ => ((Additive.toMul w : Lˣ) : L)) (hv ⟨σ, hσ⟩)

noncomputable def invariantsUnitsModuleAddEquiv :
    Representation.invariants ((unitsModule K L).ρ.comp H.subtype) ≃+
      Additive (fixedField H)ˣ where
  toFun v := Additive.ofMul (Units.mk0 ⟨_, mem_fixedField_of_mem_invariants_unitsModule H v.2⟩
    fun h => (Additive.toMul (α := Lˣ) v.1).ne_zero (congrArg Subtype.val h))
  invFun y := ⟨Additive.ofMul (Units.map ((algebraMap (fixedField H) L : _ →+* L) : _ →* L)
      (Additive.toMul y)), fun σ => Additive.toMul.injective (Units.ext
        ((mem_fixedField_iff _ _).1 ((Additive.toMul y : (fixedField H)ˣ) : fixedField H).2
          σ σ.2))⟩
  left_inv _ := Subtype.ext (Additive.toMul.injective (Units.ext rfl))
  right_inv _ := Additive.toMul.injective (Units.ext (Subtype.ext rfl))
  map_add' _ _ := Additive.toMul.injective (Units.ext (Subtype.ext rfl))

@[simp]
theorem coe_invariantsUnitsModuleAddEquiv_apply
    (v : Representation.invariants ((unitsModule K L).ρ.comp H.subtype)) :
    (((Additive.toMul (invariantsUnitsModuleAddEquiv H v) : (fixedField H)ˣ) : fixedField H) : L) =
      ((Additive.toMul (α := Lˣ) v.1 : Lˣ) : L) :=
  rfl

variable [IsGalois K L]

theorem invariantsUnitsModuleAddEquiv_quotientToInvariants (U : OpenNormalSubgroup Gal(L/K))
    (q : Gal(L/K) ⧸ (U : Subgroup Gal(L/K)))
    (v : Representation.invariants ((unitsModule K L).ρ.comp (U : Subgroup Gal(L/K)).subtype)) :
    invariantsUnitsModuleAddEquiv (U : Subgroup Gal(L/K))
        (((unitsModule K L).quotientToInvariants (U : Subgroup Gal(L/K))).ρ q v) =
      (unitsModule K (fixedField (U : Subgroup Gal(L/K)))).ρ (quotientEquivGal U q)
        (invariantsUnitsModuleAddEquiv (U : Subgroup Gal(L/K)) v) := by
  induction q using QuotientGroup.induction_on with
  | H σ =>
    refine Additive.toMul.injective (Units.ext (Subtype.ext ?_))
    exact (quotientEquivGal_mk_apply U σ
      ⟨_, mem_fixedField_of_mem_invariants_unitsModule (U : Subgroup Gal(L/K)) v.2⟩).symm

/-- `invariantsUnitsModuleAddEquiv` as a linear equivalence between the underlying modules of the
two representations (stated with their module structures, so that it can be rewritten with). -/
noncomputable def invariantsUnitsModuleLinearEquiv (U : OpenNormalSubgroup Gal(L/K)) :
    ((unitsModule K L).quotientToInvariants (U : Subgroup Gal(L/K))).V ≃ₗ[IntegerScalars.{u}]
      (unitsModule K (fixedField (U : Subgroup Gal(L/K)))).V :=
  uliftIntLinearEquiv (invariantsUnitsModuleAddEquiv (U : Subgroup Gal(L/K)))

theorem invariantsUnitsModuleLinearEquiv_apply (U : OpenNormalSubgroup Gal(L/K))
    (v : (unitsModule K L).quotientToInvariants (U : Subgroup Gal(L/K))) :
    invariantsUnitsModuleLinearEquiv U v = invariantsUnitsModuleAddEquiv (U : Subgroup Gal(L/K)) v :=
  rfl

noncomputable def groupCohomologyQuotientUnitsModuleIso (U : OpenNormalSubgroup Gal(L/K)) (n : ℕ) :
    groupCohomology ((unitsModule K L).quotientToInvariants (U : Subgroup Gal(L/K))) n ≅
      groupCohomology (unitsModule K (fixedField (U : Subgroup Gal(L/K)))) n :=
  groupCohomology.mapIso (quotientEquivGal U) (invariantsUnitsModuleLinearEquiv U)
    (fun q => LinearMap.ext fun v => invariantsUnitsModuleAddEquiv_quotientToInvariants U q v) n

end Units

section Hilbert90

theorem isZero_groupCohomology_one_unitsModule (K E : Type u) [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] : IsZero (groupCohomology (unitsModule K E) 1) := by
  have hz : ∀ x : groupCohomology (unitsModule K E) 1, x = 0 := fun x =>
    H1_induction_on x fun f => by
      rw [H1π_eq_zero_iff]
      have hf := (mem_cocycles₁_iff (A := unitsModule K E) f).1 f.2
      obtain ⟨β, hβ⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units
        (fun σ => Additive.toMul (α := Eˣ) (f σ)) fun g h =>
          congrArg (Additive.toMul (α := Eˣ)) (hf g h)
      exact ⟨Additive.ofMul β, funext fun σ => congrArg (Additive.ofMul (α := Eˣ)) (hβ σ)⟩
  have : Subsingleton (groupCohomology (unitsModule K E) 1) := ⟨fun a b => by rw [hz a, hz b]⟩
  exact ModuleCat.isZero_of_subsingleton _

variable [IsGalois K L]

theorem isZero_groupCohomology_one_quotientToInvariants_unitsModule
    (U : OpenNormalSubgroup Gal(L/K)) :
    IsZero (groupCohomology ((unitsModule K L).quotientToInvariants (U : Subgroup Gal(L/K))) 1) :=
  (isZero_groupCohomology_one_unitsModule K (fixedField (U : Subgroup Gal(L/K)))).of_iso
    (groupCohomologyQuotientUnitsModuleIso U 1)

theorem isZero_cohomology_one_unitsModule : IsZero (cohomology (unitsModule K L) 1) :=
  isZero_cohomology_of_forall_isZero _ 1 isZero_groupCohomology_one_quotientToInvariants_unitsModule

theorem subsingleton_cohomology_one_unitsModule : Subsingleton (cohomology (unitsModule K L) 1) :=
  ModuleCat.subsingleton_of_isZero isZero_cohomology_one_unitsModule

end Hilbert90

end Langlands.GaloisCohomology
