import Langlands.Galois.Local.SeparableUnramifiedArithmeticProof
import Langlands.Galois.Local.SeparableUnramifiedGaloisProof
import Langlands.Galois.Local.AbsoluteProof
import Langlands.GroupScheme.Descent.FiniteUnramifiedAutomorphismLift

noncomputable section

open IsLocalRing ValuativeRel
open scoped NNReal Topology

namespace Langlands.LocalGalois.Separable

universe u

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

local instance : NontriviallyNormedField F := localNormedField F
local instance : IsUltrametricDist F := localNormedField_ultrametric F
local instance : CompleteSpace F := localNormedField_complete F
local instance : Finite (ResidueField (baseIntegers F)) := localResidue_finite F

/-- The actual inertia fixed field has faithful residue action. -/
theorem fixedField_residueHom_injective :
    Function.Injective (residueHom F (inertiaFixedField F)) := by
  apply (injective_iff_map_eq_one (residueHom F (inertiaFixedField F))).mpr
  intro σ hσ
  let τ := σ.liftNormal (SeparableClosure F)
  have hτ : τ.restrictNormal (inertiaFixedField F) = σ :=
    σ.restrict_liftNormal (SeparableClosure F)
  have hI : τ ∈ separableInertia F := by
    apply mem_separableInertia_of_forall_teichSet F τ
    intro x hx
    obtain ⟨M, hM, hx⟩ := hx
    let ζ : extensionIntegers F (SeparableClosure F) :=
      ⟨x, mem_integers_of_pow_eq_one F (teichOrder_ne_zero F hM) hx⟩
    have hζ : ζ ^ (Nat.card (ResidueField (baseIntegers F)) ^ M - 1) = 1 :=
      Subtype.ext hx
    have hxK : x ∈ inertiaFixedField F :=
      mem_inertiaFixedField_of_pow_eq_one F hM ζ hζ
    let z : fixedFieldIntegers F := ⟨⟨x, hxK⟩, ζ.property⟩
    let z' := fixedFieldIntegersEquiv F z
    have hz' : integerInclusion F (SeparableClosure F) (inertiaFixedField F) z' = ζ := rfl
    have hres := residueHom_restrict F (SeparableClosure F) (inertiaFixedField F) τ
      (residue _ z')
    rw [hτ, hσ, AlgEquiv.one_apply, residueInclusion_residue, hz',
      residueHom_apply] at hres
    have hpow : (integerAut F (SeparableClosure F) τ ζ) ^
        (Nat.card (ResidueField (baseIntegers F)) ^ M - 1) = 1 := by
      rw [← map_pow, hζ, map_one]
    have heq := eq_of_pow_eq_one_of_sub_mem (teichOrder_isUnit F hM) hpow hζ
      (by rw [← residue_eq_zero_iff, map_sub, hres, sub_self])
    exact congrArg Subtype.val heq
  apply AlgEquiv.ext
  intro x
  apply Subtype.val_injective
  exact (σ.liftNormal_commutes (SeparableClosure F) x).symm.trans
    ((mem_inertiaFixedField_iff F (x : SeparableClosure F)).mp x.property τ hI)

/-- The residue comparison for the actual inertia fixed field is a topological
group isomorphism. -/
def fixedFieldResidueGaloisEquiv :
    Gal(inertiaFixedField F/F) ≃ₜ*
      Gal(ResidueField (extensionIntegers F (inertiaFixedField F))/
        ResidueField (baseIntegers F)) := by
  let e := MulEquiv.ofBijective (residueHom F (inertiaFixedField F))
    ⟨fixedField_residueHom_injective F, residueHom_surjective F (inertiaFixedField F)⟩
  have he : Continuous e := residueHom_continuous F (inertiaFixedField F)
  exact
    { toMulEquiv := e
      continuous_toFun := he
      continuous_invFun := he.continuous_symm_of_equiv_compact_to_t2 }

section FiniteField

variable (k L : Type*) [Field k] [Fintype k] [Field L] [Algebra k L]
    [Algebra.IsAlgebraic k L]

/-- Arithmetic Frobenius generates a dense subgroup in every algebraic
extension of a finite field. -/
theorem arithmeticFrobenius_denseRange :
    DenseRange (fun n : ℤ => (FiniteField.frobeniusAlgEquivOfAlgebraic k L) ^ n) := by
  let : IsGalois k L := isGalois_of_finite_base k L
  intro σ
  apply mem_closure_iff_nhds_one.mpr
  intro U hU
  obtain ⟨E, hE⟩ :=
    (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois U).mp hU
  let : Finite E := Module.finite_of_finite k
  obtain ⟨i, hi⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k E).surjective
      (AlgEquiv.restrictNormalHom E σ)
  change FiniteField.frobeniusAlgEquivOfAlgebraic k E ^ i.val =
    AlgEquiv.restrictNormalHom E σ at hi
  let fr := FiniteField.frobeniusAlgEquivOfAlgebraic k L
  have hfr : AlgEquiv.restrictNormalHom E fr =
      FiniteField.frobeniusAlgEquivOfAlgebraic k E := by
    ext x
    simp only [AlgEquiv.restrictNormalHom_apply, fr,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic, IntermediateField.coe_pow]
  refine ⟨fr ^ (i.val : ℤ), ⟨(i.val : ℤ), rfl⟩, hE ?_⟩
  apply (FiniteGaloisIntermediateField.mem_fixingSubgroup_iff _ E).mpr
  rw [map_div, map_zpow, hfr, zpow_natCast, hi, div_self']

end FiniteField

/-- Choose an arithmetic Frobenius lift on the actual inertia fixed field.
Its powers meet every finite-subextension fixing-subgroup coset, and its
action on the actual integer residue field is the cardinality power map. -/
theorem exists_fixedField_arithmeticFrobenius :
    ∃ φ : Gal(inertiaFixedField F/F),
      (∀ E : IntermediateField F (inertiaFixedField F), FiniteDimensional F E →
        ∀ σ : Gal(inertiaFixedField F/F),
          ∃ n : ℤ, σ⁻¹ * φ ^ n ∈ E.fixingSubgroup) ∧
      (∀ x : fixedFieldIntegers F,
        residue _ (Langlands.GroupScheme.Descent.FiniteUnramified.fixedFieldIntegerAut
          F φ x) = residue _ x ^ Nat.card 𝓀[F]) := by
  let k := ResidueField (baseIntegers F)
  let L := ResidueField (extensionIntegers F (inertiaFixedField F))
  let : Fintype k := Fintype.ofFinite _
  let : Algebra.IsIntegral k L := residueExtension_isIntegral F (inertiaFixedField F)
  let : Algebra.IsAlgebraic k L :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral (R := k) x).isAlgebraic⟩
  let e := fixedFieldResidueGaloisEquiv F
  let fr := FiniteField.frobeniusAlgEquivOfAlgebraic k L
  let φ := e.symm fr
  have hφ : residueHom F (inertiaFixedField F) φ = fr := e.apply_symm_apply fr
  have hd : DenseRange (fun n : ℤ => φ ^ n) := by
    have h := e.symm.surjective.denseRange.comp (arithmeticFrobenius_denseRange k L)
      e.symm.continuous
    simpa only [Function.comp_def, map_zpow] using h
  refine ⟨φ, ?_, ?_⟩
  · intro E hE σ
    let := hE
    let U : Set Gal(inertiaFixedField F/F) :=
      {τ | σ⁻¹ * τ ∈ E.fixingSubgroup}
    have hopen : IsOpen U :=
      E.fixingSubgroup_isOpen.preimage (continuous_const.mul continuous_id)
    exact hd.exists_mem_open hopen ⟨σ, by simp [U]⟩
  · intro x
    let z := fixedFieldIntegersEquiv F x
    have h := congrArg (fun τ => τ (residue _ z)) hφ
    rw [residueHom_apply] at h
    have hcard : Nat.card k = Nat.card 𝓀[F] :=
      Nat.card_congr (localResidueEquiv F).toEquiv
    change residue _ (integerAut F (inertiaFixedField F) φ z) =
      residue _ z ^ Fintype.card k at h
    rw [Fintype.card_eq_nat_card, hcard] at h
    apply (ResidueField.mapEquiv (fixedFieldIntegersEquiv F)).injective
    rw [map_pow, ResidueField.mapEquiv_apply, ResidueField.map_residue,
      ResidueField.mapEquiv_apply, ResidueField.map_residue]
    exact h

end Langlands.LocalGalois.Separable
