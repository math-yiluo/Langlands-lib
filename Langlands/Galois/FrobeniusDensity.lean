import Langlands.Galois.ClosureRestriction
import Langlands.Galois.FrobeniusLift
import Langlands.Global.Arithmetic.ChebotarevDegreeOne
import Mathlib.NumberTheory.RamificationInertia.Galois

/-! # Density of actual geometric Frobenius conjugates -/

noncomputable section

open NumberField IsLocalRing
open scoped NumberField Pointwise Topology Valued nonZeroDivisors

universe u

namespace Langlands.GaloisRepresentation

variable {K : Type u} [Field K] [NumberField K]

/-- The chosen geometric Frobenius lift mapped to the actual global Galois group. -/
def globalGeometricFrobenius (v : Global.FinitePlace K) : Field.absoluteGaloisGroup K :=
  Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) (geometricFrobeniusLift v)

section LocalComparison

variable (v : Global.FinitePlace K) (E : IntermediateField K (AlgebraicClosure K))

local notation "Kv" => Global.FiniteCompletion K v
local notation "Cv" => AlgebraicClosure Kv
local notation "Ov" => LocalGalois.baseIntegers Kv
local notation "Ic" => LocalGalois.extensionIntegers Kv Cv

private def finiteClosureEmbedding : E →+* Cv := by
  let : Algebra K Kv := (NumberField.FinitePlace.embedding v).toAlgebra
  let i : AlgebraicClosure K →ₐ[K] Cv :=
    chosenClosureEmbedding (NumberField.FinitePlace.embedding v)
  exact i.toRingHom.comp E.val.toRingHom

private def finiteIntegersMap : (𝓞 E) →+* Ic :=
  ((finiteClosureEmbedding v E).comp (algebraMap (𝓞 E) E)).codRestrict
    (Ic).toSubring fun x => by
      apply (LocalGalois.integral_iff_mem_spectralIntegers Kv Cv _).mp
      exact IsIntegral.map_of_comp_eq (algebraMap ℤ Ov) (finiteClosureEmbedding v E)
        (RingHom.ext_int _ _) x.property

private theorem finiteIntegersMap_base (x : 𝓞 K) :
    finiteIntegersMap v E (algebraMap (𝓞 K) (𝓞 E) x) =
      algebraMap Ov Ic (Global.CompletionResidue.integersMap K v x) := by
  let : Algebra K Kv := (NumberField.FinitePlace.embedding v).toAlgebra
  let i : AlgebraicClosure K →ₐ[K] Cv :=
    chosenClosureEmbedding (NumberField.FinitePlace.embedding v)
  apply Subtype.ext
  change i (algebraMap E (AlgebraicClosure K) (algebraMap K E (x : K))) =
    algebraMap Kv Cv (algebraMap (𝓞 K) Kv x)
  rw [← IsScalarTower.algebraMap_apply K E (AlgebraicClosure K), i.commutes,
    IsScalarTower.algebraMap_apply K Kv Cv]
  rfl

private def finiteResidueMap : (𝓞 E) →+* LocalResidueClosure v :=
  (residue Ic).comp (finiteIntegersMap v E)

private def inducedPrime : Ideal (𝓞 E) := RingHom.ker (finiteResidueMap v E)

private theorem inducedPrime_isPrime : (inducedPrime v E).IsPrime :=
  RingHom.ker_isPrime (finiteResidueMap v E)

private theorem inducedPrime_liesOver : (inducedPrime v E).LiesOver v.asIdeal := by
  constructor
  ext x
  rw [Ideal.under_def, Ideal.mem_comap]
  change x ∈ v.asIdeal ↔ finiteResidueMap v E (algebraMap (𝓞 K) (𝓞 E) x) = 0
  rw [finiteResidueMap, RingHom.comp_apply, finiteIntegersMap_base,
    ← Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap]
  rw [map_eq_zero_iff _ (algebraMap (ResidueField Ov) (LocalResidueClosure v)).injective]
  exact (Global.CompletionResidue.residueMap_eq_zero_iff K v x).symm

private theorem finiteClosureEmbedding_restrict [Normal K E] (g : LocalGroup v) (x : E) :
    finiteClosureEmbedding v E (AlgEquiv.restrictNormalHom E
      (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) g) x) =
      AlgEquiv.toRingEquiv g (finiteClosureEmbedding v E x) := by
  let : Algebra K Kv := (NumberField.FinitePlace.embedding v).toAlgebra
  let i : AlgebraicClosure K →ₐ[K] Cv :=
    chosenClosureEmbedding (NumberField.FinitePlace.embedding v)
  let s : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
    Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) g
  change i (↑(AlgEquiv.restrictNormalHom E s x) : AlgebraicClosure K) =
    AlgEquiv.toRingEquiv g (i x)
  exact (congrArg i (AlgEquiv.restrictNormalHom_apply E s x)).trans
    (restrictionAlongClosure_commutes i g (x : AlgebraicClosure K))

private theorem arithmeticFrobeniusAt_inducedPrime [Normal K E] :
    (RingOfIntegers.mapAlgHom (AlgEquiv.restrictNormalHom E
      ((globalGeometricFrobenius v)⁻¹))).IsArithFrobAt (inducedPrime v E) := by
  let g : Cv ≃ₐ[Kv] Cv := geometricFrobeniusLift v
  let σ := AlgEquiv.restrictNormalHom E ((globalGeometricFrobenius v)⁻¹)
  let := inducedPrime_liesOver v E
  intro x
  have hc : Nat.card (𝓞 K ⧸ (inducedPrime v E).under (𝓞 K)) = residueCardinality v := by
    rw [← (inducedPrime v E).over_def v.asIdeal, residueCardinality,
      Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have haction : finiteIntegersMap v E (RingOfIntegers.mapAlgHom σ x) =
      LocalGalois.integerAut Kv Cv (g⁻¹)
        (finiteIntegersMap v E x) := by
    apply Subtype.ext
    change finiteClosureEmbedding v E (σ (x : E)) =
      AlgEquiv.toRingEquiv g⁻¹ (finiteClosureEmbedding v E (x : E))
    have hσ : σ = AlgEquiv.restrictNormalHom E
        (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding v) (g⁻¹)) :=
      congrArg (AlgEquiv.restrictNormalHom E) (map_inv _ g).symm
    rw [hσ]
    exact finiteClosureEmbedding_restrict v E (g⁻¹) (x : E)
  change finiteResidueMap v E (RingOfIntegers.mapAlgHom σ x -
    x ^ Nat.card (𝓞 K ⧸ (inducedPrime v E).under (𝓞 K))) = 0
  rw [hc, map_sub, map_pow, sub_eq_zero]
  change residue Ic (finiteIntegersMap v E (RingOfIntegers.mapAlgHom σ x)) =
    residue Ic (finiteIntegersMap v E x) ^ residueCardinality v
  rw [haction, ← LocalGalois.residueHom_apply]
  exact geometricFrobeniusLift_spec v _

end LocalComparison

private theorem exists_frobenius_conjugate_restrict
    (E : IntermediateField K (AlgebraicClosure K)) [NumberField E] [IsGalois K E]
    (g : Field.absoluteGaloisGroup K) (S : Finset (Global.FinitePlace K)) :
    ∃ v : Global.FinitePlace K, v ∉ S ∧ (residueCardinality v).Prime ∧
      ∃ t : Field.absoluteGaloisGroup K,
        AlgEquiv.restrictNormalHom E (t * globalGeometricFrobenius v * t⁻¹) =
          AlgEquiv.restrictNormalHom E g := by
  let r : Field.absoluteGaloisGroup K →* (E ≃ₐ[K] E) := AlgEquiv.restrictNormalHom E
  obtain ⟨v, hv, hcard, q, hqv, hqu, hqf⟩ :=
    Global.chebotarevDegreeOne K E ((r g)⁻¹) S
  let := hqv
  let := hqu
  let := inducedPrime_isPrime v E
  let := inducedPrime_liesOver v E
  obtain ⟨a, ha⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal
    (inducedPrime v E) q.asIdeal (E ≃ₐ[K] E)
  have hfrob : IsArithFrobAt (𝓞 K) (r ((globalGeometricFrobenius v)⁻¹)) (inducedPrime v E) :=
    arithmeticFrobeniusAt_inducedPrime v E
  have hconj := hfrob.conj a
  rw [ha] at hconj
  have hmaps : RingOfIntegers.mapAlgHom (a * r ((globalGeometricFrobenius v)⁻¹) * a⁻¹) =
      RingOfIntegers.mapAlgHom ((r g)⁻¹) :=
    AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt hconj hqf
      (fun _ hx => mem_nonZeroDivisors_iff_ne_zero.mpr (fun h => hx (h ▸ q.asIdeal.zero_mem)))
  have heq : a * r ((globalGeometricFrobenius v)⁻¹) * a⁻¹ = (r g)⁻¹ := by
    have hring : (a * r ((globalGeometricFrobenius v)⁻¹) * a⁻¹).toRingEquiv.toRingHom =
        ((r g)⁻¹).toRingEquiv.toRingHom :=
      IsFractionRing.ringHom_ext (A := 𝓞 E) fun x =>
        congrArg (fun y : 𝓞 E => (y : E)) (DFunLike.congr_fun hmaps x)
    exact AlgEquiv.ext (RingHom.congr_fun hring)
  have hr : Function.Surjective r :=
    AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥E) (AlgebraicClosure K)
  obtain ⟨t, ht⟩ := hr a
  refine ⟨v, hv, hcard, t, ?_⟩
  change r (t * globalGeometricFrobenius v * t⁻¹) = r g
  rw [map_mul, map_mul, map_inv, ht]
  simpa only [map_inv, mul_inv_rev, inv_inv, mul_assoc] using congrArg Inv.inv heq

/-- Conjugates of the chosen geometric Frobenius lifts at degree-one places
outside any finite set are dense in the actual absolute Galois group. -/
theorem dense_conjugates_globalGeometricFrobenius_degreeOne
    (S : Finset (Global.FinitePlace K)) :
    Dense {g : Field.absoluteGaloisGroup K | ∃ v : Global.FinitePlace K,
      v ∉ S ∧ (residueCardinality v).Prime ∧
        ∃ t : Field.absoluteGaloisGroup K, t * globalGeometricFrobenius v * t⁻¹ = g} := by
  refine dense_iff_inter_open.mpr fun U hU ⟨g, hg⟩ => ?_
  have hn : (fun x : Field.absoluteGaloisGroup K => g * x) ⁻¹' U ∈ 𝓝 1 :=
    (hU.preimage (continuous_const_mul g)).mem_nhds (by simpa using hg)
  obtain ⟨E, hEfin, hEnormal, hEU⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal K (AlgebraicClosure K) _).mp hn
  let := hEfin
  let := hEnormal
  let : NumberField E := NumberField.of_module_finite K E
  let : IsGalois K E := ⟨⟩
  obtain ⟨v, hv, hprime, t, ht⟩ := exists_frobenius_conjugate_restrict E g S
  let x := t * globalGeometricFrobenius v * t⁻¹
  let r : Field.absoluteGaloisGroup K →* (E ≃ₐ[K] E) := AlgEquiv.restrictNormalHom E
  have hfix : g⁻¹ * x ∈ E.fixingSubgroup := by
    apply (IntermediateField.mem_fixingSubgroup_iff E _).mpr
    exact (AlgEquiv.restrictNormal_eq_one_iff E (g⁻¹ * x)).mp (show r (g⁻¹ * x) = 1 by
      rw [map_mul, map_inv, show r x = r g from ht, inv_mul_cancel])
  have hx : x ∈ U := by
    have hx := hEU hfix
    change g * (g⁻¹ * x) ∈ U at hx
    simpa only [mul_inv_cancel_left] using hx
  exact ⟨x, hx, v, hv, hprime, t, rfl⟩

end Langlands.GaloisRepresentation
