import Langlands.Global.Arithmetic.PrimitiveTraceStabilizerStatement
import Mathlib.RingTheory.Norm.Basic
import Langlands.HarmonicAnalysis.CharacterTransport
import Langlands.HarmonicAnalysis.Conductor
import Langlands.HarmonicAnalysis.PadicFiniteCoefficientSeparationProof
import Langlands.LocalField.RelativeIntegers

/-! Integral witnesses and actual trace-tower identities for the first-order route. -/

noncomputable section

namespace Langlands.Global.AuxiliaryFirstOrder

universe u v w

private theorem valuation_le_exp_neg_ord {p : ℕ} [Fact p.Prime]
    {F : PadicField.{u} p} (T : F.TopologicalData) (x : F.Carrier) :
    T.discreteValuation x ≤ WithZero.exp (-T.ord x) := by
  apply WithZero.le_exp_of_log_le
  simp only [PadicField.TopologicalData.ord, neg_neg, le_refl]

/-- A common-base prime power clears the denominator of an actual local element. -/
theorem exists_prime_pow_mul_mem_integers {p : ℕ} [Fact p.Prime]
    {F : PadicField.{u} p} (T : F.TopologicalData) (x : F.Carrier) :
    ∃ k : ℕ, (p : F.Carrier) ^ k * x ∈ T.Integers := by
  let k : ℕ := (-T.ord x).toNat
  refine ⟨k, (T.mem_integers_iff_discreteValuation_le_one _).mpr ?_⟩
  have he : 1 ≤ T.ord (p : F.Carrier) := T.ord_prime_pos
  have hpow : T.discreteValuation ((p : F.Carrier) ^ k) ≤ WithZero.exp (-(k : ℤ)) := by
    apply (valuation_le_exp_neg_ord T _).trans
    apply WithZero.exp_le_exp.mpr
    have hord : T.ord ((p : F.Carrier) ^ k) = (k : ℤ) * T.ord (p : F.Carrier) := by
      simpa using T.ord_zpow (p : F.Carrier) (k : ℤ)
    rw [hord]
    nlinarith [Int.natCast_nonneg k]
  rw [map_mul]
  calc
    T.discreteValuation ((p : F.Carrier) ^ k) * T.discreteValuation x ≤
        WithZero.exp (-(k : ℤ)) * WithZero.exp (-T.ord x) :=
      mul_le_mul' hpow (valuation_le_exp_neg_ord T x)
    _ = WithZero.exp (-(k : ℤ) - T.ord x) := by rw [← WithZero.exp_add]; rfl
    _ ≤ 1 := by
      rw [← WithZero.exp_zero]
      apply WithZero.exp_le_exp.mpr
      have hk : -T.ord x ≤ (k : ℤ) := Int.self_le_toNat _
      omega

/-- A nonzero actual base-linear functional is detected by an integral element. -/
theorem exists_integral_linear_witness {p : ℕ} [Fact p.Prime]
    {F : PadicField.{u} p} {M : PadicField.{v} p}
    [Algebra F.Carrier M.Carrier] [IsScalarTower (Padic p) F.Carrier M.Carrier]
    (T : M.TopologicalData) (δ : M.Carrier →ₗ[F.Carrier] F.Carrier) (hδ : δ ≠ 0) :
    ∃ y : T.Integers, δ (y : M.Carrier) ≠ 0 := by
  classical
  have hx : ∃ x, δ x ≠ 0 := by
    by_contra! h
    exact hδ (LinearMap.ext h)
  obtain ⟨x, hx⟩ := hx
  obtain ⟨k, hk⟩ := exists_prime_pow_mul_mem_integers T x
  refine ⟨⟨(p : M.Carrier) ^ k * x, hk⟩, ?_⟩
  have hp : (p : F.Carrier) ≠ 0 := by
    let : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hs : (p : M.Carrier) ^ k * x = ((p : F.Carrier) ^ k) • x := by
    simp only [Algebra.smul_def, map_pow, map_natCast]
  change δ ((p : M.Carrier) ^ k * x) ≠ 0
  rw [hs, map_smul, smul_eq_mul]
  exact mul_ne_zero (pow_ne_zero _ hp) hx

/-- The actual difference of the two weighted trace functionals. -/
def traceDifference {F : Type u} {M : Type v} [Field F] [Field M]
    [Algebra F M] [FiniteDimensional F M] (L : IntermediateField F M)
    (b : L) (σ : M ≃ₐ[F] M) : M →ₗ[F] F :=
  ((Algebra.trace F M).comp (LinearMap.mul F M (b : M))).comp σ.toLinearMap -
    (Algebra.trace F M).comp (LinearMap.mul F M (b : M))

@[simp]
theorem traceDifference_apply {F : Type u} {M : Type v} [Field F] [Field M]
    [Algebra F M] [FiniteDimensional F M] (L : IntermediateField F M)
    (b : L) (σ : M ≃ₐ[F] M) (x : M) :
    traceDifference L b σ x = Algebra.trace F M ((b : M) * σ x) -
      Algebra.trace F M ((b : M) * x) := rfl

/-- Exact trace stabilizers give a nonzero difference for each unwanted automorphism. -/
theorem traceDifference_ne_zero {F : Type u} {M : Type v} [Field F] [Field M]
    [Algebra F M] [FiniteDimensional F M] (L : IntermediateField F M)
    (b : L) (hb : HasExactTraceStabilizer L b) (σ : M ≃ₐ[F] M)
    (hσ : σ ∉ L.fixingSubgroup) : traceDifference L b σ ≠ 0 := by
  intro h
  apply hσ
  apply (hb σ).mp
  intro x
  have hx := congrArg (fun δ : M →ₗ[F] F => δ x) h
  exact sub_eq_zero.mp hx

/-- One common prime-power threshold detects a finite family of nonzero base-linear maps. -/
theorem exists_simultaneous_linear_detection {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (M : PadicField.{v} p)
    [Algebra F.Carrier M.Carrier] [IsScalarTower (Padic p) F.Carrier M.Carrier]
    (TF : F.TopologicalData) (TM : M.TopologicalData)
    {I : Type w} [Finite I] (δ : I → M.Carrier →ₗ[F.Carrier] F.Carrier)
    (hδ : ∀ i, δ i ≠ 0) :
    letI := TF.topology
    ∀ ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier,
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ i : I, ∃ y : TM.Integers,
        ψ.complex ((p : F.Carrier) ^ (-(N : ℤ)) * δ i (y : M.Carrier)) ≠ 1 := by
  let := TF.topology
  intro ψ
  classical
  let := Fintype.ofFinite I
  have hex (i : I) : ∃ y : TM.Integers, δ i (y : M.Carrier) ≠ 0 :=
    exists_integral_linear_witness TM (δ i) (hδ i)
  let w (i : I) : TM.Integers := (hex i).choose
  have hw (i : I) : δ i (w i : M.Carrier) ≠ 0 := (hex i).choose_spec
  let d (i : I) : F.Carrier := δ i (w i : M.Carrier)
  let s : Finset F.Carrier := Finset.univ.image d
  obtain ⟨N₀, hN⟩ := HarmonicAnalysis.padicFiniteCoefficientSeparation p F TF ψ s 0
  refine ⟨N₀, fun N hNge i => ?_⟩
  have hd : d i ∈ s := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hnot : ¬ (∀ x ∈ TF.additiveLattice 0,
      ψ.complex ((p : F.Carrier) ^ (-(N : ℤ)) * d i * x) = 1) := by
    intro h
    exact hw i ((hN N hNge (d i) hd).mp h)
  push Not at hnot
  obtain ⟨x, hx, hxψ⟩ := hnot
  let xO : TF.Integers := ⟨x, (TF.mem_additiveLattice_zero x).mp hx⟩
  let y : TM.Integers := TF.relativeIntegerMap TM xO * w i
  refine ⟨y, ?_⟩
  have hδy : δ i (y : M.Carrier) = x * d i := by
    change δ i (algebraMap F.Carrier M.Carrier x * (w i : M.Carrier)) = _
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  rw [hδy]
  convert hxψ using 1
  congr 1
  ring

/-- One inverse-prime-power threshold detects every unwanted trace action on actual integers. -/
theorem exists_simultaneous_trace_detection {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (M : PadicField.{v} p)
    [Algebra F.Carrier M.Carrier] [IsScalarTower (Padic p) F.Carrier M.Carrier]
    [FiniteDimensional F.Carrier M.Carrier] (L : IntermediateField F.Carrier M.Carrier)
    (TF : F.TopologicalData) (TM : M.TopologicalData) (b : L)
    (hb : HasExactTraceStabilizer L b) :
    letI := TF.topology
    ∀ ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier,
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ σ : M.Carrier ≃ₐ[F.Carrier] M.Carrier,
        σ ∉ L.fixingSubgroup → ∃ y : TM.Integers,
          ψ.complex ((p : F.Carrier) ^ (-(N : ℤ)) * traceDifference L b σ (y : M.Carrier)) ≠ 1 := by
  let := TF.topology
  intro ψ
  let B := {σ : M.Carrier ≃ₐ[F.Carrier] M.Carrier // σ ∉ L.fixingSubgroup}
  obtain ⟨N₀, hN⟩ := exists_simultaneous_linear_detection F M TF TM
    (fun σ : B => traceDifference L b σ.val)
    (fun σ => traceDifference_ne_zero L b hb σ.val σ.property) ψ
  exact ⟨N₀, fun N hNge σ hσ => hN N hNge ⟨σ, hσ⟩⟩

/-- The weighted intermediate trace is exactly the total-field trace. -/
theorem weighted_trace_tower {F : Type u} {M : Type v} [Field F] [Field M]
    [Algebra F M] [FiniteDimensional F M] (L : IntermediateField F M)
    (a : F) (b : L) (y : M) :
    Algebra.trace F L (b * (algebraMap F L a * Algebra.trace L M y)) =
      a * Algebra.trace F M ((b : M) * y) := by
  have hmul : b * Algebra.trace L M y =
      Algebra.trace L M ((b : M) * y) := by
    simpa [Algebra.smul_def] using ((Algebra.trace L M).map_smul b y).symm
  rw [show b * (algebraMap F L a * Algebra.trace L M y) =
    a • (b * Algebra.trace L M y) by simp only [Algebra.smul_def]; ring]
  rw [map_smul, hmul, Algebra.trace_trace, smul_eq_mul]

/-- The supplied intermediate subfield is an actual finite p-adic field. -/
abbrev intermediatePadicField {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (M : PadicField.{v} p)
    [Algebra F.Carrier M.Carrier] [IsScalarTower (Padic p) F.Carrier M.Carrier]
    [FiniteDimensional F.Carrier M.Carrier] (L : IntermediateField F.Carrier M.Carrier) :
    PadicField.{v} p := by
  let : FiniteDimensional (Padic p) L := Module.Finite.trans F.Carrier L
  exact { Carrier := L }

/-- Actual field norms are invariant under every automorphism fixing the intermediate field. -/
theorem norm_units_fixed {F : Type u} {M : Type v} [Field F] [Field M]
    [Algebra F M] [FiniteDimensional F M] (L : IntermediateField F M)
    (σ : M ≃ₐ[F] M) (hσ : σ ∈ L.fixingSubgroup) (z : Mˣ) :
    Units.map (Algebra.norm L) (Units.map σ.toRingEquiv.toMonoidHom z) =
      Units.map (Algebra.norm L) z := by
  let e : M ≃ₐ[L] M := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (by
    intro x
    change σ (x : M) = (x : M)
    exact (IntermediateField.mem_fixingSubgroup_iff L σ).mp hσ x x.property)
  apply Units.ext
  change Algebra.norm L (σ (z : M)) = Algebra.norm L (z : M)
  exact Algebra.norm_eq_of_algEquiv e (z : M)

/-- The published trace-character and scalar constructors give the exact total-trace value. -/
theorem weighted_trace_character {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (M : PadicField.{v} p)
    [Algebra F.Carrier M.Carrier] [IsScalarTower (Padic p) F.Carrier M.Carrier]
    [FiniteDimensional F.Carrier M.Carrier] (L : IntermediateField F.Carrier M.Carrier)
    (TF : F.TopologicalData) (TL : (intermediatePadicField F M L).TopologicalData) :
    letI := TF.topology
    letI := TL.topology
    letI := TL.valuativeRel
    letI := TL.localField
    ∀ (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier) (b : Lˣ)
      (a : F.Carrier) (y : M.Carrier),
      ((TF.traceCharacter TL ψ).scale b)
        (algebraMap F.Carrier L a * Algebra.trace L M.Carrier y) =
      ψ (a * Algebra.trace F.Carrier M.Carrier (((b : L) : M.Carrier) * y)) := by
  let := TF.topology
  let := TL.topology
  let := TL.valuativeRel
  let := TL.localField
  intro ψ b a y
  change ψ (Algebra.trace F.Carrier L
    ((b : L) * (algebraMap F.Carrier L a * Algebra.trace L M.Carrier y))) = _
  rw [weighted_trace_tower]

end Langlands.Global.AuxiliaryFirstOrder
