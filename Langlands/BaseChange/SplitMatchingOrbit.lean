import Langlands.BaseChange.OrbitalIntegral
import Langlands.HarmonicAnalysis.Distribution.TransposeInvariantProof

/-! Closedness and the quotient topology of regular semisimple conjugacy classes. -/

noncomputable section

open Topology
open scoped BigOperators

namespace Langlands.BaseChange

open QuotientIntegration TraceFormula JacquetLanglands
open HarmonicAnalysis.Distribution (charpolyCoeffs charpoly_eq_of_coeff_eq continuous_charpolyCoeffs)

universe u

variable {F : Type u} [Field F] {n : ℕ}

local notation "G" => GeneralLinear n F
local notation "M" => Matrix (Fin n) (Fin n) F

private def powerIntertwiner (A B : M) : ℕ → M
  | 0 => 0
  | k + 1 => A * powerIntertwiner A B k + B ^ k

private theorem powerIntertwiner_mul_sub (A B : M) (k : ℕ) :
    A * powerIntertwiner A B k - powerIntertwiner A B k * B = A ^ k - B ^ k := by
  induction k with
  | zero => simp [powerIntertwiner]
  | succ k ih =>
    let D := powerIntertwiner A B k
    change A * (A * D + B ^ k) - (A * D + B ^ k) * B = A ^ (k + 1) - B ^ (k + 1)
    calc
      _ = A * (A * D - D * B) + A * B ^ k - B ^ (k + 1) := by
        rw [pow_succ B k]
        noncomm_ring
      _ = A ^ (k + 1) - B ^ (k + 1) := by
        rw [show A * D - D * B = A ^ k - B ^ k from ih, mul_sub, sub_add_cancel, pow_succ' A k]

private theorem powerIntertwiner_self (A : M) (k : ℕ) :
    powerIntertwiner A A k = k • A ^ (k - 1) := by
  induction k with
  | zero => simp [powerIntertwiner]
  | succ k ih =>
    cases k with
    | zero => simp [powerIntertwiner]
    | succ k =>
      rw [powerIntertwiner, ih]
      simp only [Nat.add_one_sub_one]
      rw [← Nat.cast_smul_eq_nsmul F (k + 1) (A ^ k), Matrix.mul_smul,
        ← pow_succ' A k, Nat.cast_smul_eq_nsmul]
      exact (succ_nsmul (A ^ (k + 1)) (k + 1)).symm

private def polynomialIntertwiner (p : Polynomial F) (A B : M) : M :=
  p.sum fun k c => c • powerIntertwiner A B k

private theorem polynomialIntertwiner_mul_sub (p : Polynomial F) (A B : M) :
    A * polynomialIntertwiner p A B - polynomialIntertwiner p A B * B =
      Polynomial.aeval A p - Polynomial.aeval B p := by
  simp only [polynomialIntertwiner, Polynomial.aeval_def, Polynomial.eval₂_eq_sum,
    Polynomial.sum_def, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
    Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, powerIntertwiner_mul_sub, ← Algebra.smul_def]

private theorem polynomialIntertwiner_self (p : Polynomial F) (A : M) :
    polynomialIntertwiner p A A = Polynomial.aeval A p.derivative := by
  simp only [polynomialIntertwiner, Polynomial.derivative_apply, Polynomial.sum_def,
    map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, ← Algebra.smul_def,
    powerIntertwiner_self]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.smul_mul, ← Algebra.smul_def, Nat.cast_smul_eq_nsmul]

private theorem polynomialIntertwiner_det_ne_zero (A : M) (hA : A.charpoly.Separable) :
    (polynomialIntertwiner A.charpoly A A).det ≠ 0 := by
  obtain ⟨s, t, h⟩ := Polynomial.separable_def' _ |>.mp hA
  have he := congrArg (Polynomial.aeval A) h
  simp only [map_add, map_mul, map_one, Matrix.aeval_self_charpoly, mul_zero, zero_add] at he
  have hd := congrArg Matrix.det he
  rw [Matrix.det_mul, Matrix.det_one, ← polynomialIntertwiner_self] at hd
  intro hz
  rw [hz, mul_zero] at hd
  exact zero_ne_one hd

section Topology

variable [TopologicalSpace F] [IsTopologicalDivisionRing F]

private theorem continuous_polynomialIntertwiner (p : Polynomial F) (A : M) :
    Continuous (fun B : G => polynomialIntertwiner p A B) := by
  have h (k : ℕ) : Continuous (fun B : G => powerIntertwiner A B k) := by
    induction k with
    | zero => exact continuous_const
    | succ k ih =>
      exact (continuous_const.mul ih).add (Units.continuous_val.pow k)
  refine continuous_finsetSum _ fun k _ => ?_
  change Continuous (fun B : G => p.coeff k • powerIntertwiner A B k)
  exact (h k).const_smul (p.coeff k)

/-- The ordinary conjugate of `γ` as a function of the centralizer coset. -/
def regularOrbitMap (γ : G) : LeftQuotient (glCentralizer γ) → G :=
  twistedOrbitFunction (MonoidHom.id G) γ id

omit [TopologicalSpace F] [IsTopologicalDivisionRing F] in
@[simp] theorem regularOrbitMap_mk (γ x : G) :
    regularOrbitMap γ (leftQuotientMap (glCentralizer γ) x) = x⁻¹ * γ * x := rfl

private theorem regularOrbitMap_continuous (γ : G) : Continuous (regularOrbitMap γ) :=
  (leftQuotient_isOpenQuotientMap (glCentralizer γ)).isQuotientMap.continuous_iff.mpr
    ((continuous_inv.mul continuous_const).mul continuous_id)

omit [TopologicalSpace F] [IsTopologicalDivisionRing F] in
private theorem regularOrbitMap_injective (γ : G) : Function.Injective (regularOrbitMap γ) := by
  intro a b
  induction a, b using Quotient.inductionOn₂ with
  | h x y =>
    intro h
    change x⁻¹ * γ * x = y⁻¹ * γ * y at h
    apply Quotient.sound
    change QuotientGroup.rightRel (glCentralizer γ) x y
    rw [QuotientGroup.rightRel_apply, glCentralizer_eq_centralizer,
      Subgroup.mem_centralizer_singleton_iff]
    calc
      y * x⁻¹ * γ = y * (x⁻¹ * γ * x) * x⁻¹ := by group
      _ = γ * (y * x⁻¹) := by rw [h]; group

omit [TopologicalSpace F] [IsTopologicalDivisionRing F] in
private theorem regularOrbitMap_charpoly (γ : G) (q : LeftQuotient (glCentralizer γ)) :
    (regularOrbitMap γ q : M).charpoly = (γ : M).charpoly := by
  induction q using Quotient.inductionOn with
  | h x =>
    change (((x⁻¹ * γ * x : G) : M)).charpoly = (γ : M).charpoly
    simp only [Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']

variable [T2Space F]

/-- A continuous local choice of conjugators within the characteristic-polynomial fiber. -/
private theorem exists_conjugatorSection (a : G) (ha : IsRegularSemisimple a) :
    ∃ U : Set G, IsOpen U ∧ a ∈ U ∧ ∃ s : U → G, Continuous s ∧
      ∀ b : U, (b.val : M).charpoly = (a : M).charpoly → (s b)⁻¹ * a * s b = b.val := by
  let Q (b : G) := polynomialIntertwiner (a : M).charpoly (a : M) (b : M)
  have hQ : Continuous Q := continuous_polynomialIntertwiner _ _
  let U : Set G := {b | (Q b).det ≠ 0}
  let s (b : U) : G := Matrix.GeneralLinearGroup.mk'' (Q b) (isUnit_iff_ne_zero.mpr b.property)
  refine ⟨U, isOpen_ne.preimage hQ.matrix_det, polynomialIntertwiner_det_ne_zero _ ha,
    s, ?_, ?_⟩
  · apply Units.continuous_iff.mpr
    refine ⟨hQ.comp continuous_subtype_val, ?_⟩
    simp only [Matrix.coe_units_inv]
    refine continuous_iff_continuousAt.mpr fun b => ?_
    change ContinuousAt (fun c : U => (Q c)⁻¹) b
    have hi : ContinuousAt Ring.inverse (Q b).det := by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ b.property
    have hQU : Continuous (fun c : U => Q c) := hQ.comp continuous_subtype_val
    exact (continuousAt_matrix_inv (Q b) hi).comp' (x := b) hQU.continuousAt
  · intro b hb
    have h := polynomialIntertwiner_mul_sub (a : M).charpoly (a : M) (b.val : M)
    have hb0 : Polynomial.aeval (b.val : M) (a : M).charpoly = 0 := by
      rw [← hb, Matrix.aeval_self_charpoly]
    rw [Matrix.aeval_self_charpoly, hb0, sub_self] at h
    have hab : a * s b = s b * b.val := Units.ext (sub_eq_zero.mp h)
    calc
      _ = (s b)⁻¹ * (a * s b) := mul_assoc _ _ _
      _ = b.val := by rw [hab, inv_mul_cancel_left]

private theorem regularOrbitMap_isClosed_range (γ : G) (hγ : IsRegularSemisimple γ) :
    IsClosed (Set.range (regularOrbitMap γ)) := by
  let fiber : Set G := charpolyCoeffs n ⁻¹' {charpolyCoeffs n γ}
  have hclosed : IsClosed fiber := isClosed_singleton.preimage (continuous_charpolyCoeffs n)
  have hrange : Set.range (regularOrbitMap γ) ⊆ fiber := by
    rintro _ ⟨q, rfl⟩
    change charpolyCoeffs n (regularOrbitMap γ q) = charpolyCoeffs n γ
    funext i
    simp only [charpolyCoeffs, regularOrbitMap_charpoly]
  apply isClosed_iff_nhds.mpr
  intro a ha
  have haf : a ∈ fiber := closure_minimal hrange hclosed (mem_closure_iff_nhds.mpr ha)
  have hp : (a : M).charpoly = (γ : M).charpoly :=
    charpoly_eq_of_coeff_eq _ _ (congrFun haf)
  have hreg : IsRegularSemisimple a := by
    unfold IsRegularSemisimple
    rwa [hp]
  obtain ⟨U, hU, haU, s, -, hs⟩ := exists_conjugatorSection a hreg
  obtain ⟨b, hbU, q, hq⟩ := ha U (hU.mem_nhds haU)
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  have hb : (b : M).charpoly = (a : M).charpoly := by
    rw [← hq, regularOrbitMap_charpoly, hp]
  let r := s ⟨b, hbU⟩
  have hab : r⁻¹ * a * r = b := hs ⟨b, hbU⟩ hb
  refine ⟨leftQuotientMap (glCentralizer γ) (x * r⁻¹), ?_⟩
  rw [regularOrbitMap_mk]
  change x⁻¹ * γ * x = b at hq
  calc
    _ = r * (x⁻¹ * γ * x) * r⁻¹ := by group
    _ = a := by rw [hq, ← hab]; group

/-- The quotient orbit map for a separable characteristic polynomial is a closed embedding. -/
theorem regularOrbitMap_isClosedEmbedding (γ : G) (hγ : IsRegularSemisimple γ) :
    IsClosedEmbedding (regularOrbitMap γ) := by
  let R := Set.range (regularOrbitMap γ)
  let e : LeftQuotient (glCentralizer γ) ≃ R :=
    Equiv.ofInjective _ (regularOrbitMap_injective γ)
  have hcont : Continuous e.symm := by
    refine continuous_iff_continuousAt.mpr fun a => ?_
    obtain ⟨q, hq⟩ := a.property
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    have hp : (a.val : M).charpoly = (γ : M).charpoly :=
      hq ▸ regularOrbitMap_charpoly γ (leftQuotientMap (glCentralizer γ) x)
    have hreg : IsRegularSemisimple a.val := by
      unfold IsRegularSemisimple
      rwa [hp]
    obtain ⟨U, hU, haU, s, hcs, hs⟩ := exists_conjugatorSection a.val hreg
    let V : Set R := Subtype.val ⁻¹' U
    have hV : IsOpen V := hU.preimage continuous_subtype_val
    have hc : ContinuousOn e.symm V := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      let z (b : V) : U := ⟨b.val.val, b.property⟩
      have hz : Continuous z := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      have heq : V.domRestrict e.symm = fun b => leftQuotientMap (glCentralizer γ) (x * s (z b)) := by
        funext b
        apply e.injective
        apply Subtype.ext
        rw [Set.domRestrict_apply, Equiv.apply_symm_apply]
        change b.val.val = (x * s (z b))⁻¹ * γ * (x * s (z b))
        have hb : (b.val.val : M).charpoly = (a.val : M).charpoly := by
          obtain ⟨p, hp'⟩ := b.val.property
          rw [← hp', regularOrbitMap_charpoly, hp]
        symm
        calc
          _ = (s (z b))⁻¹ * (x⁻¹ * γ * x) * s (z b) := by group
          _ = b.val.val := by rw [show x⁻¹ * γ * x = a.val from hq]; exact hs (z b) hb
      rw [heq]
      exact (leftQuotient_isOpenQuotientMap (glCentralizer γ)).continuous.comp
        (continuous_const.mul (hcs.comp hz))
    exact (hc a haU).continuousAt (hV.mem_nhds haU)
  let E : LeftQuotient (glCentralizer γ) ≃ₜ R :=
    ⟨e, (regularOrbitMap_continuous γ).subtype_mk _, hcont⟩
  exact ⟨IsEmbedding.subtypeVal.comp E.isEmbedding, regularOrbitMap_isClosed_range γ hγ⟩

end Topology

end Langlands.BaseChange
