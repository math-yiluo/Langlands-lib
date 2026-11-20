import Langlands.TraceFormula.GeneralLinearEllipticClassFinitenessStatement
import Langlands.Global.PrincipalAdelesDiscreteProof
import Langlands.LinearAlgebra.MatrixCharpolyConjugacyProof
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.Topology.Algebra.MvPolynomial

/-! # Rational conjugacy classes meeting a compact adelic regular elliptic set -/

namespace Langlands.TraceFormula

open Langlands.Global Langlands.JacquetLanglands

universe u

private noncomputable def charpolyCoefficients {A : Type*} [CommRing A] (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) A) : Fin (n + 1) → A :=
  fun i => g.val.charpoly.coeff i

private theorem continuous_charpolyCoefficients {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (n : ℕ) :
    Continuous (charpolyCoefficients (A := A) n) := by
  refine continuous_pi fun i => ?_
  let p := (Matrix.charpoly.univ A (Fin n)).coeff i
  have heq : (fun g : Matrix.GeneralLinearGroup (Fin n) A => charpolyCoefficients n g i) =
      fun g => MvPolynomial.eval (fun ij : Fin n × Fin n => g.val ij.1 ij.2) p := by
    funext g
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id A)
      (fun ij => g.val ij.1 ij.2) i).symm
  rw [heq]
  exact (MvPolynomial.continuous_eval p).comp
    (continuous_pi fun ij => Units.continuous_val.matrix_elem ij.1 ij.2)

private theorem charpoly_conjugate {A : Type*} [CommRing A] {n : ℕ}
    (x g : Matrix.GeneralLinearGroup (Fin n) A) :
    (x⁻¹ * g * x).val.charpoly = g.val.charpoly := by
  simpa only [Units.val_mul, Matrix.coe_units_inv] using Matrix.charpoly_units_conj' x g.val

private theorem rational_representatives (K : Type u) [Field K] (n : ℕ) (p : Polynomial K) :
    ∃ R : Finset (RationalGL K n), ∀ γ : RationalGL K n, γ.val.charpoly = p →
      ∃ r ∈ R, ∃ y : RationalGL K n, y⁻¹ * γ * y = r := by
  obtain ⟨s, hs⟩ := matrixCharpolyFiniteConjugacy K n p
  have hFinite : ((Units.val : RationalGL K n → Matrix (Fin n) (Fin n) K) ⁻¹'
      (s : Set (Matrix (Fin n) (Fin n) K))).Finite :=
    s.finite_toSet.preimage Units.val_injective.injOn
  refine ⟨hFinite.toFinset, ?_⟩
  intro γ hγ
  obtain ⟨M, hM, y, hy⟩ := hs γ.val hγ
  refine ⟨y * γ * y⁻¹, hFinite.mem_toFinset.mpr ?_, y⁻¹, by rw [inv_inv]⟩
  change y.val * γ.val * (y⁻¹).val ∈ s
  rwa [hy]

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

private theorem finite_polynomials_of_coefficients
    {C : Set (Fin (n + 1) → Adeles K)} (hC : IsCompact C) :
    {p : Polynomial K | p.natDegree ≤ n ∧
      (fun i : Fin (n + 1) => (p.map (algebraMap K (Adeles K))).coeff i) ∈ C}.Finite := by
  let includeCoefficients : (Fin (n + 1) → principalAdeles K) → (Fin (n + 1) → Adeles K) :=
    fun a i => (a i).val
  have hEmbedding : Topology.IsClosedEmbedding includeCoefficients :=
    Topology.IsClosedEmbedding.piMap (fun _ =>
      (principalAdeles_isClosed K).isClosedEmbedding_subtypeVal)
  let : DiscreteTopology (principalAdeles K) := principalAdeles_discreteTopology K
  have hFinite : (includeCoefficients ⁻¹' C).Finite :=
    (hEmbedding.isCompact_preimage hC).finite_of_discrete
  let coefficients (p : Polynomial K) (i : Fin (n + 1)) : principalAdeles K :=
    ⟨algebraMap K (Adeles K) (p.coeff i), ⟨p.coeff i, rfl⟩⟩
  apply Set.Finite.of_finite_image (f := coefficients)
  · refine hFinite.subset ?_
    rintro _ ⟨p, hp, rfl⟩
    change (fun i : Fin (n + 1) => algebraMap K (Adeles K) (p.coeff i)) ∈ C
    simpa only [Polynomial.coeff_map] using hp.2
  · intro p hp q hq heq
    apply Polynomial.ext
    intro i
    by_cases hi : i ≤ n
    · apply NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers K) K
      exact congrArg (fun a => (a ⟨i, Nat.lt_succ_of_le hi⟩).val) heq
    · have hni : n < i := lt_of_not_ge hi
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp.1 hni),
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq.1 hni)]

private theorem isRegularElliptic_of_local_conjugate (v : FinitePlace K)
    (γ : RationalGL K n) (x : AdelicGL K n)
    (h : IsRegularElliptic (FiniteAdelicGL.localProjection K n v
      (AdelicGL.finite K n (x⁻¹ * AdelicGL.rational K n γ * x)))) :
    IsRegularElliptic γ := by
  let localMap := (FiniteAdelicGL.localProjection K n v).toMonoidHom.comp
    (AdelicGL.finite K n).toMonoidHom
  let f := algebraMap K (FiniteCompletion K v)
  have hPoly : (localMap (x⁻¹ * AdelicGL.rational K n γ * x)).val.charpoly =
      γ.val.charpoly.map f := by
    rw [map_mul, map_mul, map_inv, charpoly_conjugate]
    exact Matrix.charpoly_map γ.val f
  change IsRegularElliptic (localMap (x⁻¹ * AdelicGL.rational K n γ * x)) at h
  unfold IsRegularElliptic IsRegularSemisimple at h
  rw [hPoly] at h
  exact ⟨(Polynomial.separable_map f).mp h.1,
    Polynomial.Monic.irreducible_of_irreducible_map f _ γ.val.charpoly_monic h.2⟩

/-- A compact adelic set that is regular elliptic at one finite place meets only
finitely many rational conjugacy classes, all regular elliptic. -/
theorem generalLinearEllipticClassFiniteness :
    GeneralLinearEllipticClassFinitenessStatement.{u} := by
  classical
  intro K _ _ n v Ω hΩ hElliptic
  have hPolynomials := finite_polynomials_of_coefficients K n
    (hΩ.image (continuous_charpolyCoefficients n))
  choose representatives hRepresentatives using rational_representatives K n
  refine ⟨hPolynomials.toFinset.biUnion representatives, ?_⟩
  intro γ
  rintro ⟨x, hx⟩
  have hEllipticγ := isRegularElliptic_of_local_conjugate K n v γ x (hElliptic _ hx)
  have hPolynomial : γ.val.charpoly ∈ hPolynomials.toFinset := by
    apply hPolynomials.mem_toFinset.mpr
    refine ⟨by simp, ⟨_, hx, ?_⟩⟩
    funext i
    change (x⁻¹ * AdelicGL.rational K n γ * x).val.charpoly.coeff i =
      (γ.val.charpoly.map (algebraMap K (Adeles K))).coeff i
    rw [charpoly_conjugate]
    change (γ.val.map (algebraMap K (Adeles K))).charpoly.coeff i = _
    rw [Matrix.charpoly_map]
  obtain ⟨r, hr, y, hy⟩ := hRepresentatives γ.val.charpoly γ rfl
  exact ⟨hEllipticγ, r, Finset.mem_biUnion.mpr ⟨γ.val.charpoly, hPolynomial, hr⟩, y, hy⟩

end Langlands.TraceFormula
