import Langlands.HarmonicAnalysis.UnitConjugation.InvariantDistribution
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.Topology.Algebra.MvPolynomial

/-! # Small dilates of compact conjugacy saturations near the nilpotent cone -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Set Function _root_.Topology

variable {R : Type*} [NormedRing R]

/-- The coefficients below the leading term of the characteristic polynomial of left
multiplication on the underlying vector space. -/
def leftRegularCoefficients (F : Type*) [NontriviallyNormedField F] [NormedAlgebra F R]
    [FiniteDimensional F R] (x : R) : Fin (Module.finrank F R) → F :=
  fun i => (Algebra.lmul F R x).charpoly.coeff i

variable {F : Type*} [NontriviallyNormedField F] [CompleteSpace F]
  [NormedAlgebra F R] [FiniteDimensional F R]

omit [CompleteSpace F] in
@[simp]
theorem leftRegularCoefficients_conjugation (g : Rˣ) (x : R) :
    leftRegularCoefficients F (conjugationHomeomorph g x) = leftRegularCoefficients F x := by
  let e := Units.mulLeftLinearEquiv F R g
  have he : Algebra.lmul F R (conjugationHomeomorph g x) = e.conj (Algebra.lmul F R x) := by
    ext y
    change ((g : R) * x * (g⁻¹ : Rˣ).val) * y = (g : R) * (x * ((g⁻¹ : Rˣ).val * y))
    simp only [mul_assoc]
  funext i
  simp only [leftRegularCoefficients, he, e.charpoly_conj]

omit [CompleteSpace F] in
theorem leftRegularCoefficients_eq_zero_iff (x : R) :
    leftRegularCoefficients F x = 0 ↔ IsNilpotent x := by
  rw [← IsNilpotent.map_iff (Algebra.lmul_injective (R := F)), LinearMap.isNilpotent_iff_charpoly]
  let p := (Algebra.lmul F R x).charpoly
  have hdeg : p.natDegree = Module.finrank F R := LinearMap.charpoly_natDegree _
  have hmon : p.Monic := LinearMap.charpoly_monic _
  change (fun i : Fin (Module.finrank F R) => p.coeff i) = 0 ↔ p = Polynomial.X ^ Module.finrank F R
  constructor
  · intro h
    rw [← hdeg, hmon.eq_X_pow_iff_natDegree_le_natTrailingDegree]
    apply Polynomial.le_natTrailingDegree hmon.ne_zero
    intro i hi
    exact congrFun h ⟨i, hi.trans_eq hdeg⟩
  · intro h
    funext i
    rw [h, Polynomial.coeff_X_pow, ite_eq_right i.isLt.ne]
    rfl

/-- The left regular coefficient map is polynomial in the ambient coordinates. -/
theorem continuous_leftRegularCoefficients : Continuous (leftRegularCoefficients (R := R) F) := by
  classical
  let d := Module.finrank F R
  let b := Module.finBasis F R
  let M (x : R) := LinearMap.toMatrix b b (Algebra.lmul F R x)
  apply continuous_pi
  intro i
  have h : (fun x : R => leftRegularCoefficients F x i) =
      fun x => MvPolynomial.eval (fun jk : Fin d × Fin d => M x jk.1 jk.2)
        (MvPolynomial.map (Int.castRingHom F) ((Matrix.charpoly.univ ℤ (Fin d)).coeff i)) := by
    funext x
    rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, Matrix.charpoly.univ_coeff_eval₂Hom]
    change (Algebra.lmul F R x).charpoly.coeff i = (M x).charpoly.coeff i
    rw [LinearMap.charpoly_toMatrix]
  rw [h]
  apply (MvPolynomial.continuous_eval _).comp
  apply continuous_pi
  intro jk
  let A := (b.coord jk.1).comp ((LinearMap.applyₗ' F (b jk.2) : Module.End F R →ₗ[F] R).comp
    (Algebra.lmul F R).toLinearMap)
  have hA : (fun x : R => M x jk.1 jk.2) = A := by
    funext x
    exact LinearMap.toMatrix_apply b b (Algebra.lmul F R x) jk.1 jk.2
  rw [hA]
  exact A.continuous_of_finiteDimensional

variable {X : Type*} [TopologicalSpace X]

/-- On a compact set in `X`, points of a continuous map that are close to a small
scalar multiple of a conjugate from a fixed compact set must lie in any specified
open neighborhood of the nilpotent preimage. -/
def NilpotentApproximationStatement (p : X → R) (K V : Set X) (ω : Set R) : Prop :=
  Continuous p → IsCompact K → IsOpen V → IsCompact ω →
  (∀ x ∈ K, IsNilpotent (p x) → x ∈ V) →
  ∃ ε : ℝ, 0 < ε ∧ ∀ (c : F) (x : X), x ∈ K → ∀ (g : Rˣ) (a : R), a ∈ ω →
    ‖c‖ < ε → ‖c • conjugationHomeomorph g a - p x‖ < ε → x ∈ V

/-- Separate nonnilpotent points of the compact set from zero in the coefficient
comparison, and make the separation uniform by the tube lemma. -/
theorem nilpotentApproximation (p : X → R) (K V : Set X) (ω : Set R) :
    NilpotentApproximationStatement (F := F) p K V ω := by
  intro hp hK hV hω hnil
  let χ := leftRegularCoefficients (R := R) F
  have hχ : Continuous χ := continuous_leftRegularCoefficients
  have hχ0 : χ 0 = 0 := (leftRegularCoefficients_eq_zero_iff (F := F) 0).2 IsNilpotent.zero
  let Q : Set ((X × R) × (F × R)) :=
    {z | χ (p z.1.1 + z.2.2) ≠ χ (z.2.1 • z.1.2)}
  have hQ : IsOpen Q := (isClosed_eq
    (hχ.comp ((hp.comp continuous_fst.fst).add continuous_snd.snd))
    (hχ.comp (continuous_snd.fst.smul continuous_fst.snd))).isOpen_compl
  have hQ0 : ((K \ V) ×ˢ ω) ×ˢ {(0 : F × R)} ⊆ Q := by
    rintro ⟨⟨x, a⟩, z⟩ ⟨hx, hz⟩
    have hz0 : z = 0 := hz
    subst z
    change χ (p x + 0) ≠ χ ((0 : F) • a)
    rw [add_zero, zero_smul, hχ0]
    intro h
    exact hx.1.2 (hnil x hx.1.1 ((leftRegularCoefficients_eq_zero_iff (F := F) (p x)).mp h))
  obtain ⟨A, B, _, hB, hA, h0B, hAB⟩ :=
    generalized_tube_lemma ((hK.diff hV).prod hω) isCompact_singleton hQ hQ0
  obtain ⟨ε, hε, hεB⟩ := Metric.mem_nhds_iff.mp (hB.mem_nhds (h0B (mem_singleton (0 : F × R))))
  refine ⟨ε, hε, fun c x hx g a ha hc he => ?_⟩
  by_contra hxV
  let e := c • conjugationHomeomorph g a - p x
  have hBe : (c, e) ∈ B := hεB (by
    simpa [Metric.mem_ball, Prod.dist_eq, dist_zero_right, max_lt_iff, e] using ⟨hc, he⟩)
  have hbad := hAB (show ((x, a), (c, e)) ∈ A ×ˢ B from ⟨hA ⟨⟨hx, hxV⟩, ha⟩, hBe⟩)
  change χ (p x + e) ≠ χ (c • a) at hbad
  have hs : p x + e = conjugationHomeomorph g (c • a) := by
    change p x + (c • ((g : R) * a * (g⁻¹ : Rˣ).val) - p x) = (g : R) * (c • a) * (g⁻¹ : Rˣ).val
    rw [add_comm (p x), sub_add_cancel, mul_smul_comm, smul_mul_assoc]
  rw [hs] at hbad
  exact hbad (leftRegularCoefficients_conjugation g (c • a))

end Langlands.HarmonicAnalysis.UnitConjugation
