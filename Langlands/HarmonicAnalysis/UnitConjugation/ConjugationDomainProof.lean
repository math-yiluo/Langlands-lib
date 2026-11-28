import Langlands.HarmonicAnalysis.UnitConjugation.ConjugationDomainStatement
import Langlands.LinearAlgebra.DivisionMatrixIntegerConjugation
import Langlands.Algebra.DivisionAlgebraNorm
import Langlands.Galois.Local.AbsoluteDefinitions
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Harish-Chandra's Lemma 4.3 for the Lie algebra of `Aˣ`

This module proves `LieAlgebraConjugationDomainStatement` (`lieAlgebraConjugationDomain`): for a
finite-dimensional semisimple algebra `A` over a nonarchimedean local field `F` of characteristic
zero and a compact set `ω ⊆ A`, there are a compact set `ω₀` and an open and closed set `D`,
invariant under conjugation by `Aˣ`, with `ω ⊆ D ⊆ ω₀^G = ⋃_u u ω₀ u⁻¹`.

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups* (notes by
DeBacker and Sally, 1999), §4, Lemma 4.3 (Lemma 10), printed p. 31. Harish-Chandra's proof uses
Lemma 2.6, a set of representatives of the conjugacy classes of Cartan subalgebras and
semisimple elements in orbit closures. The proof here is special to `G = GL₁(A)` and uses the
characteristic polynomial of left multiplication instead:

* `charpolyCoefficients F X` lists the coefficients of the characteristic polynomial `χ_X` of
  left multiplication by `X` on `A`; they are continuous (`continuous_charpolyCoefficients`) and
  invariant under conjugation (`charpolyCoefficients_conjugation`), and `χ_X (X) = 0`
  (`aeval_charpoly_lmul`).
* `exists_isCompact_conj_of_integral`: one compact set `K ⊆ A` contains a conjugate of every root
  of every monic polynomial over `F` whose coefficients have norm at most one. By the
  Wedderburn–Artin theorem `A ≅ ∏ᵢ M_{dᵢ}(Dᵢ)` with finite-dimensional division algebras `Dᵢ`.
  Each `Dᵢ` carries the ultrametric absolute value `x ↦ ‖N_{Dᵢ/F}(x)‖ ^ (1 / [Dᵢ : F])`
  (`CentralDivision.regularAbsoluteValue`), whose closed unit ball is compact.
  `LinearAlgebra.DivisionMatrixIntegerConjugation.exists_units_conj_integral_of_aeval`
  conjugates each component into the matrices with entries in that ball.
* `lieAlgebraConjugationDomain`: choose `t ≠ 0` with `‖t‖ ≤ 1` and `‖t‖ ‖cᵢ(X)‖ ≤ 1` for the
  coefficients `cᵢ(X)` of every `X ∈ ω`, and put `D = {X | ∀ i, ‖t cᵢ(X)‖ ≤ 1}` and
  `ω₀ = t⁻¹ K`. For `X ∈ D` the polynomial `scaleRoots χ_X t` is monic, has coefficients of norm
  at most one and has the root `t X`, so `t X` is conjugate into `K`.
-/

noncomputable section

open Polynomial Topology Set

namespace Langlands.HarmonicAnalysis

open UnitConjugation

namespace ConjugationDomain

/-! ### Integral elements are conjugate into a fixed compact set -/

section Integral

variable (F : Type*) [NontriviallyNormedField F] [CompleteSpace F] [IsUltrametricDist F]
  [LocallyCompactSpace F]
  (A : Type*) [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
  [TopologicalSpace A] [IsTopologicalRing A] [ContinuousSMul F A]

/-- In a finite-dimensional semisimple algebra over a complete, locally compact, ultrametric
nontrivially normed field, one compact set contains a conjugate, under the unit group, of every
root of every monic polynomial whose coefficients have norm at most one. -/
theorem exists_isCompact_conj_of_integral :
    ∃ K : Set A, IsCompact K ∧ ∀ (Y : A) (p : F[X]), p.Monic → (∀ i, ‖p.coeff i‖ ≤ 1) →
      aeval Y p = 0 → ∃ u : Aˣ, conjugationHomeomorph u Y ∈ K := by
  obtain ⟨k, Dv, d, _, _, _, -, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite F A
  let _ : ∀ i, NormedAddCommGroup (Dv i) := fun i =>
    @NonUnitalNormedRing.toNormedAddCommGroup _
      (@NormedRing.toNonUnitalNormedRing _ (CentralDivision.regularNormedRing F (Dv i)))
  let _ : ∀ i, NormedSpace F (Dv i) := fun i =>
    @NormedAlgebra.toNormedSpace F (Dv i) _
      (@NormedRing.toSeminormedRing _ (CentralDivision.regularNormedRing F (Dv i)))
      (CentralDivision.regularNormedAlgebra F (Dv i))
  have _ : ∀ i, ProperSpace (Dv i) := fun i => FiniteDimensional.proper F (Dv i)
  let B := Π i, Matrix (Fin (d i)) (Fin (d i)) (Dv i)
  let KB : Set B := Set.pi univ fun i => Set.pi univ fun _ => Set.pi univ fun _ =>
    Metric.closedBall (0 : Dv i) 1
  have hKB : IsCompact KB :=
    isCompact_univ_pi fun i => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_closedBall _ _
  have hcont : Continuous (e.symm : B → A) :=
    e.symm.toLinearMap.continuous_of_finiteDimensional
  refine ⟨e.symm '' KB, hKB.image hcont, fun Y p hp hcoeff hY => ?_⟩
  have hZ : ∀ i, aeval (e Y i) p = 0 := by
    intro i
    have h1 : aeval (e Y) p = 0 := by
      rw [Polynomial.aeval_algHom_apply e Y p, hY, map_zero]
    have h2 := Polynomial.aeval_algHom_apply
      (Pi.evalAlgHom F (fun i => Matrix (Fin (d i)) (Fin (d i)) (Dv i)) i) (e Y) p
    rw [h1, map_zero] at h2
    simpa using h2
  have hcoeff' : ∀ i j, CentralDivision.regularNormValuation F (Dv i)
      (algebraMap F (Dv i) (p.coeff j)) ≤ 1 := by
    intro i j
    rw [CentralDivision.regularNormValuation_algebraMap]
    refine pow_le_one₀ (by positivity) ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
    exact hcoeff j
  choose u hu using fun i =>
    LinearAlgebra.DivisionMatrixIntegerConjugation.exists_units_conj_integral_of_aeval
      (v := CentralDivision.regularNormValuation F (Dv i)) (e Y i) p hp (hcoeff' i) (hZ i)
  let U : Bˣ := MulEquiv.piUnits.symm u
  let U' : Aˣ := Units.map (e.symm : B →ₐ[F] A).toMonoidHom U
  refine ⟨U', (U : B) * e Y * ((U⁻¹ : Bˣ) : B), ?_, ?_⟩
  · intro i _ a _ b _
    rw [Metric.mem_closedBall, dist_zero_right]
    change CentralDivision.regularAbsoluteValue F (Dv i) _ ≤ 1
    rw [CentralDivision.regularAbsoluteValue_apply]
    refine Real.rpow_le_one (norm_nonneg _) ?_ (by positivity)
    have := hu i a b
    exact_mod_cast this
  · simp only [conjugationHomeomorph_apply, map_mul, AlgEquiv.symm_apply_apply]
    rfl

end Integral

/-! ### Characteristic-polynomial coefficients of left multiplication -/

section Coefficients

variable (F : Type*) [Field F] {A : Type*} [Ring A] [Algebra F A] [FiniteDimensional F A]

/-- The coefficients of `T ^ 0, …, T ^ (n - 1)` in the characteristic polynomial of left
multiplication by `X` on the `n`-dimensional `F`-vector space `A`. -/
def charpolyCoefficients (X : A) : Fin (Module.finrank F A) → F :=
  fun i => (Algebra.lmul F A X).charpoly.coeff i

/-- Cayley–Hamilton for left multiplication: `X` is a root of the characteristic polynomial of
left multiplication by `X`. -/
theorem aeval_charpoly_lmul (X : A) : aeval X (Algebra.lmul F A X).charpoly = 0 := by
  apply Algebra.lmul_injective (R := F)
  rw [← Polynomial.aeval_algHom_apply, map_zero]
  exact LinearMap.aeval_self_charpoly _

variable {F}

/-- The characteristic polynomial of left multiplication is invariant under conjugation. -/
theorem charpolyCoefficients_conjugation [TopologicalSpace A] [IsTopologicalRing A] (g : Aˣ)
    (X : A) : charpolyCoefficients F (conjugationHomeomorph g X) = charpolyCoefficients F X := by
  let e := Units.mulLeftLinearEquiv F A g
  have he : Algebra.lmul F A (conjugationHomeomorph g X) = e.conj (Algebra.lmul F A X) := by
    ext y
    change ((g : A) * X * (g⁻¹ : Aˣ).val) * y = (g : A) * (X * ((g⁻¹ : Aˣ).val * y))
    simp only [mul_assoc]
  funext i
  simp only [charpolyCoefficients, he, e.charpoly_conj]

/-- The coefficients are polynomial functions of the coordinates, hence continuous for the
module topology. -/
theorem continuous_charpolyCoefficients [TopologicalSpace F] [IsTopologicalRing F]
    [TopologicalSpace A] [IsModuleTopology F A] :
    Continuous (charpolyCoefficients (A := A) F) := by
  classical
  let d := Module.finrank F A
  let b := Module.finBasis F A
  let M (x : A) := LinearMap.toMatrix b b (Algebra.lmul F A x)
  apply continuous_pi
  intro i
  have h : (fun x : A => charpolyCoefficients F x i) =
      fun x => MvPolynomial.eval (fun jk : Fin d × Fin d => M x jk.1 jk.2)
        (MvPolynomial.map (Int.castRingHom F) ((Matrix.charpoly.univ ℤ (Fin d)).coeff i)) := by
    funext x
    rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, Matrix.charpoly.univ_coeff_eval₂Hom]
    change (Algebra.lmul F A x).charpoly.coeff i = (M x).charpoly.coeff i
    rw [LinearMap.charpoly_toMatrix]
  rw [h]
  apply (MvPolynomial.continuous_eval _).comp
  apply continuous_pi
  intro jk
  let L := (b.coord jk.1).comp ((LinearMap.applyₗ' F (b jk.2) : Module.End F A →ₗ[F] A).comp
    (Algebra.lmul F A).toLinearMap)
  have hL : (fun x : A => M x jk.1 jk.2) = L := by
    funext x
    exact LinearMap.toMatrix_apply b b (Algebra.lmul F A x) jk.1 jk.2
  rw [hL]
  exact IsModuleTopology.continuous_of_linearMap L

end Coefficients

end ConjugationDomain

open ConjugationDomain

universe u v

/-- **Harish-Chandra's Lemma 4.3** for the unit group of a finite-dimensional semisimple algebra
over a nonarchimedean local field of characteristic zero: every compact `ω ⊆ A` lies in an open,
closed, conjugation-invariant `D` contained in the saturation of a compact `ω₀`. -/
theorem lieAlgebraConjugationDomain : LieAlgebraConjugationDomainStatement.{u, v} := by
  intro F _ _ _ _ _ A _ _ _ _ _ _
  have := IsModuleTopology.isTopologicalRing F A
  intro ω hω
  let _ := LocalGalois.localNormedField F
  have := LocalGalois.localNormedField_ultrametric F
  have := LocalGalois.localNormedField_complete F
  obtain ⟨K, hK, hKY⟩ := exists_isCompact_conj_of_integral F A
  obtain ⟨C, hC⟩ := hω.exists_bound_of_continuousOn
    (continuous_charpolyCoefficients (F := F) (A := A)).continuousOn
  obtain ⟨t, ht0, htlt⟩ := NormedField.exists_norm_lt F
    (show (0 : ℝ) < (max C 0 + 1)⁻¹ by positivity)
  have htne : t ≠ 0 := norm_pos_iff.1 ht0
  have hC1 : 0 < max C 0 + 1 := by positivity
  have ht1 : ‖t‖ ≤ 1 := by
    refine htlt.le.trans ?_
    rw [inv_le_one₀ hC1]
    linarith [le_max_right C 0]
  have htC : ‖t‖ * C ≤ 1 := by
    have h := mul_lt_mul_of_pos_right htlt hC1
    rw [inv_mul_cancel₀ hC1.ne'] at h
    nlinarith [le_max_left C 0, le_max_right C 0, norm_nonneg t]
  refine ⟨(fun Z => t⁻¹ • Z) '' K, hK.image (continuous_const_smul _),
    {X | ∀ i, ‖t * charpolyCoefficients F X i‖ ≤ 1}, ?_, ?_, ?_, ?_⟩
  · have hD : {X : A | ∀ i, ‖t * charpolyCoefficients F X i‖ ≤ 1} =
        ⋂ i, (fun X => t * charpolyCoefficients F X i) ⁻¹' Metric.closedBall 0 1 := by
      ext X
      simp
    rw [hD]
    exact isClopen_iInter_of_finite fun i =>
      (IsUltrametricDist.isClopen_closedBall 0 one_ne_zero).preimage
        (continuous_const.mul ((continuous_apply i).comp continuous_charpolyCoefficients))
  · intro w X hX i
    rw [charpolyCoefficients_conjugation]
    exact hX i
  · intro X hX i
    rw [norm_mul]
    calc ‖t‖ * ‖charpolyCoefficients F X i‖ ≤ ‖t‖ * C :=
          mul_le_mul_of_nonneg_left ((norm_le_pi_norm _ i).trans (hC X hX)) (norm_nonneg _)
      _ ≤ 1 := htC
  · intro X hX
    set p := (Algebra.lmul F A X).charpoly with hpdef
    have hpX : aeval X p = 0 := aeval_charpoly_lmul F X
    have hpm : p.Monic := LinearMap.charpoly_monic _
    have hpd : p.natDegree = Module.finrank F A := LinearMap.charpoly_natDegree _
    have hq := Polynomial.scaleRoots_aeval_eq_zero (r := t) hpX
    have hqm : (p.scaleRoots t).Monic := (Polynomial.monic_scaleRoots_iff t).2 hpm
    have hqc : ∀ i, ‖(p.scaleRoots t).coeff i‖ ≤ 1 := by
      intro i
      rw [Polynomial.coeff_scaleRoots, norm_mul, norm_pow]
      rcases lt_trichotomy i p.natDegree with h | h | h
      · obtain ⟨k, hk⟩ : ∃ k, p.natDegree - i = k + 1 := ⟨p.natDegree - i - 1, by omega⟩
        rw [hk, pow_succ]
        have hi := hX ⟨i, hpd ▸ h⟩
        rw [norm_mul] at hi
        change ‖t‖ * ‖p.coeff i‖ ≤ 1 at hi
        calc ‖p.coeff i‖ * (‖t‖ ^ k * ‖t‖) ≤ ‖p.coeff i‖ * (1 * ‖t‖) := by
              gcongr
              exact pow_le_one₀ (norm_nonneg _) ht1
          _ = ‖t‖ * ‖p.coeff i‖ := by ring
          _ ≤ 1 := hi
      · rw [h, Nat.sub_self, pow_zero, mul_one]
        have := hpm.coeff_natDegree
        rw [this, norm_one]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h, norm_zero, zero_mul]
        exact zero_le_one
    obtain ⟨w, hw⟩ := hKY _ _ hqm hqc hq
    refine mem_conjugationSaturation_iff.2 ⟨w⁻¹,
      t⁻¹ • conjugationHomeomorph w (algebraMap F A t * X), ⟨_, hw, rfl⟩, ?_⟩
    simp only [conjugationHomeomorph_apply, inv_inv, ← Algebra.smul_def, mul_smul_comm,
      smul_mul_assoc, smul_smul, inv_mul_cancel₀ htne, one_smul]
    simp [mul_assoc]

end Langlands.HarmonicAnalysis
