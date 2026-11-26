import Langlands.Automorphic.GeneralLinearHilbertEnveloping
import Langlands.Global.ArchimedeanCenterConjugationKernel
import Langlands.Global.ArchimedeanCompactComponentCoverageProof
import Langlands.Representation.Archimedean.SmoothIntertwiner
import Langlands.Representation.Archimedean.BanachOrbitSmoothing
import Langlands.Representation.Archimedean.HilbertSubmoduleAction

/-! # Centre finiteness on smooth vectors of irreducible unitary representations -/

noncomputable section

open scoped Classical Topology Manifold ContDiff InnerProductSpace Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- A curve in a subspace has a derivative there once its image under an isometric linear
inclusion has the image derivative. -/
theorem HasDerivAt.of_isometry {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (L : P →L[ℝ] E) (hL : Isometry L)
    {f : ℝ → P} {y : P} {t : ℝ}
    (h : HasDerivAt (fun s => L (f s)) (L y) t) : HasDerivAt f y t := by
  rw [hasDerivAt_iff_tendsto_slope] at h ⊢
  have he : Topology.IsEmbedding L := hL.isEmbedding
  apply he.tendsto_nhds_iff.mpr
  have hs : (slope (fun s => L (f s)) t) = L ∘ slope f t := by
    funext s
    simp [slope_def_module, map_sub, map_smul]
  rwa [hs] at h

namespace Langlands.Algebra.UniformIntegral

section UniformIntegral

variable {B : Type*} [CommRing B] [Algebra ℂ B]

/-- If every element of a commutative complex algebra is a root of a monic polynomial of degree
at most `m`, then a family of nonzero pairwise orthogonal idempotents has at most `m` members. -/
theorem card_le_of_orthogonal_idempotents (m : ℕ)
    (h : ∀ b : B, ∃ q : Polynomial ℂ, q.Monic ∧ q.natDegree ≤ m ∧ Polynomial.aeval b q = 0)
    {ι : Type*} [Fintype ι] (e : ι → B) (he : ∀ i, e i * e i = e i)
    (horth : ∀ i j, i ≠ j → e i * e j = 0) (hne : ∀ i, e i ≠ 0) :
    Fintype.card ι ≤ m := by
  classical
  let f : ι → ℂ := fun i => ((Fintype.equivFin ι i : ℕ) : ℂ)
  have hf : Function.Injective f := by
    intro i j hij
    have h1 : ((Fintype.equivFin ι i : ℕ) : ℂ) = ((Fintype.equivFin ι j : ℕ) : ℂ) := hij
    exact (Fintype.equivFin ι).injective (Fin.ext (by exact_mod_cast h1))
  let b : B := ∑ i, f i • e i
  have hb (j : ι) : b * e j = f j • e j := by
    simp only [b, Finset.sum_mul, smul_mul_assoc]
    rw [Finset.sum_eq_single j]
    · rw [he]
    · intro i _ hij
      rw [horth i j hij, smul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hq (q : Polynomial ℂ) (j : ι) : Polynomial.aeval b q * e j = q.eval (f j) • e j := by
    induction q using Polynomial.induction_on with
    | C a => simp [Algebra.smul_def]
    | add p q hp hq => simp [add_mul, hp, hq, add_smul]
    | monomial k a ih =>
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, mul_assoc, hb, mul_smul_comm, ih,
        smul_smul]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      ring_nf
  obtain ⟨q, hqm, hqd, hq0⟩ := h b
  have hroot (j : ι) : q.IsRoot (f j) := by
    have h1 := hq q j
    rw [hq0, zero_mul] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_right (hne j)
  have hq0' : q ≠ 0 := hqm.ne_zero
  calc Fintype.card ι = (Finset.univ.image f).card := (Finset.card_image_of_injective _ hf).symm
    _ ≤ q.roots.toFinset.card := Finset.card_le_card (fun x hx => by
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
        exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq0').mpr (hroot j)))
    _ ≤ q.roots.card := Multiset.toFinset_card_le _
    _ ≤ q.natDegree := Polynomial.card_roots' q
    _ ≤ m := hqd

/-- A finite-dimensional reduced commutative complex algebra all of whose elements are roots of
monic polynomials of degree at most `m` has dimension at most `m`. -/
theorem finrank_le_of_isReduced_of_finiteDimensional [IsReduced B] [FiniteDimensional ℂ B]
    (m : ℕ)
    (h : ∀ b : B, ∃ q : Polynomial ℂ, q.Monic ∧ q.natDegree ≤ m ∧ Polynomial.aeval b q = 0) :
    Module.finrank ℂ B ≤ m := by
  classical
  have : IsArtinianRing B := isArtinian_of_tower ℂ inferInstance
  let e := IsArtinianRing.equivPi B
  let : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  let f : MaximalSpectrum B → B := fun I => e.symm (Pi.single I 1)
  have hef (I : MaximalSpectrum B) : e (f I) = Pi.single I 1 := e.apply_symm_apply _
  have hidem (I : MaximalSpectrum B) : f I * f I = f I := by
    apply e.injective
    rw [map_mul, hef, ← Pi.single_mul, mul_one]
  have horth (I J : MaximalSpectrum B) (hIJ : I ≠ J) : f I * f J = 0 := by
    apply e.injective
    rw [map_mul, hef, hef, map_zero]
    funext K
    by_cases hK : K = I
    · subst hK
      simp [Ne.symm hIJ]
    · simp [hK]
  have hne (I : MaximalSpectrum B) : f I ≠ 0 := by
    intro h0
    have h1 := congrArg (fun x => e x I) h0
    simp only [hef, map_zero, Pi.single_eq_same, Pi.zero_apply] at h1
    have : Nontrivial (B ⧸ I.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr I.isMaximal.ne_top
    exact one_ne_zero h1
  have hcard := card_le_of_orthogonal_idempotents m h f hidem horth hne
  have hspan : Submodule.span ℂ (Set.range f) = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    have hsurj (I : MaximalSpectrum B) : ∃ c : ℂ, algebraMap ℂ (B ⧸ I.asIdeal) c = e x I := by
      let : Field (B ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
      exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ)).2 _
    choose c hc using hsurj
    have hx : x = ∑ I, c I • f I := by
      apply e.injective
      funext J
      rw [map_sum, Finset.sum_apply]
      simp only [Algebra.smul_def, map_mul, Pi.mul_apply, hef]
      rw [Finset.sum_eq_single J]
      · rw [Pi.single_eq_same, mul_one, ← hc J]
        rfl
      · intro I _ hIJ
        simp [Ne.symm hIJ]
      · intro hJ
        exact absurd (Finset.mem_univ J) hJ
    rw [hx]
    exact Submodule.sum_mem _ fun I _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨I, rfl⟩)
  calc Module.finrank ℂ B = Module.finrank ℂ (⊤ : Submodule ℂ B) := finrank_top ℂ B |>.symm
    _ = Module.finrank ℂ (Submodule.span ℂ (Set.range f)) := by rw [hspan]
    _ ≤ Fintype.card (MaximalSpectrum B) := finrank_range_le_card f
    _ ≤ m := hcard

/-- A reduced commutative complex algebra all of whose elements are roots of monic polynomials
of degree at most `m` is finite-dimensional. -/
theorem finiteDimensional_of_isReduced_of_uniform [IsReduced B] (m : ℕ)
    (h : ∀ b : B, ∃ q : Polynomial ℂ, q.Monic ∧ q.natDegree ≤ m ∧ Polynomial.aeval b q = 0) :
    FiniteDimensional ℂ B := by
  classical
  have hrank : Module.rank ℂ B ≤ m := by
    apply rank_le
    intro s hs
    let B₀ := Algebra.adjoin ℂ (s : Set B)
    have hint : ∀ x ∈ (s : Set B), IsIntegral ℂ x := fun x _ => by
      obtain ⟨q, hqm, -, hq0⟩ := h x
      exact ⟨q, hqm, by rwa [← Polynomial.aeval_def]⟩
    have : Module.Finite ℂ B₀ := Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet hint
    have : IsReduced B₀ := isReduced_of_injective B₀.val Subtype.val_injective
    have h₀ : ∀ b : B₀, ∃ q : Polynomial ℂ, q.Monic ∧ q.natDegree ≤ m ∧
        Polynomial.aeval b q = 0 := fun b => by
      obtain ⟨q, hqm, hqd, hq0⟩ := h b.val
      refine ⟨q, hqm, hqd, Subtype.val_injective ?_⟩
      have hc := Subalgebra.aeval_coe B₀ b q
      rw [hq0] at hc
      rw [← hc]
      rfl
    have hfin := finrank_le_of_isReduced_of_finiteDimensional m h₀
    let g : s → B₀ := fun x => ⟨x, Algebra.subset_adjoin x.property⟩
    have hg : LinearIndependent ℂ g := by
      apply LinearIndependent.of_comp B₀.val.toLinearMap
      exact hs
    rw [← Fintype.card_coe]
    exact hg.fintype_card_le_finrank.trans hfin
  exact Module.rank_lt_aleph0_iff.mp (hrank.trans_lt (Cardinal.natCast_lt_aleph0))

end UniformIntegral

end Langlands.Algebra.UniformIntegral

namespace Langlands.Global.ArchimedeanGL

universe u

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- Conjugation on the enveloping centre takes only finitely many values on the actual
archimedean group. -/
theorem finite_range_centerConjugationHom : Finite (centerConjugationHom F n).range := by
  let c := centerConjugationHom F n
  let K := standardInfiniteCompact F n
  let a := c.comp K.subtype
  have hN : IsOpen (c.ker : Set (InfiniteAdelicGL F n)) := isOpen_ker_centerConjugationHom F n
  have hNc : IsClosed (c.ker : Set (InfiniteAdelicGL F n)) := Subgroup.isClosed_of_isOpen _ hN
  have hcomp : connectedComponent (1 : InfiniteAdelicGL F n) ⊆ c.ker :=
    (IsClopen.connectedComponent_subset ⟨hNc, hN⟩ c.ker.one_mem)
  have hrange : c.range = a.range := by
    apply le_antisymm
    · rintro _ ⟨g, rfl⟩
      obtain ⟨k, hk⟩ := compactComponentCoverage F n g
      have hmem : k.val⁻¹ * g ∈ connectedComponent (1 : InfiniteAdelicGL F n) := by
        have h := smul_connectedComponent k.val⁻¹ k.val
        rw [inv_mul_cancel] at h
        rw [← h]
        exact ⟨g, hk, rfl⟩
      have hker : c (k.val⁻¹ * g) = 1 := hcomp hmem
      refine ⟨k, ?_⟩
      change c k.val = c g
      rw [map_mul, map_inv, inv_mul_eq_one] at hker
      exact hker
    · rintro _ ⟨k, rfl⟩
      exact ⟨k.val, rfl⟩
  have : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_standardInfiniteCompact F n)
  have h : IsOpen (a.ker : Set K) := hN.preimage continuous_subtype_val
  have : Finite (K ⧸ a.ker) := Subgroup.quotient_finite_of_isOpen a.ker h
  have ha : Finite a.range := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange a).toEquiv
  rw [hrange]
  exact ha


open Langlands.Archimedean DerivativeSmoothVectors

attribute [local instance 100] LieRing.ofAssociativeRing

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (R : (ArchimedeanMatrix F n)ˣ →* (E →L[ℂ] E))

local notation "A" => ArchimedeanMatrix F n
local notation "I" => 𝓘(ℝ, A)
local notation "D" => DerivativeSmoothVectors I R

/-- The genuine enveloping action is covariant for the genuine smooth group action:
translating by `b` conjugates the enveloping element by `b`. -/
theorem hilbertEnvelopingAction_representation (hR : IsContinuousRepresentation R)
    (b : (ArchimedeanMatrix F n)ˣ) (a : EnvelopingAlgebra F n) (v : D) :
    hilbertEnvelopingAction F n R hR
        (envelopingConjugation F n ((archimedeanGLCoordinates F n).symm b) a)
        (representation I R b v) =
      representation I R b (hilbertEnvelopingAction F n R hR a v) := by
  induction a using enveloping_real_left_induction F n generalizing v with
  | h1 => simp
  | hadd a c ha hc => simp only [map_add, LinearMap.add_apply, ha, hc]
  | hsmul z a ha => simp only [map_smul, LinearMap.smul_apply, ha]
  | hgen X a ha =>
    simp only [map_mul, Module.End.mul_apply]
    rw [ha, envelopingConjugation_generator, complexLieConjugation_complexify,
      hilbertEnvelopingAction_real_generator, hilbertEnvelopingAction_real_generator,
      operator_representation_units]
    congr 2
    rw [inverseConjugationCLM_apply, realLieAlgebraToMatrix_realLieConjugation, map_inv,
      ContinuousMulEquiv.apply_symm_apply]
    simp [mul_assoc]

variable {R} in
/-- The genuine enveloping action commutes with the smooth map induced by a bounded operator
commuting with the archimedean action. -/
theorem hilbertEnvelopingAction_derivativeMapLinear (hR : IsContinuousRepresentation R)
    (C : E →L[ℂ] E) (hC : ∀ b v, C (R b v) = R b (C v)) (a : EnvelopingAlgebra F n) (v : D) :
    hilbertEnvelopingAction F n R hR a (SmoothIntertwiner.derivativeMapLinear I R R C hC v) =
      SmoothIntertwiner.derivativeMapLinear I R R C hC (hilbertEnvelopingAction F n R hR a v) := by
  induction a using enveloping_real_left_induction F n generalizing v with
  | h1 => simp
  | hadd a c ha hc => simp only [map_add, LinearMap.add_apply, ha, hc]
  | hsmul z a ha => simp only [map_smul, LinearMap.smul_apply, ha]
  | hgen X a ha =>
    rw [map_mul, Module.End.mul_apply, Module.End.mul_apply, ha,
      hilbertEnvelopingAction_real_generator]
    apply (toSmooth I R).injective
    rw [toSmooth_operator, SmoothIntertwiner.toSmooth_derivativeMapLinear,
      SmoothIntertwiner.toSmooth_derivativeMapLinear, toSmooth_operator,
      SmoothIntertwiner.map_smoothLieDerivative]




/-- The enveloping centre acting on genuine smooth vectors. -/
def hilbertCenterAction (hR : IsContinuousRepresentation R) :
    EnvelopingCenter F n →ₐ[ℂ] Module.End ℂ D :=
  (hilbertEnvelopingAction F n R hR).comp (centerInclusion F n)

/-- Conjugating a central element by `g` corresponds to translating by its coordinates. -/
theorem hilbertCenterAction_centerConjugation (hR : IsContinuousRepresentation R)
    (g : InfiniteAdelicGL F n) (z : EnvelopingCenter F n) (v : D) :
    hilbertCenterAction F n R hR (centerConjugation F n g z)
        (representation I R (archimedeanGLCoordinates F n g) v) =
      representation I R (archimedeanGLCoordinates F n g) (hilbertCenterAction F n R hR z v) := by
  have h := hilbertEnvelopingAction_representation F n R hR (archimedeanGLCoordinates F n g)
    (centerInclusion F n z) v
  rw [ContinuousMulEquiv.symm_apply_apply, ← centerInclusion_centerConjugation] at h
  exact h

theorem hilbertCenterAction_centerConjugation_eq_zero (hR : IsContinuousRepresentation R)
    (g : InfiniteAdelicGL F n) {z : EnvelopingCenter F n}
    (hz : hilbertCenterAction F n R hR z = 0) :
    hilbertCenterAction F n R hR (centerConjugation F n g z) = 0 := by
  apply LinearMap.ext
  intro v
  let b := archimedeanGLCoordinates F n g
  have hv : v = representation I R b (representation I R b⁻¹ v) := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hv, hilbertCenterAction_centerConjugation, hz, LinearMap.zero_apply, map_zero,
    LinearMap.zero_apply]

theorem hilbertCenterAction_centerConjugation_eq_zero_iff (hR : IsContinuousRepresentation R)
    (g : InfiniteAdelicGL F n) (z : EnvelopingCenter F n) :
    hilbertCenterAction F n R hR (centerConjugation F n g z) = 0 ↔
      hilbertCenterAction F n R hR z = 0 := by
  refine ⟨fun h => ?_, hilbertCenterAction_centerConjugation_eq_zero F n R hR g⟩
  have h' := hilbertCenterAction_centerConjugation_eq_zero F n R hR g⁻¹ h
  rwa [centerConjugation_inv, AlgEquiv.symm_apply_apply] at h'

theorem hilbertSmoothValue_injective : Function.Injective (hilbertSmoothValue F n R) :=
  fun _ _ hxy => (toSmooth I R).injective (Subtype.ext hxy)

theorem hilbertSmoothValue_representation (b : (ArchimedeanMatrix F n)ˣ) (v : D) :
    hilbertSmoothValue F n R (representation I R b v) = R b (hilbertSmoothValue F n R v) := rfl

theorem hilbertSmoothValue_derivativeMapLinear (C : E →L[ℂ] E) (hC : ∀ b v, C (R b v) = R b (C v))
    (v : D) :
    hilbertSmoothValue F n R (SmoothIntertwiner.derivativeMapLinear I R R C hC v) =
      C (hilbertSmoothValue F n R v) := rfl

section Exponential

/-- The coordinates of the archimedean exponential curve as a curve of units. -/
theorem coordinates_realLieExponentialCurve_val (X : RealLieAlgebra F n) (t : ℝ) :
    ((archimedeanGLCoordinates F n (realLieExponentialCurve F n X t) :
      (ArchimedeanMatrix F n)ˣ) : ArchimedeanMatrix F n) =
      NormedSpace.exp (t • realLieAlgebraToMatrix F n X) := by
  rw [realLieExponentialCurve, ContinuousMulEquiv.apply_symm_apply]
  rfl

/-- The exponential curve in units is smooth. -/
theorem contMDiff_coordinates_realLieExponentialCurve (X : RealLieAlgebra F n) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞
      (fun t : ℝ => archimedeanGLCoordinates F n (realLieExponentialCurve F n X t)) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  rw [contMDiff_iff_contDiff]
  have hfun : (Units.val ∘ fun t : ℝ => archimedeanGLCoordinates F n
      (realLieExponentialCurve F n X t)) =
      fun t : ℝ => NormedSpace.exp (t • realLieAlgebraToMatrix F n X) := by
    funext t
    exact coordinates_realLieExponentialCurve_val F n X t
  rw [hfun]
  have h : AnalyticOnNhd ℝ (NormedSpace.exp : ArchimedeanMatrix F n → ArchimedeanMatrix F n)
      Set.univ := fun B _ =>
    NormedSpace.analyticAt_exp_of_mem_ball (𝕂 := ℝ) B
      (by rw [NormedSpace.expSeries_radius_eq_top, Metric.mem_eball]; exact edist_lt_top _ _)
  exact h.contDiff.comp (contDiff_id.smul contDiff_const)

/-- The tangent of the exponential curve in units at zero is the matrix of the direction. -/
theorem hasMFDerivAt_coordinates_realLieExponentialCurve (X : RealLieAlgebra F n) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I
      (fun t : ℝ => archimedeanGLCoordinates F n (realLieExponentialCurve F n X t)) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (realLieAlgebraToMatrix F n X)) := by
  refine ⟨(contMDiff_coordinates_realLieExponentialCurve F n X).continuous.continuousAt, ?_⟩
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) (realLieAlgebraToMatrix F n X) (0 : ℝ)).hasFDerivAt
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  simp only [writtenInExtChartAt, extChartAt, mfld_simps]
  have hfun : (fun t : ℝ => ((archimedeanGLCoordinates F n (realLieExponentialCurve F n X t) :
      (ArchimedeanMatrix F n)ˣ) : ArchimedeanMatrix F n)) =
      fun t : ℝ => NormedSpace.exp (t • realLieAlgebraToMatrix F n X) := by
    funext t
    exact coordinates_realLieExponentialCurve_val F n X t
  convert h.hasFDerivWithinAt using 1
  · exact hfun
  · apply ContinuousLinearMap.ext_ring
    rfl

/-- **Genuine derivatives along exponential curves.** The orbit of a genuine smooth vector
along the real exponential curve in direction `X` has derivative at zero equal to the genuine
derivative of the vector in the matrix direction of `X`. -/
theorem hasDerivAt_exponentialOrbit (X : RealLieAlgebra F n) (v : D) :
    HasDerivAt (fun t : ℝ => R (archimedeanGLCoordinates F n (realLieExponentialCurve F n X t))
        (hilbertSmoothValue F n R v))
      (hilbertSmoothValue F n R (operator I R (realLieAlgebraToMatrix F n X) v)) 0 := by
  let o := orbitMap R (hilbertSmoothValue F n R v)
  have hv : Langlands.Archimedean.IsSmoothVector I R (hilbertSmoothValue F n R v) := (toSmooth I R v).property
  have hf : HasMFDerivAt I 𝓘(ℝ, E) o
      (archimedeanGLCoordinates F n (realLieExponentialCurve F n X 0))
      (mfderiv I 𝓘(ℝ, E) o 1) := by
    rw [realLieExponentialCurve_zero, map_one]
    exact (hv.mdifferentiableAt (by simp)).hasMFDerivAt
  have h := HasMFDerivAt.comp (0 : ℝ) hf (hasMFDerivAt_coordinates_realLieExponentialCurve F n X)
  rw [hasMFDerivAt_iff_hasFDerivAt] at h
  have hval : ((mfderiv I 𝓘(ℝ, E) o 1).comp
      ((1 : ℝ →L[ℝ] ℝ).smulRight (realLieAlgebraToMatrix F n X))) (1 : ℝ) =
      hilbertSmoothValue F n R (operator I R (realLieAlgebraToMatrix F n X) v) := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self, one_smul]
    rfl
  exact h.hasDerivAt.congr_deriv hval

/-- **Identification of enveloping derivatives.** Let `y` assign to every enveloping element a
vector, additively and complex-linearly, with `y 1` the value of the genuine smooth vector `v`.
If the orbit of every `y a` along every real exponential curve has derivative `y (X a)` at zero,
then every `y a` is the value of the genuine enveloping derivative of `v`. -/
theorem eq_hilbertEnvelopingAction_of_hasDerivAt (hR : IsContinuousRepresentation R) (v : D)
    (y : EnvelopingAlgebra F n → E) (h1 : y 1 = hilbertSmoothValue F n R v)
    (hadd : ∀ a b, y (a + b) = y a + y b) (hsmul : ∀ (c : ℂ) a, y (c • a) = c • y a)
    (hder : ∀ X a, HasDerivAt
      (fun t : ℝ => R (archimedeanGLCoordinates F n (realLieExponentialCurve F n X t)) (y a))
      (y (envelopingGenerator F n (complexify F n X) * a)) 0)
    (a : EnvelopingAlgebra F n) :
    y a = hilbertSmoothValue F n R (hilbertEnvelopingAction F n R hR a v) := by
  induction a using enveloping_real_left_induction F n with
  | h1 => rw [h1, map_one, Module.End.one_apply]
  | hadd a b ha hb => rw [hadd, ha, hb, map_add, LinearMap.add_apply, map_add]
  | hsmul c a ha => rw [hsmul, ha, map_smul, LinearMap.smul_apply, map_smul]
  | hgen X a ha =>
    have h := hder X a
    rw [ha] at h
    have h' := hasDerivAt_exponentialOrbit F n R X (hilbertEnvelopingAction F n R hR a v)
    rw [h.unique h', map_mul, Module.End.mul_apply, hilbertEnvelopingAction_real_generator]

end Exponential

section Orbit

/-- The finite set of conjugations of the enveloping centre. -/
def centerConjugationFinset : Finset (EnvelopingCenter F n ≃ₐ[ℂ] EnvelopingCenter F n) :=
  haveI := finite_range_centerConjugationHom F n
  (Set.toFinite ((centerConjugationHom F n).range :
    Set (EnvelopingCenter F n ≃ₐ[ℂ] EnvelopingCenter F n))).toFinset

theorem mem_centerConjugationFinset_iff (γ : EnvelopingCenter F n ≃ₐ[ℂ] EnvelopingCenter F n) :
    γ ∈ centerConjugationFinset F n ↔ γ ∈ (centerConjugationHom F n).range := by
  simp [centerConjugationFinset]

/-- The product of `X - γ z` over all conjugations `γ` of the enveloping centre. -/
def centerOrbitPolynomial (z : EnvelopingCenter F n) : Polynomial (EnvelopingCenter F n) :=
  ∏ γ ∈ centerConjugationFinset F n, (Polynomial.X - Polynomial.C (γ z))

theorem centerOrbitPolynomial_monic (z : EnvelopingCenter F n) :
    (centerOrbitPolynomial F n z).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun γ _ => Polynomial.monic_X_sub_C (γ z)

theorem natDegree_centerOrbitPolynomial_le (z : EnvelopingCenter F n) :
    (centerOrbitPolynomial F n z).natDegree ≤ (centerConjugationFinset F n).card := by
  rw [centerOrbitPolynomial]
  have h1 : ∀ γ ∈ centerConjugationFinset F n,
      (Polynomial.X - Polynomial.C (γ z)).natDegree ≤ 1 := fun γ _ =>
    Polynomial.natDegree_X_sub_C_le (γ z)
  have h2 := Finset.sum_le_sum h1
  rw [Finset.sum_const, smul_eq_mul, mul_one] at h2
  exact (Polynomial.natDegree_prod_le _ _).trans h2

theorem aeval_centerOrbitPolynomial (z : EnvelopingCenter F n) :
    Polynomial.aeval z (centerOrbitPolynomial F n z) = 0 := by
  rw [centerOrbitPolynomial, map_prod]
  exact Finset.prod_eq_zero ((mem_centerConjugationFinset_iff F n 1).mpr (one_mem _)) (by simp)

theorem centerConjugation_coeff_centerOrbitPolynomial (g : InfiniteAdelicGL F n)
    (z : EnvelopingCenter F n) (k : ℕ) :
    centerConjugation F n g ((centerOrbitPolynomial F n z).coeff k) =
      (centerOrbitPolynomial F n z).coeff k := by
  have hmap : (centerOrbitPolynomial F n z).map (centerConjugation F n g).toRingHom =
      centerOrbitPolynomial F n z := by
    rw [centerOrbitPolynomial, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    let c := centerConjugationHom F n g
    have hc : c = centerConjugation F n g := rfl
    refine Finset.prod_nbij' (fun γ => c * γ) (fun γ => c⁻¹ * γ) ?_ ?_ ?_ ?_ ?_
    · intro γ hγ
      rw [mem_centerConjugationFinset_iff] at hγ ⊢
      exact (centerConjugationHom F n).range.mul_mem ⟨g, rfl⟩ hγ
    · intro γ hγ
      rw [mem_centerConjugationFinset_iff] at hγ ⊢
      exact (centerConjugationHom F n).range.mul_mem
        ((centerConjugationHom F n).range.inv_mem ⟨g, rfl⟩) hγ
    · intro γ _
      simp
    · intro γ _
      simp
    · intro γ _
      rw [AlgEquiv.mul_apply, hc]
      rfl
  have h := congrArg (fun p => Polynomial.coeff p k) hmap
  simp only [Polynomial.coeff_map] at h
  exact h

end Orbit

section Scalar

variable {𝒢 : Type*} [Group 𝒢] (ρ : 𝒢 →* (E →L[ℂ] E))
  (ι : (ArchimedeanMatrix F n)ˣ →* 𝒢)

include ρ in
omit [NumberField F] in
/-- If every operator of `ρ` normalizes the archimedean action, it is an archimedean
translation followed by an operator commuting with the archimedean action. -/
theorem exists_eq_mul_commute
    (hnorm : ∀ g : 𝒢, ∃ b : (ArchimedeanMatrix F n)ˣ, ∀ a, ρ g * R a = R (b * a * b⁻¹) * ρ g)
    (g : 𝒢) : ∃ (b : (ArchimedeanMatrix F n)ˣ) (C : E →L[ℂ] E),
      (∀ a v, C (R a v) = R a (C v)) ∧ ρ g = R b * C := by
  obtain ⟨b, hb⟩ := hnorm g
  refine ⟨b, R b⁻¹ * ρ g, fun a v => ?_, ?_⟩
  · change (R b⁻¹ * ρ g * R a) v = (R a * (R b⁻¹ * ρ g)) v
    rw [mul_assoc, hb, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul]
    congr 3
    group
  · rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

variable [CompleteSpace E] [MeasurableSpace (ArchimedeanMatrix F n)ˣ]
  [BorelSpace (ArchimedeanMatrix F n)ˣ]

/-- **Scalar action of conjugation-invariant enveloping elements.** Let `ρ` be a unitary
topologically irreducible representation whose restriction `R` to the archimedean group is
jointly continuous and is normalized by every operator of `ρ`. Then every element of the
enveloping algebra fixed by all archimedean conjugations acts by a scalar on the genuine smooth
vectors. -/
theorem exists_hilbertEnvelopingAction_eq_smul (μ : MeasureTheory.Measure (ArchimedeanMatrix F n)ˣ)
    [μ.IsHaarMeasure] (hR : IsContinuousRepresentation R) (hRρ : ∀ b, ρ (ι b) = R b)
    (hnorm : ∀ g : 𝒢, ∃ b : (ArchimedeanMatrix F n)ˣ, ∀ a, ρ g * R a = R (b * a * b⁻¹) * ρ g)
    (hU : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (hirr : IsTopologicallyIrreducible ρ) (s : EnvelopingAlgebra F n)
    (hs : ∀ g, envelopingConjugation F n g s = s) :
    ∃ c : ℂ, ∀ v : D, hilbertEnvelopingAction F n R hR s v = c • v := by
  let Av := hilbertSmoothValue F n R
  let ds := hilbertEnvelopingAction F n R hR s
  let Bv := Av.comp ds
  have hUR : ∀ g x y, inner ℂ (R g x) (R g y) = inner ℂ x y := fun g x y => by
    rw [← hRρ]; exact hU _ x y
  have hd : DenseRange (Av : D → E) :=
    (dense_smoothVectors_units R μ hR).mono (fun x hx => ⟨⟨x, hx⟩, rfl⟩)
  have hA : Av ≠ 0 := by
    have := hirr.1
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    intro he
    have hclosed : IsClosed ({0} : Set E) := isClosed_singleton
    have hh : Set.range (Av : D → E) ⊆ ({0} : Set E) := by
      rw [he]
      simp
    exact hx (Set.mem_singleton_iff.mp (closure_minimal hh hclosed (hd x)))
  have hstable (g : 𝒢) (v : D) : ∃ w, Av w = ρ g (Av v) ∧ Bv w = ρ g (Bv v) := by
    obtain ⟨b, C, hC, hg⟩ := exists_eq_mul_commute F n R ρ hnorm g
    refine ⟨representation I R b (SmoothIntertwiner.derivativeMapLinear I R R C hC v), ?_, ?_⟩
    · rw [hg]
      rfl
    · have h1 := hilbertEnvelopingAction_representation F n R hR b s
        (SmoothIntertwiner.derivativeMapLinear I R R C hC v)
      rw [hs] at h1
      change Av (ds _) = _
      rw [h1, hilbertEnvelopingAction_derivativeMapLinear F n hR C hC, hg]
      rfl
  obtain ⟨T, hT⟩ := exists_hilbertEnvelopingAction_formalAdjoint F n R hR hUR s
  obtain ⟨S, hS, he⟩ := exists_unitaryIntertwiner_of_regularization_pairing ρ ρ hU hU hirr
    Av Bv hA hstable (fun w => Av (T w)) Av hd (fun v w => hT v w)
  have hc (g : 𝒢) : Commute S (ρ g) := ContinuousLinearMap.ext (he g)
  obtain ⟨c, hc⟩ := exists_eq_scalar_of_unitary_commute ρ hU hirr S hc
  refine ⟨c, fun v => ?_⟩
  have hinj : Function.Injective Av := fun x y hxy =>
    (toSmooth I R).injective (Subtype.ext hxy)
  apply hinj
  change Bv v = Av (c • v)
  rw [← hS, hc, map_smul]
  rfl




/-- **Integrality of the centre.** Under the hypotheses of
`exists_hilbertEnvelopingAction_eq_smul`, every element of the enveloping centre acts on the
genuine smooth vectors as a root of a monic complex polynomial whose degree is at most the
number of conjugations of the centre. The coefficients come from the conjugation-invariant
coefficients of `centerOrbitPolynomial`, which act by scalars. -/
theorem exists_monic_aeval_hilbertCenterAction_eq_zero
    (μ : MeasureTheory.Measure (ArchimedeanMatrix F n)ˣ)
    [μ.IsHaarMeasure] (hR : IsContinuousRepresentation R) (hRρ : ∀ b, ρ (ι b) = R b)
    (hnorm : ∀ g : 𝒢, ∃ b : (ArchimedeanMatrix F n)ˣ, ∀ a, ρ g * R a = R (b * a * b⁻¹) * ρ g)
    (hU : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (hirr : IsTopologicallyIrreducible ρ) (z : EnvelopingCenter F n) :
    ∃ q : Polynomial ℂ, q.Monic ∧ q.natDegree ≤ (centerConjugationFinset F n).card ∧
      Polynomial.aeval (hilbertCenterAction F n R hR z) q = 0 := by
  let p := centerOrbitPolynomial F n z
  let N := p.natDegree
  let Ψ := hilbertCenterAction F n R hR
  have hcoef (k : ℕ) : ∃ c : ℂ, ∀ v, Ψ (p.coeff k) v = c • v :=
    exists_hilbertEnvelopingAction_eq_smul F n R ρ ι μ hR hRρ hnorm hU hirr
      (centerInclusion F n (p.coeff k)) (fun g => by
        rw [← centerInclusion_centerConjugation, centerConjugation_coeff_centerOrbitPolynomial])
  choose c hc using hcoef
  let r : Polynomial ℂ := ∑ i : Fin N, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)
  have hr : r.degree < N := Polynomial.degree_sum_fin_lt _
  refine ⟨Polynomial.X ^ N + r, Polynomial.monic_X_pow_add hr, ?_, ?_⟩
  · have hdeg : (Polynomial.X ^ N + r).natDegree = N := by
      rw [Polynomial.natDegree_add_eq_left_of_degree_lt
        (by rwa [Polynomial.degree_X_pow]), Polynomial.natDegree_X_pow]
    rw [hdeg]
    exact natDegree_centerOrbitPolynomial_le F n z
  · have hpm : p.Monic := centerOrbitPolynomial_monic F n z
    have hp : Polynomial.aeval z p = 0 := aeval_centerOrbitPolynomial F n z
    rw [hpm.as_sum] at hp
    simp only [map_add, map_sum, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_self, RingHom.id_apply] at hp
    have hΨ := congrArg Ψ hp
    simp only [map_add, map_sum, map_mul, map_pow, map_zero] at hΨ
    have hcoefΨ (i : ℕ) : Ψ (p.coeff i) = algebraMap ℂ (Module.End ℂ D) (c i) :=
      LinearMap.ext fun v => by rw [hc, Module.algebraMap_end_apply]
    simp only [hcoefΨ] at hΨ
    rw [Finset.sum_range (fun i => algebraMap ℂ (Module.End ℂ D) (c i) * Ψ z ^ i)] at hΨ
    simpa only [r, map_add, map_sum, map_mul, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C] using hΨ


/-- **No square-zero central operators.** Under the hypotheses of
`exists_hilbertEnvelopingAction_eq_smul`, a central element whose square acts by zero on the
genuine smooth vectors acts by zero.

Among the finite products of conjugates of `w` that act nonzero, the maximal ones are permuted
by conjugation. The closure of the span of their images is invariant and nonzero, hence
everything. The action of `w` kills the image of every maximal product. By the formal-adjoint
pairing, every value of the formal adjoint of `w` is orthogonal to the images of the maximal
products, hence to their dense span. So the adjoint vanishes, and by density of the smooth
vectors so does `w`. -/
theorem hilbertCenterAction_eq_zero_of_mul_self_eq_zero
    (μ : MeasureTheory.Measure (ArchimedeanMatrix F n)ˣ)
    [μ.IsHaarMeasure] (hR : IsContinuousRepresentation R) (hRρ : ∀ b, ρ (ι b) = R b)
    (hnorm : ∀ g : 𝒢, ∃ b : (ArchimedeanMatrix F n)ˣ, ∀ a, ρ g * R a = R (b * a * b⁻¹) * ρ g)
    (hU : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (hirr : IsTopologicallyIrreducible ρ) (w : EnvelopingCenter F n)
    (hw : hilbertCenterAction F n R hR w * hilbertCenterAction F n R hR w = 0) :
    hilbertCenterAction F n R hR w = 0 := by
  classical
  let Ψ := hilbertCenterAction F n R hR
  let Av := hilbertSmoothValue F n R
  let Γ := centerConjugationFinset F n
  have hUR : ∀ g x y, inner ℂ (R g x) (R g y) = inner ℂ x y := fun g x y => by
    rw [← hRρ]; exact hU _ x y
  have hd : DenseRange (Av : D → E) :=
    (dense_smoothVectors_units R μ hR).mono (fun x hx => ⟨⟨x, hx⟩, rfl⟩)
  by_contra hne
  let W : Finset (EnvelopingCenter F n ≃ₐ[ℂ] EnvelopingCenter F n) → EnvelopingCenter F n :=
    fun S => ∏ γ ∈ S, γ w
  let 𝓕 := Γ.powerset.filter (fun S => Ψ (W S) ≠ 0)
  let Mx : Finset (EnvelopingCenter F n ≃ₐ[ℂ] EnvelopingCenter F n) → Prop :=
    fun S => S ∈ 𝓕 ∧ ∀ T ∈ 𝓕, S ⊆ T → T = S
  have h1Γ : (1 : EnvelopingCenter F n ≃ₐ[ℂ] EnvelopingCenter F n) ∈ Γ :=
    (mem_centerConjugationFinset_iff F n 1).mpr (one_mem _)
  -- a maximal element above `{1}`
  obtain ⟨S₀, hS₀⟩ : ∃ S₀, Mx S₀ := by
    let 𝓕' := 𝓕.filter (fun S => {1} ⊆ S)
    have hne' : 𝓕'.Nonempty := ⟨{1}, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr h1Γ), by simpa [W] using hne⟩,
      Finset.Subset.refl _⟩⟩
    obtain ⟨m, hm, hmax⟩ := 𝓕'.exists_maximal hne'
    refine ⟨m, (Finset.mem_filter.mp hm).1, fun T hT hmT => ?_⟩
    have hT' : T ∈ 𝓕' := Finset.mem_filter.mpr ⟨hT, (Finset.mem_filter.mp hm).2.trans hmT⟩
    exact Finset.Subset.antisymm (hmax hT' hmT) hmT
  -- conjugation permutes maximal elements
  have hWconj (c : EnvelopingCenter F n ≃ₐ[ℂ] EnvelopingCenter F n) (S) :
      W (S.image (c * ·)) = c (W S) := by
    simp only [W, map_prod]
    rw [Finset.prod_image fun x _ y _ hxy => mul_left_cancel hxy]
    rfl
  have hΓmul (c) (hc : c ∈ (centerConjugationHom F n).range) {S} (hS : S ⊆ Γ) :
      S.image (c * ·) ⊆ Γ := by
    intro x hx
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hx
    change c * γ ∈ centerConjugationFinset F n
    rw [mem_centerConjugationFinset_iff]
    exact mul_mem hc ((mem_centerConjugationFinset_iff F n γ).mp (hS hγ))
  have hMx (g : InfiniteAdelicGL F n) {S} (hS : Mx S) :
      Mx (S.image (centerConjugationHom F n g * ·)) := by
    have hc : centerConjugationHom F n g ∈ (centerConjugationHom F n).range := ⟨g, rfl⟩
    have hSΓ : S ⊆ Γ := Finset.mem_powerset.mp (Finset.mem_filter.mp hS.1).1
    have hmem : ∀ T, T ∈ 𝓕 ↔ T ⊆ Γ ∧ Ψ (W T) ≠ 0 := fun T => by
      simp [𝓕, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨(hmem _).mpr ⟨hΓmul _ hc hSΓ, ?_⟩, fun T hT hST => ?_⟩
    · rw [hWconj]
      change Ψ (centerConjugation F n g (W S)) ≠ 0
      rw [Ne, hilbertCenterAction_centerConjugation_eq_zero_iff]
      exact ((hmem S).mp hS.1).2
    · let c := centerConjugationHom F n g
      have hT' : T.image (c⁻¹ * ·) ∈ 𝓕 := by
        refine (hmem _).mpr ⟨hΓmul _ (inv_mem hc) ((hmem T).mp hT).1, ?_⟩
        rw [hWconj]
        change Ψ (centerConjugation F n g⁻¹ (W T)) ≠ 0
        rw [Ne, hilbertCenterAction_centerConjugation_eq_zero_iff]
        exact ((hmem T).mp hT).2
      have hsub : S ⊆ T.image (c⁻¹ * ·) := by
        intro x hx
        refine Finset.mem_image.mpr ⟨c * x, hST (Finset.mem_image_of_mem _ hx), ?_⟩
        simp
      have heq := hS.2 _ hT' hsub
      rw [← heq, Finset.image_image]
      have : ((c * ·) ∘ (c⁻¹ * ·)) = id := funext fun x => by simp
      rw [this, Finset.image_id]
  -- `w` times a maximal product acts by zero
  have hkill {S} (hS : Mx S) : Ψ w * Ψ (W S) = 0 := by
    have hSΓ : S ⊆ Γ := Finset.mem_powerset.mp (Finset.mem_filter.mp hS.1).1
    by_cases h1 : (1 : EnvelopingCenter F n ≃ₐ[ℂ] EnvelopingCenter F n) ∈ S
    · have hW : W S = w * W (S.erase 1) := by
        simp only [W]
        rw [← Finset.mul_prod_erase S _ h1]
        rfl
      rw [hW, map_mul, ← mul_assoc, hw, zero_mul]
    · have hW : W (insert 1 S) = w * W S := by
        simp only [W]
        rw [Finset.prod_insert h1]
        rfl
      by_contra hne'
      rw [← map_mul, ← hW] at hne'
      have hmem : insert 1 S ∈ 𝓕 := by
        simp only [𝓕, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.insert_subset h1Γ hSΓ, hne'⟩
      exact h1 ((hS.2 _ hmem (Finset.subset_insert _ _)) ▸ Finset.mem_insert_self 1 S)
  -- the invariant subspace
  let Uset : Set E := {x | ∃ S, Mx S ∧ ∃ d : D, x = Av (Ψ (W S) d)}
  let Us := Submodule.span ℂ Uset
  let U := Us.topologicalClosure
  have hUc : IsClosed (U : Set E) := Us.isClosed_topologicalClosure
  have hUinv : ∀ g, ∀ x ∈ U, ρ g x ∈ U := by
    intro g
    obtain ⟨b, C, hC, hg⟩ := exists_eq_mul_commute F n R ρ hnorm g
    have hgen : Submodule.span ℂ Uset ≤ U.comap (ρ g).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨S, hS, d, rfl⟩
      apply Submodule.le_topologicalClosure
      apply Submodule.subset_span
      let g' := (archimedeanGLCoordinates F n).symm b
      refine ⟨S.image (centerConjugationHom F n g' * ·), hMx g' hS,
        representation I R b (SmoothIntertwiner.derivativeMapLinear I R R C hC d), ?_⟩
      rw [hWconj]
      change ρ g (Av (Ψ (W S) d)) =
        Av (Ψ (centerConjugation F n g' (W S)) (representation I R b _))
      have hb : archimedeanGLCoordinates F n g' = b := ContinuousMulEquiv.apply_symm_apply _ _
      have h := hilbertCenterAction_centerConjugation F n R hR g' (W S)
        (SmoothIntertwiner.derivativeMapLinear I R R C hC d)
      rw [hb] at h
      rw [h, hilbertSmoothValue_representation]
      change ρ g (Av (Ψ (W S) d)) = R b (Av (hilbertEnvelopingAction F n R hR
        (centerInclusion F n (W S)) (SmoothIntertwiner.derivativeMapLinear I R R C hC d)))
      rw [hilbertEnvelopingAction_derivativeMapLinear F n hR C hC,
        hilbertSmoothValue_derivativeMapLinear, hg]
      rfl
    have hclosed : IsClosed ((U.comap (ρ g).toLinearMap : Submodule ℂ E) : Set E) :=
      hUc.preimage (ρ g).continuous
    exact Submodule.topologicalClosure_minimal _ hgen hclosed
  have hUtop : U = ⊤ := by
    rcases hirr.2 U hUc hUinv with h | h
    · exfalso
      have hS₀ne : Ψ (W S₀) ≠ 0 := (Finset.mem_filter.mp hS₀.1).2
      obtain ⟨d, hd0⟩ : ∃ d, Ψ (W S₀) d ≠ 0 :=
        not_forall.mp fun hall => hS₀ne (LinearMap.ext hall)
      have hmemU : Av (Ψ (W S₀) d) ∈ U :=
        Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨S₀, hS₀, d, rfl⟩)
      rw [h, Submodule.mem_bot] at hmemU
      exact hd0 (hilbertSmoothValue_injective F n R (by rw [hmemU, map_zero]))
    · exact h
  -- the formal adjoint of `w` vanishes
  obtain ⟨T, hT⟩ := exists_hilbertEnvelopingAction_formalAdjoint F n R hR hUR (centerInclusion F n w)
  have hTzero (u : D) : Av (T u) = 0 := by
    let K := LinearMap.ker ((innerSL ℂ (Av (T u)) : E →L[ℂ] ℂ) : E →ₗ[ℂ] ℂ)
    have hK : IsClosed (K : Set E) :=
      ContinuousLinearMap.isClosed_ker (innerSL ℂ (Av (T u)))
    have hspan : Submodule.span ℂ Uset ≤ K := by
      apply Submodule.span_le.mpr
      rintro _ ⟨S, hS, d, rfl⟩
      change inner ℂ (Av (T u)) (Av (Ψ (W S) d)) = 0
      rw [← inner_conj_symm]
      have h := hT (Ψ (W S) d) u
      change inner ℂ (Av (Ψ w (Ψ (W S) d))) (Av u) = _ at h
      rw [← h, ← Module.End.mul_apply, hkill hS, LinearMap.zero_apply, map_zero, inner_zero_left,
        map_zero]
    have hUK : U ≤ K := Submodule.topologicalClosure_minimal _ hspan hK
    have hmem : Av (T u) ∈ K := hUK (hUtop ▸ Submodule.mem_top)
    have h2 : inner ℂ (Av (T u)) (Av (T u)) = 0 := by
      rw [← innerSL_apply_apply ℂ]
      exact hmem
    exact inner_self_eq_zero.mp h2
  apply hne
  apply LinearMap.ext
  intro x
  apply hilbertSmoothValue_injective F n R
  rw [LinearMap.zero_apply, map_zero]
  apply ext_inner_right ℂ
  intro y
  rw [inner_zero_left]
  have hc : IsClosed {y : E | inner ℂ (Av (Ψ w x)) y = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hrange : Set.range (Av : D → E) ⊆ {y : E | inner ℂ (Av (Ψ w x)) y = 0} := by
    rintro _ ⟨u, rfl⟩
    have h := hT x u
    change inner ℂ (Av (Ψ w x)) (Av u) = _ at h
    change inner ℂ (Av (Ψ w x)) (Av u) = 0
    rw [h, hTzero, inner_zero_right]
  exact closure_minimal hrange hc (hd y)


/-- **Centre finiteness on smooth vectors.** Let `ρ` be a unitary topologically irreducible
representation of a group on a complex Hilbert space whose restriction `R` to the archimedean
group is jointly continuous and is normalized by every operator of `ρ`. Then the kernel of the
enveloping centre acting on the genuine smooth vectors has finite complex codimension. -/
theorem finite_quotient_ker_hilbertCenterAction
    (μ : MeasureTheory.Measure (ArchimedeanMatrix F n)ˣ)
    [μ.IsHaarMeasure] (hR : IsContinuousRepresentation R) (hRρ : ∀ b, ρ (ι b) = R b)
    (hnorm : ∀ g : 𝒢, ∃ b : (ArchimedeanMatrix F n)ˣ, ∀ a, ρ g * R a = R (b * a * b⁻¹) * ρ g)
    (hU : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (hirr : IsTopologicallyIrreducible ρ) :
    Module.Finite ℂ (EnvelopingCenter F n ⧸
      (RingHom.ker (hilbertCenterAction F n R hR)).restrictScalars ℂ) := by
  let Ψ := hilbertCenterAction F n R hR
  let J := RingHom.ker Ψ
  let mk := Ideal.Quotient.mkₐ ℂ J
  have hred : IsReduced (EnvelopingCenter F n ⧸ J) := by
    rw [isReduced_iff_pow_one_lt 2 one_lt_two]
    intro x hx
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, RingHom.mem_ker] at hx
    rw [Ideal.Quotient.eq_zero_iff_mem, RingHom.mem_ker]
    exact hilbertCenterAction_eq_zero_of_mul_self_eq_zero F n R ρ ι μ hR hRρ hnorm hU hirr z
      (by rw [← map_mul, ← pow_two]; exact hx)
  have huni : ∀ x : EnvelopingCenter F n ⧸ J, ∃ q : Polynomial ℂ, q.Monic ∧
      q.natDegree ≤ (centerConjugationFinset F n).card ∧ Polynomial.aeval x q = 0 := by
    intro x
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨q, hqm, hqd, hq0⟩ :=
      exists_monic_aeval_hilbertCenterAction_eq_zero F n R ρ ι μ hR hRρ hnorm hU hirr z
    refine ⟨q, hqm, hqd, ?_⟩
    change Polynomial.aeval (mk z) q = 0
    rw [Polynomial.aeval_algHom_apply]
    change Ideal.Quotient.mk J _ = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, RingHom.mem_ker, ← Polynomial.aeval_algHom_apply]
    exact hq0
  have hfin := Langlands.Algebra.UniformIntegral.finiteDimensional_of_isReduced_of_uniform _ huni
  exact Module.Finite.equiv (Submodule.Quotient.restrictScalarsEquiv ℂ J).symm

/-- Every genuine smooth vector has a finite-dimensional orbit under the enveloping centre:
one ideal of finite codimension kills all of them. -/
theorem exists_ideal_hilbertCenterAction
    (μ : MeasureTheory.Measure (ArchimedeanMatrix F n)ˣ)
    [μ.IsHaarMeasure] (hR : IsContinuousRepresentation R) (hRρ : ∀ b, ρ (ι b) = R b)
    (hnorm : ∀ g : 𝒢, ∃ b : (ArchimedeanMatrix F n)ˣ, ∀ a, ρ g * R a = R (b * a * b⁻¹) * ρ g)
    (hU : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (hirr : IsTopologicallyIrreducible ρ) :
    ∃ J : Ideal (EnvelopingCenter F n),
      Module.Finite ℂ (EnvelopingCenter F n ⧸ J.restrictScalars ℂ) ∧
      ∀ z ∈ J, ∀ v : D, hilbertCenterAction F n R hR z v = 0 :=
  ⟨RingHom.ker (hilbertCenterAction F n R hR),
    finite_quotient_ker_hilbertCenterAction F n R ρ ι μ hR hRρ hnorm hU hirr,
    fun z hz v => by rw [RingHom.mem_ker.mp hz, LinearMap.zero_apply]⟩


end Scalar

section Ambient

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {𝒢 : Type*} [Group 𝒢] (ρ : 𝒢 →* (E →L[ℂ] E)) (ι : (ArchimedeanMatrix F n)ˣ →* 𝒢)
  [MeasurableSpace (ArchimedeanMatrix F n)ˣ] [BorelSpace (ArchimedeanMatrix F n)ˣ]
  (μ : MeasureTheory.Measure (ArchimedeanMatrix F n)ˣ) [μ.IsHaarMeasure]

/-- **A common centre annihilator for smoothing families in an irreducible subspace.** Let `ρ`
be a unitary representation on a complex Hilbert space whose archimedean restriction is jointly
continuous and normalized by `ρ`, and let `M` be a nonzero closed invariant subspace, minimal
among such subspaces. There is an ideal of finite codimension of the enveloping centre with the
following property. Let `u ∈ M`, let `κ'` be a smooth compactly supported kernel on the
archimedean group and let `y` assign to each enveloping element a vector of `M`, additively and
complex-linearly. Suppose `y 1` is the smoothing of `u` by `κ'`, and the orbit of each `y a`
along each real exponential curve has derivative `y (X a)` at zero. Then `y` vanishes on the
ideal. -/
theorem exists_ideal_smoothingFamily_eq_zero
    (hR : IsContinuousRepresentation (ρ.comp ι))
    (hnorm : ∀ g : 𝒢, ∃ b : (ArchimedeanMatrix F n)ˣ, ∀ a,
      ρ g * ρ (ι a) = ρ (ι (b * a * b⁻¹)) * ρ g)
    (hU : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (M : Submodule ℂ E) (hMc : IsClosed (M : Set E)) (hMinv : ∀ g, ∀ x ∈ M, ρ g x ∈ M)
    (hMne : M ≠ ⊥)
    (hMmin : ∀ W : Submodule ℂ E, W ≤ M → IsClosed (W : Set E) →
      (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = M) :
    ∃ J : Ideal (EnvelopingCenter F n),
      Module.Finite ℂ (EnvelopingCenter F n ⧸ J.restrictScalars ℂ) ∧
      ∀ u ∈ M, ∀ κ' : (ArchimedeanMatrix F n)ˣ → ℂ,
        ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n) 𝓘(ℝ, ℂ) ∞ κ' → HasCompactSupport κ' →
        ∀ y : EnvelopingAlgebra F n → E, (∀ a, y a ∈ M) →
          y 1 = (∫ g, κ' g⁻¹ • ρ (ι g) u ∂μ) →
          (∀ a b, y (a + b) = y a + y b) → (∀ (c : ℂ) a, y (c • a) = c • y a) →
          (∀ X a, HasDerivAt
            (fun t : ℝ => ρ (ι (archimedeanGLCoordinates F n (realLieExponentialCurve F n X t)))
              (y a))
            (y (envelopingGenerator F n (complexify F n X) * a)) 0) →
          ∀ z ∈ J, y (centerInclusion F n z) = 0 := by
  have hMinv' : ∀ g (x : M), ρ g x ∈ M := fun g x => hMinv g x x.property
  have : CompleteSpace M := hMc.completeSpace_coe
  let π := invariantSubmoduleRepresentation ρ M hMinv'
  let R := π.comp ι
  have hRc : IsContinuousRepresentation R :=
    isContinuousRepresentation_invariantSubmodule (ρ.comp ι) M (fun g x => hMinv' (ι g) x) hR
  have hUπ : ∀ g (x y : M), inner ℂ (π g x) (π g y) = inner ℂ x y :=
    inner_invariantSubmoduleRepresentation ρ M hMinv' hU
  have hnormπ : ∀ g : 𝒢, ∃ b : (ArchimedeanMatrix F n)ˣ, ∀ a, π g * R a = R (b * a * b⁻¹) * π g := by
    intro g
    obtain ⟨b, hb⟩ := hnorm g
    refine ⟨b, fun a => ?_⟩
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change (ρ g * ρ (ι a)) x = (ρ (ι (b * a * b⁻¹)) * ρ g) x
    rw [hb]
  have hirr : IsTopologicallyIrreducible π := by
    refine ⟨Submodule.nontrivial_iff_ne_bot.mpr hMne, fun W hW hWinv => ?_⟩
    let W' : Submodule ℂ E := W.map M.subtype
    have hW'le : W' ≤ M := by
      rintro _ ⟨x, -, rfl⟩
      exact x.property
    have hW'c : IsClosed (W' : Set E) := by
      rw [Submodule.map_coe]
      exact hMc.isClosedEmbedding_subtypeVal.isClosedMap _ hW
    have hW'inv : ∀ g, ∀ x ∈ W', ρ g x ∈ W' := by
      rintro g _ ⟨x, hx, rfl⟩
      exact ⟨π g x, hWinv g x hx, rfl⟩
    rcases hMmin W' hW'le hW'c hW'inv with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      have hx' : (x : E) ∈ W' := ⟨x, hx, rfl⟩
      rw [h, Submodule.mem_bot] at hx'
      rw [Submodule.mem_bot]
      exact Subtype.ext hx'
    · right
      rw [eq_top_iff]
      intro x _
      have hx' : (x : E) ∈ W' := by rw [h]; exact x.property
      obtain ⟨w, hw, hwx⟩ := hx'
      rw [← Subtype.ext hwx]
      exact hw
  obtain ⟨J, hJ, hJv⟩ := exists_ideal_hilbertCenterAction F n R π ι μ hRc (fun _ => rfl) hnormπ
    hUπ hirr
  refine ⟨J, hJ, ?_⟩
  intro u hu κ' hκ' hκ'c y hyM h1 hadd hsmul hder z hz
  let uM : M := ⟨u, hu⟩
  have hw : Langlands.Archimedean.IsSmoothVector I R (smoothedVector R μ κ' uM) :=
    isSmoothVector_smoothedVector R μ hRc hκ' hκ'c uM
  let vD : DerivativeSmoothVectors I R := (toSmooth I R).symm ⟨smoothedVector R μ κ' uM, hw⟩
  let yM : EnvelopingAlgebra F n → M := fun a => ⟨y a, hyM a⟩
  have hint : MeasureTheory.Integrable (fun g : (ArchimedeanMatrix F n)ˣ => κ' g⁻¹ • R g uM) μ := by
    have hcont : Continuous (fun g : (ArchimedeanMatrix F n)ˣ => κ' g⁻¹ • R g uM) :=
      (hκ'.continuous.comp continuous_inv).smul (hRc.comp (continuous_id.prodMk continuous_const))
    exact hcont.integrable_of_hasCompactSupport
      ((hκ'c.comp_homeomorph (Homeomorph.inv _)).smul_right)
  have hyM1 : yM 1 = hilbertSmoothValue F n R vD := by
    apply Subtype.ext
    change y 1 = M.subtypeL (∫ g, κ' g⁻¹ • R g uM ∂μ)
    rw [h1, ← M.subtypeL.integral_comp_comm hint]
    rfl
  have hyMadd (a b : EnvelopingAlgebra F n) : yM (a + b) = yM a + yM b :=
    Subtype.ext (hadd a b)
  have hyMsmul (c : ℂ) (a : EnvelopingAlgebra F n) : yM (c • a) = c • yM a :=
    Subtype.ext (hsmul c a)
  have hyMder (X : RealLieAlgebra F n) (a : EnvelopingAlgebra F n) :
      HasDerivAt (fun t : ℝ => R (archimedeanGLCoordinates F n (realLieExponentialCurve F n X t))
        (yM a)) (yM (envelopingGenerator F n (complexify F n X) * a)) 0 :=
    HasDerivAt.of_isometry (M.subtypeL.restrictScalars ℝ) isometry_subtype_coe (hder X a)
  have key := eq_hilbertEnvelopingAction_of_hasDerivAt F n R hRc vD yM hyM1 hyMadd hyMsmul hyMder
    (centerInclusion F n z)
  have hzero : hilbertEnvelopingAction F n R hRc (centerInclusion F n z) vD = 0 := hJv z hz vD
  rw [hzero, map_zero] at key
  exact congrArg Subtype.val key

end Ambient

end Langlands.Global.ArchimedeanGL
