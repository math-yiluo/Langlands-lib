import Langlands.Representation.Compact.SchurOrthogonalityCore
import Langlands.Representation.Twist.UnitaryModCenterProof
import Langlands.Representation.Unitary.Twist
import Langlands.Representation.Plancherel.CoefficientTensors
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Vandermonde

noncomputable section

open MeasureTheory
open scoped ComplexConjugate TensorProduct Topology

namespace Langlands.Renard.CompactRepresentation

open Langlands.HarishChandraSchwartz Langlands.Plancherel

universe u v

variable {G : Type u} [Group G]

/-- A smooth real additive character gives a unitary phase character. -/
def schurPhase (a : G →* Multiplicative ℝ) (t : ℝ) : G →* ℂˣ where
  toFun g := Units.mk0 (Complex.exp ((t * Multiplicative.toAdd (a g) : ℝ) * Complex.I))
    (Complex.exp_ne_zero _)
  map_one' := by apply Units.ext; simp
  map_mul' g h := by
    apply Units.ext
    change Complex.exp _ = Complex.exp _ * Complex.exp _
    rw [← Complex.exp_add]
    congr 1
    rw [map_mul]
    change ((t * (Multiplicative.toAdd (a g) + Multiplicative.toAdd (a h)) : ℝ) : ℂ) *
      Complex.I = _
    push_cast
    ring

@[simp]
theorem schurPhase_val (a : G →* Multiplicative ℝ) (t : ℝ) (g : G) :
    (schurPhase a t g : ℂ) = Complex.exp ((t * Multiplicative.toAdd (a g) : ℝ) * Complex.I) := rfl

@[simp]
theorem schurPhase_norm (a : G →* Multiplicative ℝ) (t : ℝ) (g : G) :
    ‖(schurPhase a t g : ℂ)‖ = 1 := by
  simp [schurPhase_val, Complex.norm_exp]

@[simp]
theorem schurPhase_zero (a : G →* Multiplicative ℝ) (g : G) : schurPhase a 0 g = 1 := by
  apply Units.ext
  simp

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem schurPhase_isOpen_ker (a : G →* Multiplicative ℝ)
    (ha : IsOpen (a.ker : Set G)) (t : ℝ) : IsOpen ((schurPhase a t).ker : Set G) := by
  refine Subgroup.isOpen_mono (H₁ := a.ker) ?_ ha
  intro g hg
  change schurPhase a t g = 1
  apply Units.ext
  have he : a g = 1 := hg
  simp [schurPhase_val, he]

section Local

variable [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
  (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
  {V : Type v} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

include hcof in
/-- Near the trivial phase, the Schur integral produces a nonzero intertwiner. -/
theorem eventually_nonempty_phaseEquiv
    (hsq : IsSquareIntegrableModCenter ρ μ) (hi : ρ.IsIrreducible)
    (b : InvariantPositiveForm ρ) (a : G →* Multiplicative ℝ)
    (ha : IsOpen (a.ker : Set G)) (haZ : ∀ z : Subgroup.center G, a z = 1) :
    ∀ᶠ t : ℝ in 𝓝 0, Nonempty (ρ.Equiv (Langlands.twist (schurPhase a t) ρ)) := by
  classical
  obtain ⟨c, hc⟩ := hsq.2
  have hsqA := (squareIntegrableModCenter_iff_fullCenter μ).mp hsq
  have hint := integrable_orthogonality_of_positiveForm (Subgroup.center G) le_rfl
    μ c.acts c.acts hcof hsqA hsqA b
  have hτ (t : ℝ) (z : Subgroup.center G) (x : V) :
      Langlands.twist (schurPhase a t) ρ z x = (c.character z : ℂ) • x := by
    change (schurPhase a t z : ℂ) • ρ z x = _
    simp [schurPhase_val, haZ, c.acts]
  let ht (t : ℝ) := schurPhase_isOpen_ker a ha t
  have hsqτ (t : ℝ) : IsSquareIntegrableModCenter (Langlands.twist (schurPhase a t) ρ) μ :=
    isSquareIntegrableModCenter_unitaryTwist _ (ht t) (schurPhase_norm a t) μ hsq
  have hτint (t : ℝ) := integrable_orthogonality_of_positiveForm (Subgroup.center G)
    le_rfl μ c.acts (hτ t) hcof hsqA
    ((squareIntegrableModCenter_iff_fullCenter μ).mp (hsqτ t))
    (b.twist (schurPhase a t) (schurPhase_norm a t))
  have hnt : Nontrivial V := by
    have := hi
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let ℓ := b.toSmoothDual hsq.1.1 v
  let ℓt (t : ℝ) : SmoothDual (Langlands.twist (schurPhase a t) ρ) :=
    (smoothContragredientTwistEquiv (schurPhase a t) ρ (ht t)).symm ℓ
  let F (t : ℝ) := orthogonalityIntegrand (Subgroup.center G) c.acts (hτ t)
    v ℓ.val v (ℓt t).val
  let F₀ := orthogonalityIntegrand (Subgroup.center G) c.acts c.acts v ℓ.val v ℓ.val
  have hF (t : ℝ) (g : G) : F t (QuotientGroup.mk g) =
      (schurPhase a t g⁻¹ : ℂ) * F₀ (QuotientGroup.mk g) := by
    change ℓ.val (ρ g v) * ℓ.val ((schurPhase a t g⁻¹ : ℂ) • ρ g⁻¹ v) =
      (schurPhase a t g⁻¹ : ℂ) * (ℓ.val (ρ g v) * ℓ.val (ρ g⁻¹ v))
    rw [map_smul, smul_eq_mul]
    ring
  have hn (t : ℝ) (q : G ⧸ Subgroup.center G) : ‖F t q‖ = ‖F₀ q‖ := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hF, norm_mul, schurPhase_norm, one_mul]
  have hcont : ContinuousAt (fun t : ℝ => ∫ q, F t q ∂μ) 0 := by
    apply continuousAt_of_dominated
      (Filter.Eventually.of_forall fun t => (hτint t v ℓ v (ℓt t)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall fun q => (hn t q).le)
      (hint v ℓ v ℓ).norm
    apply Filter.Eventually.of_forall
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    change ContinuousAt (fun t : ℝ => F t (QuotientGroup.mk g)) 0
    simp_rw [hF, schurPhase_val]
    fun_prop
  have h0 : (∫ q, F 0 q ∂μ) ≠ 0 := by
    have he : F 0 = F₀ := by
      funext q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      rw [hF, schurPhase_zero, Units.val_one, one_mul]
    rw [he]
    obtain ⟨d, hd, hdeg⟩ := exists_formalDegree_rightInvariant (Subgroup.center G)
      le_rfl μ c.acts hcof hsqA hi b
    change orthogonalityIntegral (Subgroup.center G) μ c.acts c.acts v ℓ v ℓ ≠ 0
    rw [hdeg]
    have hℓ : ℓ.val v ≠ 0 := fun hz => hv (b.definite v hz)
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr hd.ne')) hℓ) hℓ
  filter_upwards [hcont.eventually_ne h0] with t ht0
  obtain ⟨T, hT⟩ := exists_leftSchurIntertwiner_rightInvariant (Subgroup.center G)
    μ c.acts (hτ t) hcof (hτint t) hsq.1 (hsqτ t).1 ℓ v
  have hT0 : T ≠ 0 := by
    intro hzero
    apply ht0
    change orthogonalityIntegral (Subgroup.center G) μ c.acts (hτ t) v ℓ v (ℓt t) = 0
    rw [← hT, hzero]
    exact map_zero _
  have := hi
  have := (isIrreducible_twist_iff (schurPhase a t) ρ).mpr hi
  exact ⟨T.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero T).resolve_right hT0)⟩

end Local

section FixedLevel

variable {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

/-- The actual coefficient map restricted to fixed vector and functional spaces. -/
def schurFixedCoefficientMap (K : OpenSubgroup G) :
    (fixedVectors ρ K.toSubgroup ⊗[ℂ]
      fixedVectors (smoothContragredient ρ) K.toSubgroup) →ₗ[ℂ] (G → ℂ) :=
  TensorProduct.lift
    (LinearMap.mk₂ ℂ (fun v ℓ g => (ℓ.val : SmoothDual ρ).val (ρ g v.val))
      (fun v w ℓ => by ext g; simp)
      (fun z v ℓ => by ext g; simp)
      (fun v ℓ m => by ext g; rfl)
      (fun z v ℓ => by ext g; rfl))

/-- The finite fixed-level coefficient space in the actual function space. -/
def schurFixedCoefficientSpace (K : OpenSubgroup G) : Submodule ℂ (G → ℂ) :=
  (schurFixedCoefficientMap ρ K).range

theorem finite_schurFixedCoefficientSpace
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (hadm : IsAdmissible ρ) (K : OpenSubgroup G) :
    FiniteDimensional ℂ (schurFixedCoefficientSpace ρ K) := by
  let _ : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup) := hadm.2 K
  let _ : FiniteDimensional ℂ (fixedVectors (smoothContragredient ρ) K.toSubgroup) :=
    (isAdmissible_smoothContragredient_of_compact_cofinal hcof ρ hadm).2 K
  exact Module.Finite.range (schurFixedCoefficientMap ρ K)

/-- A self phase twist places the phase-multiplied coefficient in the same fixed level. -/
theorem phase_coefficient_mem_schurFixedCoefficientSpace
    (a : G →* Multiplicative ℝ) (ha : IsOpen (a.ker : Set G)) (t : ℝ)
    (K : OpenSubgroup G) (hKa : K.toSubgroup ≤ a.ker)
    (v : V) (hv : v ∈ fixedVectors ρ K.toSubgroup)
    (ℓ : SmoothDual ρ) (hℓ : ℓ ∈ fixedVectors (smoothContragredient ρ) K.toSubgroup)
    (e : ρ.Equiv (Langlands.twist (schurPhase a t) ρ)) :
    (fun g => (schurPhase a t g : ℂ) * ℓ.val (ρ g v)) ∈ schurFixedCoefficientSpace ρ K := by
  have hp (k : K) : (schurPhase a t k : ℂ) = 1 := by
    have hk : a k = 1 := hKa k.property
    simp [schurPhase_val, hk]
  let w := e.symm v
  have hw : w ∈ fixedVectors ρ K.toSubgroup := by
    intro k
    apply e.injective
    change e.toIntertwiningMap (ρ k w) = e w
    rw [e.toIntertwiningMap.isIntertwining, e.apply_symm_apply]
    change (Langlands.twist (schurPhase a t) ρ) k (e (e.symm v)) = v
    rw [e.apply_symm_apply]
    change (schurPhase a t k : ℂ) • ρ k v = v
    rw [hp k, one_smul]
    exact hv k
  let ℓt : SmoothDual (Langlands.twist (schurPhase a t) ρ) :=
    (smoothContragredientTwistEquiv (schurPhase a t) ρ (schurPhase_isOpen_ker a ha t)).symm ℓ
  let m := contragredientMap e.toIntertwiningMap ℓt
  have hm : m ∈ fixedVectors (smoothContragredient ρ) K.toSubgroup := by
    intro k
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change ℓ.val (e.toIntertwiningMap (ρ (k : G)⁻¹ x)) = ℓ.val (e.toIntertwiningMap x)
    rw [e.toIntertwiningMap.isIntertwining]
    change ℓ.val ((schurPhase a t (k : G)⁻¹ : ℂ) • ρ (k : G)⁻¹ (e x)) = ℓ.val (e x)
    have hpinv : (schurPhase a t (k : G)⁻¹ : ℂ) = 1 := hp k⁻¹
    rw [hpinv, one_smul]
    exact congrArg (fun L : SmoothDual ρ => L.val (e x)) (hℓ k)
  refine ⟨⟨w, hw⟩ ⊗ₜ[ℂ] ⟨m, hm⟩, ?_⟩
  ext g
  change ℓ.val (e.toIntertwiningMap (ρ g w)) = (schurPhase a t g : ℂ) * ℓ.val (ρ g v)
  rw [e.toIntertwiningMap.isIntertwining]
  change ℓ.val ((schurPhase a t g : ℂ) • ρ g (e (e.symm v))) = _
  rw [e.apply_symm_apply, map_smul, smul_eq_mul]

end FixedLevel

/-- A finite-dimensional space cannot contain a local phase orbit with infinitely many
real frequencies on the support. The proof is the finite Vandermonde argument. -/
theorem finite_real_image_support_of_phase_mem {X : Type*}
    (M : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ M] (f : X → ℂ) (a : X → ℝ)
    (hmem : ∀ᶠ t : ℝ in 𝓝 0,
      (fun x => Complex.exp ((t * a x : ℝ) * Complex.I) * f x) ∈ M) :
    (a '' Function.support f).Finite := by
  classical
  by_contra hfin
  have hInf : (a '' Function.support f).Infinite := hfin
  let _ : Infinite (a '' Function.support f) := Set.infinite_coe_iff.mpr hInf
  let n := Module.finrank ℂ M + 1
  let y (i : Fin n) := Infinite.natEmbedding (a '' Function.support f) i.val
  have hxi (i : Fin n) : ∃ x : X, f x ≠ 0 ∧ a x = (y i).val := (y i).property
  choose x hfx hax using hxi
  have hai : Function.Injective (fun i : Fin n => a (x i)) := by
    intro i j hij
    have he : y i = y j := Subtype.ext (by simpa only [← hax] using hij)
    exact Fin.ext ((Infinite.natEmbedding _).injective he)
  have hmemall : ∀ᶠ t : ℝ in 𝓝 0, ∀ j : Fin n,
      (fun x => Complex.exp ((((j.val : ℝ) * t) * a x : ℝ) * Complex.I) * f x) ∈ M := by
    apply Filter.eventually_all.mpr
    intro j
    have ht : ContinuousAt (fun t : ℝ => (j.val : ℝ) * t) 0 := by fun_prop
    have hlim : Filter.Tendsto (fun t : ℝ => (j.val : ℝ) * t) (𝓝 0) (𝓝 0) := by
      simpa using ht.tendsto
    exact hlim.eventually hmem
  have hstrip : ∀ᶠ t : ℝ in 𝓝 0, ∀ i : Fin n, |t * a (x i)| < Real.pi := by
    apply Filter.eventually_all.mpr
    intro i
    have ht : ContinuousAt (fun t : ℝ => |t * a (x i)|) 0 := by fun_prop
    exact ht.eventually_lt continuousAt_const (by simpa using Real.pi_pos)
  obtain ⟨ε, hε, heps⟩ := Metric.eventually_nhds_iff.mp (hmemall.and hstrip)
  let t := ε / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hdist : dist t 0 < ε := by rw [Real.dist_eq, sub_zero, abs_of_pos ht]; dsimp [t]; linarith
  obtain ⟨hm, hs⟩ := heps hdist
  let z (i : Fin n) := Complex.exp ((t * a (x i) : ℝ) * Complex.I)
  have hzi : Function.Injective z := by
    intro i j hij
    have him (k : Fin n) : (((t * a (x k) : ℝ) : ℂ) * Complex.I).im = t * a (x k) := by simp
    have he := Complex.exp_inj_of_neg_pi_lt_of_le_pi
      (by rw [him]; exact (abs_lt.mp (hs i)).1)
      (by rw [him]; exact (abs_lt.mp (hs i)).2.le)
      (by rw [him]; exact (abs_lt.mp (hs j)).1)
      (by rw [him]; exact (abs_lt.mp (hs j)).2.le) hij
    apply hai
    have he' := congrArg Complex.im he
    rw [him, him] at he'
    exact mul_left_cancel₀ ht.ne' he'
  let v (j : Fin n) : M := ⟨_, hm j⟩
  have hv : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hz : c = 0 := Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero hzi (fun i => ?_)
    · exact fun j => congrFun hz j
    have he := congrArg (fun w : M => w.val (x i)) hc
    have heval (j : Fin n) : (v j).val (x i) = z i ^ j.val * f (x i) := by
      change Complex.exp ((((j.val : ℝ) * t) * a (x i) : ℝ) * Complex.I) * f (x i) = _
      rw [show ((((j.val : ℝ) * t) * a (x i) : ℝ) : ℂ) * Complex.I =
        (j.val : ℂ) * (((t * a (x i) : ℝ) : ℂ) * Complex.I) by push_cast; ring,
        Complex.exp_nat_mul]
    have hsum : (∑ j, c j * z i ^ j.val) * f (x i) = 0 := by
      simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
        Pi.smul_apply, smul_eq_mul, heval, Submodule.coe_zero, Pi.zero_apply,
        Finset.sum_mul, mul_assoc] using he
    exact (mul_eq_zero.mp hsum).resolve_right (hfx i)
  have hcard := hv.fintype_card_le_finrank
  simp only [Fintype.card_fin, n] at hcard
  omega

section Support

variable [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
  (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
  {V : Type v} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

include hcof in
/-- A smooth real character trivial on the center has finite image on a smooth
coefficient's support in an irreducible square-integrable representation. -/
theorem finite_real_image_coefficient_support
    (hsq : IsSquareIntegrableModCenter ρ μ) (hi : ρ.IsIrreducible)
    (b : InvariantPositiveForm ρ) (a : G →* Multiplicative ℝ)
    (ha : IsOpen (a.ker : Set G)) (haZ : ∀ z : Subgroup.center G, a z = 1)
    (v : V) (ℓ : SmoothDual ρ) :
    ((fun g => Multiplicative.toAdd (a g)) ''
      Function.support (fun g => ℓ.val (ρ g v))).Finite := by
  obtain ⟨K₁, hv⟩ := hsq.1.1 v
  obtain ⟨K₂, hℓ⟩ := isSmooth_smoothContragredient ρ ℓ
  let K : OpenSubgroup G := K₁ ⊓ K₂ ⊓ ⟨a.ker, ha⟩
  have hKa : K.toSubgroup ≤ a.ker := fun _ hg => hg.2
  have hvK : v ∈ fixedVectors ρ K.toSubgroup :=
    fun k => hv ⟨k.val, k.property.1.1⟩
  have hℓK : ℓ ∈ fixedVectors (smoothContragredient ρ) K.toSubgroup :=
    fun k => hℓ ⟨k.val, k.property.1.2⟩
  let _ := finite_schurFixedCoefficientSpace ρ hcof hsq.1 K
  apply finite_real_image_support_of_phase_mem (schurFixedCoefficientSpace ρ K)
  filter_upwards [eventually_nonempty_phaseEquiv μ hcof hsq hi b a ha haZ] with t ht
  obtain ⟨e⟩ := ht
  exact phase_coefficient_mem_schurFixedCoefficientSpace ρ a ha t K hKa v hvK ℓ hℓK e

end Support

/-- The logarithm of the absolute value of a complex character. -/
def schurLogNorm (η : G →* ℂˣ) : G →* Multiplicative ℝ where
  toFun g := Multiplicative.ofAdd (Real.log ‖(η g : ℂ)‖)
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, Units.val_mul, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr (Units.ne_zero _))
        (norm_ne_zero_iff.mpr (Units.ne_zero _))]
    rfl

theorem schurLogNorm_isOpen_ker (η : G →* ℂˣ) (hη : IsOpen (η.ker : Set G)) :
    IsOpen ((schurLogNorm η).ker : Set G) := by
  refine Subgroup.isOpen_mono (H₁ := η.ker) ?_ hη
  intro g hg
  change schurLogNorm η g = 1
  have he : η g = 1 := hg
  simp [schurLogNorm, he]

section Bound

variable [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
  (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
  {V : Type v} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

include hcof in
/-- A smooth character of modulus one on the center is bounded on the support
of each smooth coefficient of an irreducible square-integrable representation. -/
theorem character_norm_bounded_on_coefficient_support
    (hsq : IsSquareIntegrableModCenter ρ μ) (hi : ρ.IsIrreducible)
    (b : InvariantPositiveForm ρ) (η : G →* ℂˣ)
    (hη : IsOpen (η.ker : Set G))
    (hηZ : ∀ z : Subgroup.center G, ‖(η z : ℂ)‖ = 1)
    (v : V) (ℓ : SmoothDual ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : G, ℓ.val (ρ g v) ≠ 0 → ‖(η g : ℂ)‖ ≤ C := by
  have hfin := finite_real_image_coefficient_support μ hcof hsq hi b (schurLogNorm η)
    (schurLogNorm_isOpen_ker η hη) (fun z => by
      change Multiplicative.ofAdd (Real.log ‖(η z : ℂ)‖) = 1
      simp [hηZ z]) v ℓ
  obtain ⟨r, hr⟩ := hfin.bddAbove
  refine ⟨Real.exp r, Real.exp_pos r, fun g hg => ?_⟩
  have hle : Real.log ‖(η g : ℂ)‖ ≤ r := hr ⟨g, hg, rfl⟩
  have hp : 0 < ‖(η g : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero (η g))
  simpa only [Real.exp_log hp] using Real.exp_le_exp.mpr hle

end Bound

end Langlands.Renard.CompactRepresentation
