import Langlands.GroupScheme.Rational.TorusUnipotence.CotangentBasis
import Langlands.GroupScheme.Rational.TorusUnipotence.Truncation
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! # Truncated polynomial sections of formally smooth augmented algebras -/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.TorusUnipotence

open MvPolynomial DirectSum

/-- The image of the ideal of the variables in a truncated polynomial ring. -/
abbrev truncVarIdeal (σ : Type w) (k : Type u) [CommRing k] (N : ℕ) :
    Ideal (MvPolynomial σ k ⧸ idealOfVars σ k ^ N) :=
  (idealOfVars σ k).map (Ideal.Quotient.mk _)

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] {ε : A →ₐ[k] k}
  {σ : Type w}

section Approximation

variable (z : σ → A)

/-- Evaluation at augmentation-ideal elements followed by the augmentation is the constant
coefficient. -/
theorem augmentation_aeval (hz : ∀ s, ε (z s) = 0) (p : MvPolynomial σ k) :
    ε (aeval z p) = constantCoeff p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p s hp => simp [hp, hz]

variable (b : Module.Basis σ k (RingHom.ker ε).Cotangent)

/-- Every augmentation-ideal element agrees with a linear combination of the `z s` modulo the
square of the augmentation ideal. -/
theorem exists_sub_aeval_mem_sq (hz : ∀ s, ε (z s) = 0)
    (hzb : ∀ s, cotangentMap ε (z s) = b s) {x : A} (hx : x ∈ RingHom.ker ε) :
    ∃ q : MvPolynomial σ k, x - aeval z q ∈ RingHom.ker ε ^ 2 := by
  set c := b.repr (cotangentMap ε x)
  refine ⟨Finsupp.linearCombination k (X : σ → MvPolynomial σ k) c, ?_⟩
  have hφ : aeval z (Finsupp.linearCombination k (X : σ → MvPolynomial σ k) c) =
      Finsupp.linearCombination k z c := by
    rw [← AlgHom.toLinearMap_apply, Finsupp.apply_linearCombination]
    have h : (⇑(aeval z : MvPolynomial σ k →ₐ[k] A).toLinearMap ∘
        (X : σ → MvPolynomial σ k)) = z := funext fun s => by simp
    rw [h]
  have hmem : Finsupp.linearCombination k z c ∈ RingHom.ker ε := by
    rw [RingHom.mem_ker]
    change ε.toLinearMap (Finsupp.linearCombination k z c) = 0
    rw [Finsupp.apply_linearCombination]
    have : (ε.toLinearMap ∘ z) = 0 := funext fun s => by simp [hz]
    rw [this]
    simp
  have hcot : cotangentMap ε (Finsupp.linearCombination k z c) = cotangentMap ε x := by
    rw [Finsupp.apply_linearCombination]
    have : (cotangentMap ε ∘ z) = b := funext hzb
    rw [this, b.linearCombination_repr]
  rw [hφ]
  have hsub : x - Finsupp.linearCombination k z c ∈ RingHom.ker ε := Ideal.sub_mem _ hx hmem
  rw [← cotangentMap_eq_zero_iff ε hsub, map_sub, hcot, sub_self]

/-- Successive approximation of elements of `I ^ m` modulo `I ^ (m + 1)`. -/
theorem exists_sub_aeval_mem_pow_succ (hz : ∀ s, ε (z s) = 0)
    (hzb : ∀ s, cotangentMap ε (z s) = b s) (m : ℕ) {x : A} (hx : x ∈ RingHom.ker ε ^ m) :
    ∃ q : MvPolynomial σ k, x - aeval z q ∈ RingHom.ker ε ^ (m + 1) := by
  induction m generalizing x with
  | zero =>
    refine ⟨C (ε x), ?_⟩
    rw [zero_add, pow_one, aeval_C, RingHom.mem_ker, map_sub, AlgHom.commutes,
      Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  | succ m ih =>
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha c hc
      obtain ⟨q₁, hq₁⟩ := ih ha
      obtain ⟨q₂, hq₂⟩ := exists_sub_aeval_mem_sq z b hz hzb hc
      refine ⟨q₁ * q₂, ?_⟩
      have hφ₁ : aeval z q₁ ∈ RingHom.ker ε ^ m := by
        have : aeval z q₁ = a - (a - aeval z q₁) := by ring
        rw [this]
        exact Ideal.sub_mem _ ha (Ideal.pow_le_pow_right (Nat.le_succ m) hq₁)
      have : a * c - aeval z (q₁ * q₂) =
          (a - aeval z q₁) * c + aeval z q₁ * (c - aeval z q₂) := by
        rw [map_mul]
        ring
      rw [this]
      refine Ideal.add_mem _ ?_ ?_
      · have := Ideal.mul_mem_mul hq₁ hc
        rwa [← pow_succ] at this
      · have h2 : m + 1 + 1 = m + 2 := rfl
        rw [h2, pow_add]
        exact Ideal.mul_mem_mul hφ₁ hq₂
    · rintro x y ⟨q₁, hq₁⟩ ⟨q₂, hq₂⟩
      refine ⟨q₁ + q₂, ?_⟩
      have : x + y - aeval z (q₁ + q₂) = (x - aeval z q₁) + (y - aeval z q₂) := by
        rw [map_add]
        ring
      rw [this]
      exact Ideal.add_mem _ hq₁ hq₂

/-- Every element agrees with a polynomial in the `z s` modulo any power of the augmentation
ideal. -/
theorem exists_sub_aeval_mem_pow (hz : ∀ s, ε (z s) = 0)
    (hzb : ∀ s, cotangentMap ε (z s) = b s) (x : A) (n : ℕ) :
    ∃ p : MvPolynomial σ k, x - aeval z p ∈ RingHom.ker ε ^ n := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨q, hq⟩ := exists_sub_aeval_mem_pow_succ z b hz hzb n hp
    exact ⟨p + q, by rwa [map_add, ← sub_sub]⟩

/-- An algebra map into a truncated polynomial ring sending the augmentation ideal into the
variable ideal kills the corresponding power of the augmentation ideal. -/
theorem map_eq_zero_of_mem_pow {N : ℕ} (Ψ : A →ₐ[k] MvPolynomial σ k ⧸ idealOfVars σ k ^ N)
    (hΨI : ∀ a ∈ RingHom.ker ε, Ψ a ∈ truncVarIdeal σ k N) {a : A}
    (ha : a ∈ RingHom.ker ε ^ N) : Ψ a = 0 := by
  have h1 : Ψ a ∈ (RingHom.ker ε ^ N).map Ψ := Ideal.mem_map_of_mem _ ha
  rw [Ideal.map_pow] at h1
  have h2 : (RingHom.ker ε).map Ψ ^ N ≤ truncVarIdeal σ k N ^ N :=
    Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hΨI) N
  have h3 := h2 h1
  rw [truncVarIdeal, ← Ideal.map_pow, Ideal.map_quotient_self] at h3
  exact Ideal.mem_bot.1 h3

/-- The variable ideal maps into the augmentation ideal under evaluation at the `z s`. -/
theorem idealOfVars_pow_le_comap (hz : ∀ s, ε (z s) = 0) (N : ℕ) :
    idealOfVars σ k ^ N ≤ (RingHom.ker ε ^ N).comap (aeval z) := by
  have hvars : idealOfVars σ k ≤ (RingHom.ker ε).comap (aeval z) := by
    rw [idealOfVars, Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    simp [RingHom.mem_ker, hz]
  exact (Ideal.pow_right_mono hvars N).trans (Ideal.le_comap_pow _ N)

/-- An algebra map into a truncated polynomial ring which is the identity on the `z s` modulo
the square of the variable ideal, and which sends the augmentation ideal into the variable
ideal, has kernel contained in the corresponding power of the augmentation ideal. -/
theorem mem_pow_of_map_eq_zero (hz : ∀ s, ε (z s) = 0)
    (hzb : ∀ s, cotangentMap ε (z s) = b s) {N : ℕ}
    (Ψ : A →ₐ[k] MvPolynomial σ k ⧸ idealOfVars σ k ^ N)
    (hΨz : ∀ s, Ψ (z s) - Ideal.Quotient.mk _ (X s) ∈ truncVarIdeal σ k N ^ 2)
    (hΨI : ∀ a ∈ RingHom.ker ε, Ψ a ∈ truncVarIdeal σ k N) {a : A} (ha : Ψ a = 0) :
    a ∈ RingHom.ker ε ^ N := by
  obtain ⟨p, hp⟩ := exists_sub_aeval_mem_pow z b hz hzb a N
  have hΨp : (Ψ.comp (aeval z)) p = 0 := by
    have h := map_eq_zero_of_mem_pow Ψ hΨI hp
    rw [map_sub, ha, zero_sub, neg_eq_zero] at h
    simpa using h
  have hpN : p ∈ idealOfVars σ k ^ N :=
    mem_pow_of_eq_zero (Ψ.comp (aeval z)) (fun s => by simpa using hΨz s) hΨp
  have : a = (a - aeval z p) + aeval z p := by ring
  rw [this]
  exact Ideal.add_mem _ hp (idealOfVars_pow_le_comap z hz N hpN)

end Approximation

section Lift

/-- Formal smoothness lifts a first-order deformation of the augmentation through a nilpotent
ideal. -/
theorem exists_lift_of_cotangent [Algebra.FormallySmooth k A] {B : Type*} [CommRing B]
    [Algebra k B] (J : Ideal B) (hJ : IsNilpotent J)
    (L : (RingHom.ker ε).Cotangent →ₗ[k] B ⧸ J ^ 2)
    (hL : ∀ t, L t ∈ J.map (Ideal.Quotient.mk (J ^ 2))) :
    ∃ ψ : A →ₐ[k] B, ∀ a, Ideal.Quotient.mk (J ^ 2) (ψ a) =
      algebraMap k (B ⧸ J ^ 2) (ε a) + L (cotangentMap ε a) := by
  have hLL : ∀ t t', L t * L t' = 0 := by
    intro t t'
    have h := Ideal.mul_mem_mul (hL t) (hL t')
    rw [← Ideal.map_mul, ← pow_two, Ideal.map_quotient_self] at h
    exact Ideal.mem_bot.1 h
  have h1 : cotangentMap ε 1 = 0 := by simpa using cotangentMap_algebraMap ε 1
  let f : A →ₗ[k] B ⧸ J ^ 2 :=
    (Algebra.linearMap k _).comp ε.toLinearMap + L.comp (cotangentMap ε)
  have hf : ∀ a, f a = algebraMap k _ (ε a) + L (cotangentMap ε a) := fun a => rfl
  let ψ₁ : A →ₐ[k] B ⧸ J ^ 2 :=
    AlgHom.ofLinearMap f (by rw [hf, map_one, map_one, h1, map_zero, add_zero]) (by
      intro x y
      rw [hf, hf, hf, map_mul, cotangentMap_mul, map_add, map_smul, map_smul, map_mul,
        Algebra.smul_def, Algebra.smul_def]
      linear_combination -(hLL (cotangentMap ε x) (cotangentMap ε y)))
  have hnil : IsNilpotent (J ^ 2) := by
    obtain ⟨n, hn⟩ := hJ
    exact ⟨n, by rw [← pow_mul, mul_comm, pow_mul, hn, zero_pow two_ne_zero]⟩
  exact ⟨Algebra.FormallySmooth.lift (J ^ 2) hnil ψ₁, fun a => by
    rw [Algebra.FormallySmooth.mk_lift]
    rfl⟩

/-- The variable ideal of a truncated polynomial ring is nilpotent. -/
theorem truncVarIdeal_pow (N : ℕ) : truncVarIdeal σ k N ^ N = ⊥ := by
  rw [truncVarIdeal, ← Ideal.map_pow, Ideal.map_quotient_self]

variable (z : σ → A) (b : Module.Basis σ k (RingHom.ker ε).Cotangent)

/-- Formal smoothness gives an algebra map to each truncated polynomial ring which is the
identity on the `z s` modulo the square of the variable ideal. -/
theorem exists_truncated_lift [Algebra.FormallySmooth k A] (hz : ∀ s, ε (z s) = 0)
    (hzb : ∀ s, cotangentMap ε (z s) = b s) (N : ℕ) :
    ∃ ψ : A →ₐ[k] MvPolynomial σ k ⧸ idealOfVars σ k ^ N,
      (∀ s, ψ (z s) - Ideal.Quotient.mk _ (X s) ∈ truncVarIdeal σ k N ^ 2) ∧
      ∀ a ∈ RingHom.ker ε, ψ a ∈ truncVarIdeal σ k N := by
  classical
  let J := truncVarIdeal σ k N
  let L : (RingHom.ker ε).Cotangent →ₗ[k] (MvPolynomial σ k ⧸ idealOfVars σ k ^ N) ⧸ J ^ 2 :=
    b.constr k fun s => Ideal.Quotient.mk (J ^ 2) (Ideal.Quotient.mk _ (X s))
  have hLmem : ∀ t, L t ∈ J.map (Ideal.Quotient.mk (J ^ 2)) := by
    intro t
    rw [Module.Basis.constr_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun s _ => ?_
    rw [Algebra.smul_def]
    refine Ideal.mul_mem_left _ _ ?_
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨s, rfl⟩))
  have hJ : IsNilpotent J := ⟨N, by rw [truncVarIdeal_pow, Ideal.zero_eq_bot]⟩
  obtain ⟨ψ, hψ⟩ := exists_lift_of_cotangent (ε := ε) J hJ L hLmem
  refine ⟨ψ, fun s => ?_, fun a ha => ?_⟩
  · rw [← Ideal.Quotient.eq, hψ, hz s, map_zero, zero_add, hzb, Module.Basis.constr_basis]
  · have ha' : ε a = 0 := ha
    have hmem : Ideal.Quotient.mk (J ^ 2) (ψ a) ∈ J.map (Ideal.Quotient.mk (J ^ 2)) := by
      rw [hψ, ha', map_zero, zero_add]
      exact hLmem _
    exact (Ideal.mem_quotient_iff_mem (Ideal.pow_le_self two_ne_zero)).1 hmem

/-- Evaluation at the `z s` as a map from a truncated polynomial ring to the quotient by the
corresponding power of the augmentation ideal. -/
def truncEval (hz : ∀ s, ε (z s) = 0) (N : ℕ) :
    (MvPolynomial σ k ⧸ idealOfVars σ k ^ N) →ₐ[k] A ⧸ RingHom.ker ε ^ N :=
  Ideal.Quotient.liftₐ (idealOfVars σ k ^ N)
    ((Ideal.Quotient.mkₐ k (RingHom.ker ε ^ N)).comp (aeval z)) fun a ha => by
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact idealOfVars_pow_le_comap z hz N ha

theorem truncEval_mk (hz : ∀ s, ε (z s) = 0) (N : ℕ) (p : MvPolynomial σ k) :
    truncEval z hz N (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (aeval z p) :=
  rfl

/-- Evaluation at the `z s` induces a surjection from each truncated polynomial ring onto the
corresponding quotient by a power of the augmentation ideal. -/
theorem quotientMap_aeval_surjective (hz : ∀ s, ε (z s) = 0)
    (hzb : ∀ s, cotangentMap ε (z s) = b s) (N : ℕ) :
    Function.Surjective (truncEval z hz N) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨p, hp⟩ := exists_sub_aeval_mem_pow z b hz hzb x N
  refine ⟨Ideal.Quotient.mk _ p, ?_⟩
  rw [truncEval_mk, Ideal.Quotient.eq, ← neg_mem_iff, neg_sub]
  exact hp

/-- For a formally smooth augmented algebra, the map induced by evaluation at the `z s` from
each truncated polynomial ring is injective. -/
theorem quotientMap_aeval_injective [Algebra.FormallySmooth k A] (hz : ∀ s, ε (z s) = 0)
    (hzb : ∀ s, cotangentMap ε (z s) = b s) (N : ℕ) :
    Function.Injective (truncEval z hz N) := by
  obtain ⟨ψ, hψz, hψI⟩ := exists_truncated_lift z b hz hzb N
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [truncEval_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
  rw [Ideal.Quotient.eq_zero_iff_mem]
  refine mem_pow_of_eq_zero (ψ.comp (aeval z)) (fun s => ?_) ?_
  · rw [AlgHom.comp_apply, aeval_X]
    exact hψz s
  · rw [AlgHom.comp_apply]
    exact map_eq_zero_of_mem_pow ψ hψI hx

/-- For a formally smooth augmented algebra, evaluation at the `z s` identifies each truncated
polynomial ring with the corresponding quotient by a power of the augmentation ideal; the
inverse gives a section characterized by polynomial approximations. -/
theorem exists_truncated_section [Algebra.FormallySmooth k A] (hz : ∀ s, ε (z s) = 0)
    (hzb : ∀ s, cotangentMap ε (z s) = b s) (N : ℕ) :
    ∃ τ : A →ₐ[k] MvPolynomial σ k ⧸ idealOfVars σ k ^ N,
      ∀ (x : A) (p : MvPolynomial σ k), x - aeval z p ∈ RingHom.ker ε ^ N →
        τ x = Ideal.Quotient.mk _ p := by
  have hbij : Function.Bijective (truncEval z hz N) :=
    ⟨quotientMap_aeval_injective z b hz hzb N, quotientMap_aeval_surjective z b hz hzb N⟩
  refine ⟨(AlgEquiv.ofBijective _ hbij).symm.toAlgHom.comp
    (Ideal.Quotient.mkₐ k (RingHom.ker ε ^ N)), fun x p hxp => ?_⟩
  change (AlgEquiv.ofBijective _ hbij).symm (Ideal.Quotient.mkₐ k _ x) = _
  rw [AlgEquiv.symm_apply_eq, AlgEquiv.ofBijective_apply, Ideal.Quotient.mkₐ_eq_mk,
    truncEval_mk, Ideal.Quotient.eq]
  exact hxp

end Lift

section Graded

variable {ι : Type*} [DecidableEq ι] [AddCommMonoid ι] (𝒜 : ι → Submodule k A)
  [GradedAlgebra 𝒜] (z : σ → A) {w : σ → ι}

/-- Evaluation at homogeneous elements sends weighted-homogeneous polynomials to homogeneous
elements of the same degree. -/
theorem aeval_mem_of_isWeightedHomogeneous (hzw : ∀ s, z s ∈ 𝒜 (w s))
    {p : MvPolynomial σ k} {d : ι} (hp : IsWeightedHomogeneous w p d) : aeval z p ∈ 𝒜 d := by
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [aeval_monomial, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have hd : Finsupp.weight w m = d := hp (mem_support_iff.1 hm)
  rw [← hd, Finsupp.weight_apply, Finsupp.prod, Finsupp.sum]
  exact SetLike.prod_pow_mem_graded 𝒜 w z _ fun s _ => hzw s

/-- The homogeneous components of an evaluation are evaluations of weighted-homogeneous
components. -/
theorem decompose_aeval (hzw : ∀ s, z s ∈ 𝒜 (w s)) (p : MvPolynomial σ k) (d : ι) :
    (decompose 𝒜 (aeval z p) d : A) = aeval z (weightedHomogeneousComponent w d p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial m c =>
    have hm : IsWeightedHomogeneous w (monomial m c) (Finsupp.weight w m) :=
      isWeightedHomogeneous_monomial w m c rfl
    have hmem := aeval_mem_of_isWeightedHomogeneous 𝒜 z hzw hm
    by_cases h : Finsupp.weight w m = d
    · rw [← h, decompose_of_mem_same 𝒜 hmem, hm.weightedHomogeneousComponent_same]
    · rw [decompose_of_mem_ne 𝒜 hmem h, hm.weightedHomogeneousComponent_ne d (Ne.symm h),
        map_zero]
  | add p q hp hq =>
    rw [map_add, decompose_add, DirectSum.add_apply, Submodule.coe_add, hp, hq, map_add, map_add]

variable (ε) in
/-- The kernel of a graded augmentation is homogeneous. -/
theorem augIdeal_isHomogeneous (hε : ∀ i : ι, i ≠ 0 → ∀ a ∈ 𝒜 i, ε a = 0) :
    (RingHom.ker ε).IsHomogeneous 𝒜 := by
  intro i a ha
  by_cases hi : i = 0
  · subst hi
    have h : ε a = 0 := ha
    change ε _ = 0
    rw [augmentation_decompose_zero 𝒜 ε hε, h]
  · exact hε i hi _ (decompose 𝒜 a i).2

variable (ε) in
/-- The powers of the kernel of a graded augmentation are homogeneous. -/
theorem augIdeal_pow_isHomogeneous (hε : ∀ i : ι, i ≠ 0 → ∀ a ∈ 𝒜 i, ε a = 0) (n : ℕ) :
    (RingHom.ker ε ^ n).IsHomogeneous 𝒜 := by
  induction n with
  | zero =>
    intro i a _
    simp
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul (augIdeal_isHomogeneous ε 𝒜 hε)

/-- A section characterized by polynomial approximations sends homogeneous elements to classes
of weighted-homogeneous polynomials of the same degree, with constant coefficient the
augmentation. -/
theorem exists_isWeightedHomogeneous_of_section (b : Module.Basis σ k (RingHom.ker ε).Cotangent)
    (hε : ∀ i : ι, i ≠ 0 → ∀ a ∈ 𝒜 i, ε a = 0) (hzw : ∀ s, z s ∈ 𝒜 (w s))
    (hz : ∀ s, ε (z s) = 0) (hzb : ∀ s, cotangentMap ε (z s) = b s) {N : ℕ} (hN : N ≠ 0)
    (τ : A →ₐ[k] MvPolynomial σ k ⧸ idealOfVars σ k ^ N)
    (hτ : ∀ (x : A) (p : MvPolynomial σ k), x - aeval z p ∈ RingHom.ker ε ^ N →
      τ x = Ideal.Quotient.mk _ p) {d : ι} {a : A} (ha : a ∈ 𝒜 d) :
    ∃ p : MvPolynomial σ k, IsWeightedHomogeneous w p d ∧ constantCoeff p = ε a ∧
      τ a = Ideal.Quotient.mk _ p := by
  obtain ⟨p, hp⟩ := exists_sub_aeval_mem_pow z b hz hzb a N
  have hd : a - aeval z (weightedHomogeneousComponent w d p) ∈ RingHom.ker ε ^ N := by
    have := (augIdeal_pow_isHomogeneous ε 𝒜 hε N) d hp
    rwa [decompose_sub, DirectSum.sub_apply, Submodule.coe_sub, decompose_of_mem_same 𝒜 ha,
      decompose_aeval 𝒜 z hzw] at this
  refine ⟨weightedHomogeneousComponent w d p,
    weightedHomogeneousComponent_isWeightedHomogeneous _ _, ?_, hτ _ _ hd⟩
  have h1 : a - aeval z (weightedHomogeneousComponent w d p) ∈ RingHom.ker ε :=
    Ideal.pow_le_self hN hd
  rw [RingHom.mem_ker, map_sub, augmentation_aeval z hz, sub_eq_zero] at h1
  exact h1.symm

end Graded

end Langlands.GroupScheme.TorusUnipotence
