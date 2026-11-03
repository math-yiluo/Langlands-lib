import Langlands.Algebra.GradedHopf.Primitive

/-! # Sections of homogeneous coordinates with nonzero differential -/

noncomputable section

open DirectSum TensorProduct MvPolynomial Finsupp

namespace Langlands.Algebra.GradedHopf

section Augmentation

variable {k A σ : Type*} [CommRing k] [CommRing A] [Bialgebra k A]
  {z : σ → A} (hz : Function.Bijective (aeval z : MvPolynomial σ k →ₐ[k] A))
  (hz0 : ∀ i, Coalgebra.counit (R := k) (z i) = 0)
include hz0

/-- When the counit vanishes on the coordinates, it is evaluation at the origin. -/
theorem counit_aeval (F : MvPolynomial σ k) :
    Coalgebra.counit (R := k) (aeval z F) = F.coeff 0 := by
  have h : (Bialgebra.counitAlgHom k A).comp (aeval z) = aeval (0 : σ → k) :=
    MvPolynomial.algHom_ext fun i => by
      rw [AlgHom.comp_apply, aeval_X, aeval_X, Bialgebra.counitAlgHom_apply, hz0 i]
      rfl
  have := congrArg (fun f => f F) h
  simp only [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, aeval_zero] at this
  rw [this]
  rfl

include hz in
theorem coordTangent_eq_coeff [DecidableEq σ] (i : σ) (a : A) :
    coordTangent hz i a = ((coordEquiv hz).symm a).coeff (Finsupp.single i 1) := by
  rw [coordTangent_apply, coordDeriv_apply, coordEquiv, AlgEquiv.coe_ofBijective,
    counit_aeval hz0, coeff_pderiv]
  simp

include hz in
/-- An element of the augmentation ideal killed by all the tangent vectors `ξᵢ` lies in its
square. -/
theorem mem_sq_of_coordTangent_eq_zero [DecidableEq σ] {x : A}
    (hx : Coalgebra.counit (R := k) x = 0) (h : ∀ i, coordTangent hz i x = 0) :
    x ∈ RingHom.ker (Bialgebra.counitAlgHom k A) ^ 2 := by
  set F := (coordEquiv hz).symm x with hF
  have hxF : x = aeval z F := by
    rw [hF]
    exact ((coordEquiv hz).apply_symm_apply x).symm
  have hF0 : F.coeff 0 = 0 := by rw [← counit_aeval hz0, ← hxF, hx]
  have hF1 : ∀ i, F.coeff (Finsupp.single i 1) = 0 := fun i => by
    rw [← coordTangent_eq_coeff hz hz0, h i]
  have hzI : ∀ j, z j ∈ RingHom.ker (Bialgebra.counitAlgHom k A) := fun j => hz0 j
  rw [hxF, F.as_sum, map_sum]
  refine Ideal.sum_mem _ fun m hm => ?_
  have hm0 : m ≠ 0 := fun h' => by
    rw [h'] at hm
    exact (MvPolynomial.mem_support_iff.1 hm) hF0
  obtain ⟨a, ha⟩ : ∃ a, m a ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hm0 (Finsupp.ext h')
  have hle : Finsupp.single a 1 ≤ m := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 ha)
  set m' := m - Finsupp.single a 1 with hm'
  have hm'0 : m' ≠ 0 := fun h' => by
    have : m = Finsupp.single a 1 := by
      rw [← tsub_add_cancel_of_le hle, ← hm', h', zero_add]
    rw [this] at hm
    exact (MvPolynomial.mem_support_iff.1 hm) (hF1 a)
  obtain ⟨b, hb⟩ : ∃ b, m' b ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hm'0 (Finsupp.ext h')
  have hle' : Finsupp.single b 1 ≤ m' := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hb)
  have hdecomp : m = Finsupp.single a 1 + (Finsupp.single b 1 + (m' - Finsupp.single b 1)) := by
    rw [add_tsub_cancel_of_le hle', hm', add_tsub_cancel_of_le hle]
  have hmono : ∀ c : k, monomial m c =
      X a * (X b * monomial (m' - Finsupp.single b 1) c) := fun c => by
    rw [hdecomp]
    simp only [X, monomial_mul_monomial, one_mul]
  rw [hmono, map_mul, map_mul, aeval_X, aeval_X, ← mul_assoc, pow_two]
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul (hzI a) (hzI b))

end Augmentation

section Section

variable {k A σ : Type*} [Field k] [CommRing A] [Bialgebra k A] [DecidableEq σ]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] {w : σ → ℤ} {z : σ → A}

/-- A homogeneous element `g` of nonzero degree in the augmentation ideal but not in its square
admits a `k`-algebra map `s : A → k[X]` with `s g = X`: send one coordinate `zᵢ` with
`ξᵢ(g) = c ≠ 0` to `c⁻¹ X` and the other coordinates to `0`. -/
theorem exists_algHom_polynomial_eq_X (hzw : ∀ i, z i ∈ 𝒜 (w i))
    (hz : Function.Bijective (aeval z : MvPolynomial σ k →ₐ[k] A))
    (hz0 : ∀ i, Coalgebra.counit (R := k) (z i) = 0) {g : A} {d : ℤ} (hd : d ≠ 0)
    (hg : g ∈ 𝒜 d) (hg0 : Coalgebra.counit (R := k) g = 0)
    (hg2 : g ∉ RingHom.ker (Bialgebra.counitAlgHom k A) ^ 2) :
    ∃ s : A →ₐ[k] Polynomial k, s g = Polynomial.X := by
  obtain ⟨i, hi⟩ : ∃ i, coordTangent hz i g ≠ 0 := by
    by_contra h
    push Not at h
    exact hg2 (mem_sq_of_coordTangent_eq_zero hz hz0 hg0 h)
  set e := coordEquiv hz with he
  set F := e.symm g with hF
  have hgF : g = aeval z F := by
    rw [hF]
    exact (e.apply_symm_apply g).symm
  set c := F.coeff (Finsupp.single i 1) with hc
  have hc0 : c ≠ 0 := by rwa [hc, hF, ← coordTangent_eq_coeff hz hz0]
  have hFw : ∀ m ∈ F.support, weight w m = d := by
    intro m hm
    have h1 : aeval z F = aeval z (weightedHomogeneousComponent w d F) := by
      rw [← gradeProj_aeval 𝒜 hzw, ← hgF, gradeProj_of_mem_self 𝒜 hg]
    have h2 := congrArg (fun G : MvPolynomial σ k => G.coeff m) (hz.1 h1)
    classical
    simp only [coeff_weightedHomogeneousComponent] at h2
    by_contra hne
    rw [ite_eq_right_iff.2 (fun h => absurd h hne)] at h2
    exact (MvPolynomial.mem_support_iff.1 hm) h2
  have hwi : w i = d := by
    have := hFw (Finsupp.single i 1) (MvPolynomial.mem_support_iff.2 hc0)
    rwa [weight_single, one_smul] at this
  let y : σ → Polynomial k := fun j => if j = i then Polynomial.C c⁻¹ * Polynomial.X else 0
  refine ⟨(aeval y).comp (e.symm : A →ₐ[k] MvPolynomial σ k), ?_⟩
  rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, ← hF, F.as_sum, map_sum,
    Finset.sum_eq_single (Finsupp.single i 1)]
  · rw [aeval_monomial, Finsupp.prod_single_index (by simp), pow_one, ← hc]
    simp only [y, ite_true, Polynomial.algebraMap_eq, ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ hc0, map_one, one_mul]
  · intro m hm hne
    rw [aeval_monomial]
    by_cases hsupp : ∃ j ∈ m.support, j ≠ i
    · obtain ⟨j, hj, hji⟩ := hsupp
      refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hj ?_)
      simp only [y, hji, ite_false]
      exact zero_pow (Finsupp.mem_support_iff.1 hj)
    · push Not at hsupp
      have hmi : m = Finsupp.single i (m i) :=
        Finsupp.support_subset_singleton.1 fun j hj => Finset.mem_singleton.2 (hsupp j hj)
      have hw := hFw m hm
      rw [hmi, weight_single, hwi, nsmul_eq_mul] at hw
      have h1 : (m i : ℤ) = 1 := by
        have : ((m i : ℤ) - 1) * d = 0 := by rw [sub_mul, hw, one_mul, sub_self]
        rcases mul_eq_zero.1 this with h | h
        · linarith
        · exact absurd h hd
      have : m i = 1 := by exact_mod_cast h1
      exact absurd (hmi.trans (by rw [this])) hne
  · intro h
    rw [MvPolynomial.mem_support_iff, not_not] at h
    rw [h, map_zero, map_zero]

end Section

section Measure

variable (k A : Type*) [CommRing k] [CommRing A] [Bialgebra k A]

/-- The tangent space at the counit: `k`-linear maps `ξ : A → k` with
`ξ (a * b) = ε a * ξ b + ε b * ξ a`. -/
def epsDer : Submodule k (A →ₗ[k] k) where
  carrier := {ξ | ∀ a b, ξ (a * b) = Coalgebra.counit (R := k) a * ξ b +
    Coalgebra.counit (R := k) b * ξ a}
  zero_mem' := by intro a b; simp
  add_mem' := by
    intro ξ η hξ hη a b
    simp only [LinearMap.add_apply, hξ a b, hη a b]
    ring
  smul_mem' := by
    intro c ξ hξ a b
    simp only [LinearMap.smul_apply, hξ a b, smul_eq_mul]
    ring

variable {k A}

theorem epsDer_apply_one {ξ : A →ₗ[k] k} (hξ : ξ ∈ epsDer k A) : ξ 1 = 0 := by
  have h := hξ 1 1
  rw [mul_one, Bialgebra.counit_one, one_mul] at h
  have h' : ξ 1 + ξ 1 = ξ 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h'

theorem epsDer_eq_zero_of_adjoin {ξ : A →ₗ[k] k} (hξ : ξ ∈ epsDer k A) {s : Set A}
    (hs : Algebra.adjoin k s = ⊤) (h : ∀ x ∈ s, ξ x = 0) : ξ = 0 := by
  ext a
  have ha : a ∈ Algebra.adjoin k s := hs ▸ Algebra.mem_top
  rw [LinearMap.zero_apply]
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap c => rw [Algebra.algebraMap_eq_smul_one, map_smul, epsDer_apply_one hξ, smul_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | mul x y _ _ hx hy => rw [hξ x y, hx, hy, mul_zero, mul_zero, add_zero]

theorem coordTangent_mem_epsDer {σ : Type*} [DecidableEq σ] {z : σ → A}
    (hz : Function.Bijective (aeval z : MvPolynomial σ k →ₐ[k] A)) (i : σ) :
    coordTangent hz i ∈ epsDer k A :=
  fun a b => coordTangent_mul hz i a b

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {z : σ → A}
  (hz : Function.Bijective (aeval z : MvPolynomial σ k →ₐ[k] A))

/-- Evaluation of tangent vectors on the coordinates. -/
def epsDerEval : epsDer k A →ₗ[k] (σ → k) where
  toFun ξ i := (ξ : A →ₗ[k] k) (z i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

include hz in
theorem epsDerEval_bijective : Function.Bijective (epsDerEval (k := k) (A := A) (z := z)) := by
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun ξ hξ => ?_
    apply Subtype.ext
    refine epsDer_eq_zero_of_adjoin ξ.2 (adjoin_range_eq_top hz) ?_
    rintro _ ⟨i, rfl⟩
    exact congrFun hξ i
  · intro v
    refine ⟨⟨∑ i, v i • coordTangent hz i, sum_mem fun i _ =>
      Submodule.smul_mem _ _ (coordTangent_mem_epsDer hz i)⟩, ?_⟩
    funext j
    simp [epsDerEval, coordTangent_z]

include hz in
/-- With polynomial coordinates `z : σ → A`, the tangent space has dimension `#σ`. -/
theorem finrank_epsDer [Nontrivial k] : Module.finrank k (epsDer k A) = Fintype.card σ := by
  rw [(LinearEquiv.ofBijective _ (epsDerEval_bijective hz)).finrank_eq,
    Module.finrank_fintype_fun_eq_card]

include hz in
theorem finite_epsDer : Module.Finite k (epsDer k A) :=
  Module.Finite.equiv (LinearEquiv.ofBijective _ (epsDerEval_bijective hz)).symm

end Measure

section MeasureQuotient

variable {k A : Type*} [Field k] [CommRing A] [Bialgebra k A]
  {σ : Type*} [Fintype σ] [DecidableEq σ] {z : σ → A}
  (hz : Function.Bijective (aeval z : MvPolynomial σ k →ₐ[k] A))

include hz in
/-- Passing to the quotient by a coideal containing an element `g` with `ξᵢ(g) ≠ 0` for some
coordinate tangent vector strictly lowers the dimension of the tangent space. -/
theorem finrank_epsDer_quotient_lt {J : Ideal A} [(J.restrictScalars k).IsCoideal] {g : A}
    (hgJ : g ∈ J) {i : σ} (hi : coordTangent hz i g ≠ 0) :
    Module.finrank k (epsDer k (A ⧸ J)) < Module.finrank k (epsDer k A) := by
  have hfin : FiniteDimensional k (epsDer k A) := finite_epsDer hz
  let P : ((A ⧸ J) →ₗ[k] k) →ₗ[k] (A →ₗ[k] k) := (Ideal.Quotient.mkₐ k J).toLinearMap.dualMap
  have hPinj : Function.Injective P :=
    LinearMap.dualMap_injective_of_surjective Ideal.Quotient.mk_surjective
  have hle : (epsDer k (A ⧸ J)).map P < epsDer k A := by
    rw [SetLike.lt_iff_le_and_exists]
    constructor
    · rintro _ ⟨ξ, hξ, rfl⟩ a b
      simp only [P, LinearMap.dualMap_apply, AlgHom.toLinearMap_apply,
        Ideal.Quotient.mkₐ_eq_mk, map_mul]
      rw [hξ, Bialgebra.Quotient.counit_mk, Bialgebra.Quotient.counit_mk]
    · refine ⟨coordTangent hz i, coordTangent_mem_epsDer hz i, ?_⟩
      rintro ⟨ξ, _, hξ⟩
      apply hi
      rw [← hξ]
      simp only [P, LinearMap.dualMap_apply, AlgHom.toLinearMap_apply,
        Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 hgJ, map_zero]
  have h := Submodule.finrank_lt_finrank_of_lt hle
  rwa [← (Submodule.equivMapOfInjective P hPinj (epsDer k (A ⧸ J))).finrank_eq] at h

end MeasureQuotient

section Datum

variable {k A : Type*} [Field k] [CommRing A] [Bialgebra k A] [IsDomain A]
  [Algebra.FiniteType k A] [Algebra.FormallySmooth k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜]

/-- The data for one step of the split series: a homogeneous primitive element `g` of nonzero
degree, a `k`-algebra map `s : A → k[X]` with `s g = X`, and the strict decrease of the tangent
space dimension under passage to the quotient by any coideal containing `g`. -/
theorem exists_splitDatum (h𝒜 : IsGradedBialgebra 𝒜)
    (h0 : ∀ a ∈ 𝒜 0, Bialgebra.counitAlgHom k A a = 0 →
      a ∈ RingHom.ker (Bialgebra.counitAlgHom k A) ^ 2)
    (G : GradedMatrixCoefficients 𝒜) (hdiag : ∀ i, G.M i i = 1)
    (hlow : ∀ i j, j < i → G.M i j = 0) (hA : ∃ a : A, a ∉ Set.range (algebraMap k A)) :
    ∃ (g : A) (d : ℤ), d ≠ 0 ∧ g ∈ 𝒜 d ∧ Bialgebra.IsPrimitiveElem k g ∧
      (∃ s : A →ₐ[k] Polynomial k, s g = Polynomial.X) ∧
      ∀ (J : Ideal A) [(J.restrictScalars k).IsCoideal], g ∈ J →
        Module.finrank k (epsDer k (A ⧸ J)) < Module.finrank k (epsDer k A) := by
  obtain ⟨n₁, n₂, w, z, hw, hzw, hz⟩ := exists_homogeneous_polynomial_coordinates h𝒜 h0 G
  have hz0 : ∀ p, Coalgebra.counit (R := k) (z p) = 0 := fun p =>
    h𝒜.counit_eq_zero _ (hw p) _ (hzw p)
  obtain ⟨i, j, hM0, hMp⟩ := exists_isPrimitiveElem_of_unitriangular G hdiag hlow hA
  obtain ⟨g, d, hgd, hgp, hg2⟩ :=
    exists_isPrimitiveElem_not_mem_sq h𝒜 hzw hz hM0 hMp (G.mem i j)
  have hd : d ≠ 0 := by
    rintro rfl
    exact hg2 (h0 g hgd hgp.counit_eq_zero)
  obtain ⟨q, hq⟩ : ∃ q, coordTangent hz q g ≠ 0 := by
    by_contra h
    push Not at h
    exact hg2 (mem_sq_of_coordTangent_eq_zero hz hz0 hgp.counit_eq_zero h)
  refine ⟨g, d, hd, hgd, hgp, exists_algHom_polynomial_eq_X hzw hz hz0 hd hgd
    hgp.counit_eq_zero hg2, fun J _ hgJ => finrank_epsDer_quotient_lt hz hgJ hq⟩

end Datum

end Langlands.Algebra.GradedHopf
