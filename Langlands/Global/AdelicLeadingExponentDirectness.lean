import Langlands.Global.AdelicLeadingExponentDirectnessStatement
import Langlands.Global.AdelicEisensteinPositiveParametersProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ExponentDirectSum
import Mathlib.Algebra.Polynomial.Taylor

/-! # Directness of the unnormalized exponent decomposition -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints Langlands.HarishChandraSchwartz

private theorem exists_polynomial_on_nat_ray {V : Type*} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} {Q : V → ℂ} (hQ : Q ∈ polynomialFunctions V n) (x : V) :
    ∃ q : ℂ[X], q.natDegree ≤ n ∧ ∀ m : ℕ, q.eval (m : ℂ) = Q ((m : ℝ) • x) := by
  classical
  induction hQ using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨d, hd, ℓ, rfl⟩ := hf
    refine ⟨C (∏ j, ((ℓ j x : ℝ) : ℂ)) * X ^ d,
      (natDegree_C_mul_le _ _).trans (by simpa only [natDegree_X_pow] using hd), ?_⟩
    intro m
    simp only [eval_mul, eval_C, eval_pow, eval_X, map_smul, smul_eq_mul, Complex.ofReal_mul,
      Complex.ofReal_natCast]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]
  | zero =>
    exact ⟨0, by simp, fun _ => by simp⟩
  | add f₁ f₂ _ _ h₁ h₂ =>
    obtain ⟨q₁, hq₁, h₁⟩ := h₁
    obtain ⟨q₂, hq₂, h₂⟩ := h₂
    exact ⟨q₁ + q₂, (natDegree_add_le _ _).trans (max_le hq₁ hq₂),
      fun m => by simp only [eval_add, Pi.add_apply, h₁, h₂]⟩
  | smul c f _ hf =>
    obtain ⟨q, hq, he⟩ := hf
    exact ⟨C c * q, (natDegree_C_mul_le _ _).trans hq,
      fun m => by simp only [eval_mul, eval_C, Pi.smul_apply, smul_eq_mul, he]⟩

private def forwardDifference (q : ℂ[X]) : ℂ[X] :=
  taylor 1 q - q

private theorem iterate_forwardDifference_eq_zero (k : ℕ) (q : ℂ[X])
    (h : q.natDegree < k) : forwardDifference^[k] q = 0 := by
  induction k generalizing q with
  | zero => omega
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    by_cases hd : forwardDifference q = 0
    · rw [hd]
      exact Function.iterate_fixed (show forwardDifference 0 = 0 by simp [forwardDifference]) k
    · have hq : q ≠ 0 := by
        rintro rfl
        exact hd (by simp [forwardDifference])
      have hlt : (forwardDifference q).degree < q.degree := by
        unfold forwardDifference
        have ht := degree_sub_lt_left (degree_taylor q 1) (mt (taylor_eq_zero 1 q).1 hq)
          (leadingCoeff_taylor 1 q)
        rwa [degree_taylor] at ht
      exact ih _ ((natDegree_lt_natDegree hd hlt).trans_le (Nat.le_of_lt_succ h))

namespace StandardParabolicFamily

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G) (J : StandardIndex F G 𝓕.i 𝓕.ν)

local instance exponentDirectnessSplitCommGroup : CommGroup (𝓕.positiveSplitComponent J) where
  toGroup := inferInstance
  mul_comm x y :=
    Subtype.ext (𝓕.positiveSplitComponent_mul_comm J x.property y.property)

private theorem polynomialFunctions_le {V : Type*} [AddCommGroup V] [Module ℝ V]
    {m n : ℕ} (h : m ≤ n) : polynomialFunctions V m ≤ polynomialFunctions V n := by
  apply Submodule.span_mono
  rintro _ ⟨k, hk, forms, rfl⟩
  exact ⟨k, hk.trans h, forms, rfl⟩

/-- Zero satisfies the polynomial orbit condition for every label. -/
theorem hasUnnormalizedExponent_zero (lam : ComplexCharacterParameter F (𝓕.P J)) :
    𝓕.HasUnnormalizedExponent J lam 0 :=
  ⟨0, fun _ => ⟨0, (polynomialFunctions _ 0).zero_mem,
    fun _ _ => by simp [unnormalizedAction]⟩⟩

/-- Terms with the same unnormalized exponent can be added. -/
theorem hasUnnormalizedExponent_add {lam : ComplexCharacterParameter F (𝓕.P J)}
    {φ ψ : AdelicGroupPoints F G → ℂ}
    (hφ : 𝓕.HasUnnormalizedExponent J lam φ) (hψ : 𝓕.HasUnnormalizedExponent J lam ψ) :
    𝓕.HasUnnormalizedExponent J lam (φ + ψ) := by
  obtain ⟨m, hm⟩ := hφ
  obtain ⟨n, hn⟩ := hψ
  refine ⟨max m n, fun g => ?_⟩
  obtain ⟨Q, hQ, hvalues₁⟩ := hm g
  obtain ⟨P, hP, hvalues₂⟩ := hn g
  refine ⟨Q + P, Submodule.add_mem _ (polynomialFunctions_le (le_max_left m n) hQ)
    (polynomialFunctions_le (le_max_right m n) hP), ?_⟩
  intro x hx
  have h₁ := hvalues₁ x hx
  have h₂ := hvalues₂ x hx
  simp only [unnormalizedAction, Pi.add_apply] at *
  rw [add_mul, h₁, h₂]

/-- Negation preserves the polynomial orbit condition. -/
theorem hasUnnormalizedExponent_neg {lam : ComplexCharacterParameter F (𝓕.P J)}
    {φ : AdelicGroupPoints F G → ℂ} (hφ : 𝓕.HasUnnormalizedExponent J lam φ) :
    𝓕.HasUnnormalizedExponent J lam (-φ) := by
  obtain ⟨n, hn⟩ := hφ
  refine ⟨n, fun g => ?_⟩
  obtain ⟨Q, hQ, hvalues⟩ := hn g
  refine ⟨-Q, Submodule.neg_mem _ hQ, fun x hx => ?_⟩
  simp only [unnormalizedAction, Pi.neg_apply, neg_mul] at *
  rw [hvalues x hx]

/-- A difference of terms with the same label retains that exponent. -/
theorem hasUnnormalizedExponent_sub {lam : ComplexCharacterParameter F (𝓕.P J)}
    {φ ψ : AdelicGroupPoints F G → ℂ}
    (hφ : 𝓕.HasUnnormalizedExponent J lam φ) (hψ : 𝓕.HasUnnormalizedExponent J lam ψ) :
    𝓕.HasUnnormalizedExponent J lam (φ - ψ) := by
  rw [sub_eq_add_neg]
  exact 𝓕.hasUnnormalizedExponent_add J hφ (𝓕.hasUnnormalizedExponent_neg J hψ)

/-- A finite sum of terms with a common label retains that exponent. -/
theorem hasUnnormalizedExponent_sum {I : Type*} (s : Finset I)
    (f : I → AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F (𝓕.P J))
    (h : ∀ i ∈ s, 𝓕.HasUnnormalizedExponent J lam (f i)) :
    𝓕.HasUnnormalizedExponent J lam (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact 𝓕.hasUnnormalizedExponent_zero J lam
  | @insert i t hi ih =>
    rw [Finset.sum_insert hi]
    exact 𝓕.hasUnnormalizedExponent_add J (h i (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- Twisting by the Iwasawa height adds the inducing parameter to an
unnormalized exponent along that parabolic. -/
theorem hasUnnormalizedExponent_parameterTwist
    [IsClosedImmersion (𝓕.p J).hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (𝓕.p J) K) (s : ComplexCharacterParameter F (𝓕.P J))
    {lam : ComplexCharacterParameter F (𝓕.P J)} {φ : AdelicGroupPoints F G → ℂ}
    (hφ : 𝓕.HasUnnormalizedExponent J lam φ) :
    𝓕.HasUnnormalizedExponent J (lam + s) (hK.parameterTwist φ s) := by
  obtain ⟨m, hm⟩ := hφ
  refine ⟨m, fun g => ?_⟩
  obtain ⟨Q, hQ, hval⟩ := hm g
  refine ⟨hK.heightPower s g • Q, Submodule.smul_mem _ _ hQ, ?_⟩
  intro x hx
  have hheight : hK.heightPower s (map F (𝓕.P J) G (𝓕.p J) x * g) =
      parameterPower F (𝓕.P J) s x * hK.heightPower s g := by
    simp only [IsIwasawaCompact.heightPower, hK.height_map_mul, map_add, Complex.exp_add,
      parameterPower]
  have hcancel : parameterPower F (𝓕.P J) s x * parameterPower F (𝓕.P J) (-s) x = 1 := by
    rw [← parameterPower_add, add_neg_cancel]
    simp [parameterPower]
  calc
    _ = hK.heightPower s g *
        (𝓕.unnormalizedAction J x φ g * parameterPower F (𝓕.P J) (-lam) x) *
        (parameterPower F (𝓕.P J) s x * parameterPower F (𝓕.P J) (-s) x) := by
      simp only [unnormalizedAction, IsIwasawaCompact.parameterTwist, hheight, neg_add_rev,
        parameterPower_add]
      ring
    _ = _ := by rw [hcancel, mul_one, hval x hx]; rfl

/-- The polynomial orbit condition implies the simultaneous generalized
eigenvalue condition for the unnormalized split-component action. -/
theorem mem_jointGenEigenspace_of_hasUnnormalizedExponent
    {lam : ComplexCharacterParameter F (𝓕.P J)} {φ : AdelicGroupPoints F G → ℂ}
    (hφ : 𝓕.HasUnnormalizedExponent J lam φ) :
    φ ∈ jointGenEigenspace (𝓕.splitComponentRepresentation J)
      (fun b : 𝓕.positiveSplitComponent J => parameterPower F (𝓕.P J) lam b.val) := by
  obtain ⟨n, hn⟩ := hφ
  apply mem_jointGenEigenspace.mpr
  intro b
  let x := map F (𝓕.P J) G (𝓕.p J) b.val
  let eigenvalue := parameterPower F (𝓕.P J) lam b.val
  let D : Module.End ℂ (AdelicGroupPoints F G → ℂ) :=
    𝓕.splitComponentRepresentation J b - eigenvalue • 1
  refine ⟨n + 1, ?_⟩
  change (D ^ (n + 1)) φ = 0
  funext g
  obtain ⟨Q, hQ, hvalues⟩ := hn g
  obtain ⟨q, hq, hq_eval⟩ := exists_polynomial_on_nat_ray hQ (characterLog F (𝓕.P J) b.val)
  have hlog_pow (m : ℕ) :
      characterLog F (𝓕.P J) (b.val ^ m) = (m : ℝ) • characterLog F (𝓕.P J) b.val := by
    induction m with
    | zero => simp
    | succ m hm =>
      rw [pow_succ, characterLog_mul, hm, Nat.cast_succ, add_smul, one_smul]
  have hp (m : ℕ) : parameterPower F (𝓕.P J) lam (b.val ^ m) = eigenvalue ^ m := by
    change ((parameterCharacter F (𝓕.P J) lam (b.val ^ m) : ℂˣ) : ℂ) = eigenvalue ^ m
    simp only [map_pow, Units.val_pow_eq_pow_val, parameterCharacter_apply, eigenvalue]
  have hstart (m : ℕ) : φ (x ^ m * g) = eigenvalue ^ m * q.eval (m : ℂ) := by
    have hval := hvalues (b.val ^ m) (Subgroup.pow_mem _ b.property m)
    rw [hlog_pow, ← hq_eval m] at hval
    have hprod : parameterPower F (𝓕.P J) (-lam) (b.val ^ m) * eigenvalue ^ m = 1 := by
      rw [← hp, ← parameterPower_add, neg_add_cancel]
      simp [parameterPower]
    calc
      _ = (φ (x ^ m * g) * parameterPower F (𝓕.P J) (-lam) (b.val ^ m)) * eigenvalue ^ m := by
        rw [mul_assoc, hprod, mul_one]
      _ = _ := by
        simp only [unnormalizedAction, map_pow] at hval
        rw [show φ (x ^ m * g) * parameterPower F (𝓕.P J) (-lam) (b.val ^ m) =
          q.eval (m : ℂ) from hval, mul_comm]
  have hiter (k m : ℕ) :
      ((D ^ k) φ) (x ^ m * g) = eigenvalue ^ (m + k) * (forwardDifference^[k] q).eval (m : ℂ) := by
    induction k generalizing m with
    | zero => simpa only [pow_zero, Module.End.one_apply, Nat.add_zero,
        Function.iterate_zero_apply] using hstart m
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      change ((D ^ k) φ) (x * (x ^ m * g)) - eigenvalue * ((D ^ k) φ) (x ^ m * g) = _
      have hx : x * (x ^ m * g) = x ^ (m + 1) * g := by rw [pow_succ', mul_assoc]
      rw [hx, ih, ih]
      simp only [Function.iterate_succ_apply', forwardDifference, eval_sub, taylor_eval,
        Nat.cast_succ, show m + 1 + k = m + k + 1 by omega, Nat.add_succ, pow_succ]
      ring
  have hzero := iterate_forwardDifference_eq_zero (n + 1) q (Nat.lt_succ_of_le hq)
  simpa [hzero] using hiter (n + 1) 0

private abbrev unnormalizedEigenspace (lam : ComplexCharacterParameter F (𝓕.P J)) :
    Submodule ℂ (AdelicGroupPoints F G → ℂ) :=
  jointGenEigenspace (𝓕.splitComponentRepresentation J)
    (fun b : 𝓕.positiveSplitComponent J => parameterPower F (𝓕.P J) lam b.val)

theorem iSupIndep_unnormalizedCharacterEigenspace :
    iSupIndep (𝓕.unnormalizedEigenspace J) := by
  let r : ParabolicRootPresentation (𝓕.p J) (𝓕.l J) (𝓕.a J) :=
    ⟨⟨𝓕.T, 𝓕.i, 𝓕.ν, J.val, 𝓕.f J⟩, 𝓕.isCompatible J⟩
  let χ (lam : ComplexCharacterParameter F (𝓕.P J)) (b : 𝓕.positiveSplitComponent J) :=
    parameterPower F (𝓕.P J) lam b.val
  have hinj : Function.Injective χ :=
    (eisensteinPositiveParameters F G (𝓕.P J) (𝓕.M J) (𝓕.A J) (𝓕.p J) (𝓕.l J) (𝓕.a J) r).2
  exact (iSupIndep_jointGenEigenspace (𝓕.splitComponentRepresentation J)).comp hinj

/-- Finite sums of functions with distinct unnormalized exponents are direct. -/
theorem eq_zero_of_sum_eq_zero_of_hasUnnormalizedExponent
    (s : Finset (ComplexCharacterParameter F (𝓕.P J)))
    (c : ComplexCharacterParameter F (𝓕.P J) → AdelicGroupPoints F G → ℂ)
    (hc : ∀ lam ∈ s, 𝓕.HasUnnormalizedExponent J lam (c lam))
    (hz : ∑ lam ∈ s, c lam = 0) :
    ∀ lam ∈ s, c lam = 0 := by
  exact (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp
    (𝓕.iSupIndep_unnormalizedCharacterEigenspace J) s c
    (fun lam hlam => 𝓕.mem_jointGenEigenspace_of_hasUnnormalizedExponent J (hc lam hlam)) hz

/-- An error supported in nonleading exponents leaves the leading sums equal. -/
theorem leadingSum_eq_of_nonleading_difference
    (s t u : Finset (ComplexCharacterParameter F (𝓕.P J)))
    (c d b : ComplexCharacterParameter F (𝓕.P J) → AdelicGroupPoints F G → ℂ)
    (hc : ∀ lam ∈ s, 𝓕.HasUnnormalizedExponent J lam (c lam))
    (hd : ∀ lam ∈ t, 𝓕.HasUnnormalizedExponent J lam (d lam))
    (hb : ∀ lam ∈ u, 𝓕.HasUnnormalizedExponent J lam (b lam) ∧ ¬ 𝓕.IsLeadingExponent J lam)
    (heq : ∑ lam ∈ s, c lam = (∑ lam ∈ t, d lam) + ∑ lam ∈ u, b lam) :
    𝓕.leadingSum J s c = 𝓕.leadingSum J t d := by
  classical
  let support := s ∪ (t ∪ u)
  have hs : s ⊆ support := Finset.subset_union_left
  have ht : t ⊆ support := Finset.subset_union_left.trans Finset.subset_union_right
  have hu : u ⊆ support := Finset.subset_union_right.trans Finset.subset_union_right
  let pad (v : Finset (ComplexCharacterParameter F (𝓕.P J)))
      (f : ComplexCharacterParameter F (𝓕.P J) → AdelicGroupPoints F G → ℂ)
      (lam : ComplexCharacterParameter F (𝓕.P J)) := if lam ∈ v then f lam else 0
  have hmem (v : Finset (ComplexCharacterParameter F (𝓕.P J)))
      (f : ComplexCharacterParameter F (𝓕.P J) → AdelicGroupPoints F G → ℂ)
      (hf : ∀ lam ∈ v, 𝓕.HasUnnormalizedExponent J lam (f lam))
      (lam : ComplexCharacterParameter F (𝓕.P J)) :
      pad v f lam ∈ 𝓕.unnormalizedEigenspace J lam := by
    by_cases hm : lam ∈ v
    · simpa [pad, hm] using 𝓕.mem_jointGenEigenspace_of_hasUnnormalizedExponent J (hf lam hm)
    · simp [pad, hm]
  have hsum (v : Finset (ComplexCharacterParameter F (𝓕.P J))) (hv : v ⊆ support)
      (f : ComplexCharacterParameter F (𝓕.P J) → AdelicGroupPoints F G → ℂ) :
      ∑ lam ∈ support, pad v f lam = ∑ lam ∈ v, f lam := by
    simp only [pad, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hv]
  have hEq := (iSupIndep_iff_finsetSum_eq_imp_eq _).mp
    (𝓕.iSupIndep_unnormalizedCharacterEigenspace J) support (pad s c) (fun lam => pad t d lam + pad u b lam)
    (fun lam _ => ⟨hmem s c hc lam, Submodule.add_mem _
      (hmem t d hd lam) (hmem u b (fun x hx => (hb x hx).1) lam)⟩)
    (by simpa only [Finset.sum_add_distrib, hsum s hs, hsum t ht, hsum u hu] using heq)
  have hfilter (v : Finset (ComplexCharacterParameter F (𝓕.P J))) (hv : v ⊆ support)
      (f : ComplexCharacterParameter F (𝓕.P J) → AdelicGroupPoints F G → ℂ) :
      𝓕.leadingSum J v f = ∑ lam ∈ support.filter (𝓕.IsLeadingExponent J), pad v f lam := by
    have hInter : support.filter (𝓕.IsLeadingExponent J) ∩ v =
        v.filter (𝓕.IsLeadingExponent J) := by
      ext lam
      simp only [Finset.mem_inter, Finset.mem_filter]
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hv h.1, h.2⟩, h.1⟩⟩
    simp only [leadingSum, pad, Finset.sum_ite_mem, hInter]
  rw [hfilter s hs, hfilter t ht]
  refine Finset.sum_congr rfl fun lam hlam => ?_
  have hlead := Finset.mem_filter.mp hlam
  have hnot : lam ∉ u := fun h => (hb lam h).2 hlead.2
  simpa [pad, hnot] using hEq lam hlead.1

/-- Cuspidal projection decompositions with only nonleading differences
give the two functions a common family of global leading components. -/
theorem exists_common_leadingComponents_of_nonleading_differences
    {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (rho : MatrixRepresentation G (Fin N))
    (φ ψ : AdelicGroupPoints F G → ℂ)
    (h : ∀ Q : StandardIndex F G 𝓕.i 𝓕.ν,
      ∃ φc ψc : AdelicGroupPoints F G → ℂ,
        𝓕.IsCuspidalProjection hsmooth Kinf rho Q (𝓕.constantTerm Q φ) φc ∧
        𝓕.IsCuspidalProjection hsmooth Kinf rho Q (𝓕.constantTerm Q ψ) ψc ∧
        ∃ (s t u : Finset (ComplexCharacterParameter F (𝓕.P Q)))
          (c b e : ComplexCharacterParameter F (𝓕.P Q) → AdelicGroupPoints F G → ℂ),
          𝓕.IsExponentDecomposition hsmooth Kinf rho Q φc s c ∧
          𝓕.IsExponentDecomposition hsmooth Kinf rho Q ψc t b ∧
          (∀ lam ∈ u, 𝓕.HasUnnormalizedExponent Q lam (e lam) ∧ ¬ 𝓕.IsLeadingExponent Q lam) ∧
          φc = ψc + ∑ lam ∈ u, e lam) :
    ∃ L, 𝓕.IsGlobalLeadingCuspidalComponents hsmooth Kinf rho φ L ∧
      𝓕.IsGlobalLeadingCuspidalComponents hsmooth Kinf rho ψ L := by
  classical
  have hcommon (Q : StandardIndex F G 𝓕.i 𝓕.ν) :
      ∃ lq : AdelicGroupPoints F G → ℂ,
        (∃ φc, 𝓕.IsCuspidalProjection hsmooth Kinf rho Q (𝓕.constantTerm Q φ) φc ∧
          𝓕.IsLeadingPart hsmooth Kinf rho Q φc lq) ∧
        (∃ ψc, 𝓕.IsCuspidalProjection hsmooth Kinf rho Q (𝓕.constantTerm Q ψ) ψc ∧
          𝓕.IsLeadingPart hsmooth Kinf rho Q ψc lq) := by
    obtain ⟨φc, ψc, hφ, hψ, s, t, u, c, b, e, hs, ht, he, hEq⟩ := h Q
    rw [hs.sum_eq, ht.sum_eq] at hEq
    have heq := 𝓕.leadingSum_eq_of_nonleading_difference Q s t u c b e
      hs.exponent ht.exponent he hEq
    exact ⟨𝓕.leadingSum Q s c, ⟨φc, hφ, s, c, hs, rfl⟩, ⟨ψc, hψ, t, b, ht, heq⟩⟩
  choose L hL using hcommon
  exact ⟨L, fun Q => (hL Q).1, fun Q => (hL Q).2⟩

end StandardParabolicFamily

/-- Directness and the resulting leading-sum comparison on actual functions. -/
theorem eisensteinExponentDirectness : EisensteinExponentDirectnessStatement.{u} := by
  intro F _ _ G _ _ _ fam J
  exact ⟨fam.eq_zero_of_sum_eq_zero_of_hasUnnormalizedExponent J,
    fam.leadingSum_eq_of_nonleading_difference J⟩

end Langlands.Global
