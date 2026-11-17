import Langlands.GroupScheme.Torus.CompleteLocalDeformation.Rigidity
import Langlands.GroupScheme.Torus.CompleteLocalDeformation.OpenClosed
import Langlands.Algebra.NilpotentModuleFiniteness
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.Bialgebra.GroupLike
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # Lifting split bialgebras through nilpotent thickenings

Let `J` be a nilpotent ideal of a commutative ring `R` and `C` a flat commutative
`R`-bialgebra. Suppose a family `y : N → C`, indexed by an additive commutative monoid, reduces
modulo `J` to a multiplicative basis of group-like elements. Then `C` has a basis of
group-like elements `g : N → C` with `g ≡ y` modulo `J`, multiplicative in `N`, and so there is
a bialgebra isomorphism `C ≃ R[N]` sending each `y a` to `xᵃ` modulo `J`. -/

noncomputable section

universe u v w

open TensorProduct Coalgebra

namespace Langlands.GroupScheme.CompleteLocalDeformation

open Langlands.GroupAlgebraCoaction

section Module

variable {R : Type u} [CommRing R] {C : Type v} [AddCommGroup C] [Module R C]

/-- A finitely supported function with all values in `J` lies in `J • ⊤`. -/
theorem finsupp_mem_smul_top {ι : Type*} (J : Ideal R) (k : ι →₀ R) (hk : ∀ i, k i ∈ J) :
    k ∈ J • (⊤ : Submodule R (ι →₀ R)) := by
  classical
  have h := Submodule.finsuppSum_mem R (J • (⊤ : Submodule R (ι →₀ R))) k
    (fun i r => Finsupp.single i r) (fun i _ => by
      rw [← mul_one (k i), ← smul_eq_mul, ← Finsupp.smul_single]
      exact Submodule.smul_mem_smul (hk i) trivial)
  rwa [Finsupp.sum_single] at h

/-- For a surjection onto a flat module, an element of the kernel lying in `J • ⊤` lies in
`J • ker`. -/
theorem mem_smul_ker_of_flat [Module.Flat R C] (J : Ideal R) {F : Type*} [AddCommGroup F]
    [Module R F] (Φ : F →ₗ[R] C) (hΦ : Function.Surjective Φ) {k : F} (hk : Φ k = 0)
    (hkJ : k ∈ J • (⊤ : Submodule R F)) : k ∈ J • LinearMap.ker Φ := by
  set K := LinearMap.ker Φ
  have inj := LinearMap.lTensor_injective_of_exact_of_flat Φ hΦ K.subtype K.injective_subtype
    (LinearMap.exact_subtype_ker_map Φ) (R ⧸ J)
  have h1 : (1 : R ⧸ J) ⊗ₜ[R] k = 0 := by
    apply (TensorProduct.quotTensorEquivQuotSMul F J).injective
    rw [map_zero, ← map_one (Ideal.Quotient.mk J), TensorProduct.quotTensorEquivQuotSMul_mk_tmul,
      one_smul, Submodule.Quotient.mk_eq_zero]
    exact hkJ
  have h2 : (1 : R ⧸ J) ⊗ₜ[R] (⟨k, hk⟩ : K) = 0 := by
    apply inj
    rw [map_zero, LinearMap.lTensor_tmul]
    exact h1
  have h3 := congrArg (TensorProduct.quotTensorEquivQuotSMul K J) h2
  rw [map_zero, ← map_one (Ideal.Quotient.mk J), TensorProduct.quotTensorEquivQuotSMul_mk_tmul,
    one_smul, Submodule.Quotient.mk_eq_zero] at h3
  have h4 := Submodule.mem_map_of_mem (f := K.subtype) h3
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] at h4
  exact h4

/-- Nakayama's lemma for a nilpotent ideal, for arbitrary submodules. -/
theorem le_of_le_sup_smul_of_isNilpotent (J : Ideal R) (hJ : IsNilpotent J)
    (N V : Submodule R C) (h : V ≤ N ⊔ J • V) : V ≤ N := by
  have key : ∀ n : ℕ, V ≤ N ⊔ J ^ (n + 1) • V := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih =>
      calc V ≤ N ⊔ J ^ (n + 1) • V := ih
        _ ≤ N ⊔ J ^ (n + 1) • (N ⊔ J • V) := sup_le_sup_left (smul_mono_right _ h) _
        _ = N ⊔ (J ^ (n + 1) • N ⊔ J ^ (n + 1) • J • V) := by rw [Submodule.smul_sup]
        _ ≤ N ⊔ J ^ (n + 1 + 1) • V := by
          refine sup_le le_sup_left (sup_le (le_trans Submodule.smul_le_right le_sup_left) ?_)
          rw [← Submodule.mul_smul, ← pow_succ]
          exact le_sup_right
  obtain ⟨n, hn⟩ := hJ
  have := key n
  rw [pow_succ, hn, zero_mul, Ideal.zero_eq_bot, Submodule.bot_smul, sup_bot_eq] at this
  exact this

/-- A family in a flat module that spans and is linearly independent modulo a nilpotent ideal is
linearly independent and spans. -/
theorem linearIndependent_of_flat_of_isNilpotent [Module.Flat R C] (J : Ideal R)
    (hJ : IsNilpotent J) {ι : Type w} (y : ι → C)
    (hspan : Submodule.span R (Set.range y) ⊔ J • ⊤ = ⊤)
    (hind : ∀ c : ι →₀ R, Finsupp.linearCombination R y c ∈ J • (⊤ : Submodule R C) →
      ∀ i, c i ∈ J) :
    LinearIndependent R y ∧ Submodule.span R (Set.range y) = ⊤ := by
  have htop : Submodule.span R (Set.range y) = ⊤ :=
    Langlands.Algebra.eq_top_of_sup_smul_eq_top_of_nilpotent J hJ _ hspan
  refine ⟨?_, htop⟩
  set Φ := Finsupp.linearCombination R y
  have hΦ : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, htop]
  have hle : LinearMap.ker Φ ≤ ⊥ ⊔ J • LinearMap.ker Φ := by
    intro k hk
    rw [bot_sup_eq]
    refine mem_smul_ker_of_flat J Φ hΦ hk ?_
    apply finsupp_mem_smul_top
    apply hind
    rw [LinearMap.mem_ker.mp hk]
    exact zero_mem _
  have hbot := le_of_le_sup_smul_of_isNilpotent J hJ ⊥ _ hle
  exact LinearMap.ker_eq_bot.mp (eq_bot_iff.mpr hbot)

/-- `1 ⊗ x` vanishes in `(R ⧸ J) ⊗ M` exactly when `x ∈ J • ⊤`. -/
theorem one_tmul_eq_zero_iff {M : Type*} [AddCommGroup M] [Module R M] (J : Ideal R) (x : M) :
    (1 : R ⧸ J) ⊗ₜ[R] x = 0 ↔ x ∈ J • (⊤ : Submodule R M) := by
  rw [← (TensorProduct.quotTensorEquivQuotSMul M J).injective.eq_iff, map_zero,
    ← map_one (Ideal.Quotient.mk J), TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul,
    Submodule.Quotient.mk_eq_zero]

/-- Every element of `(R ⧸ J) ⊗ M` has the form `1 ⊗ x`. -/
theorem exists_one_tmul_eq {M : Type*} [AddCommGroup M] [Module R M] (J : Ideal R)
    (t : (R ⧸ J) ⊗[R] M) : ∃ x : M, (1 : R ⧸ J) ⊗ₜ[R] x = t := by
  induction t with
  | tmul r x =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    refine ⟨r • x, ?_⟩
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
  | add s t hs ht =>
    obtain ⟨x, rfl⟩ := hs
    obtain ⟨z, rfl⟩ := ht
    exact ⟨x + z, TensorProduct.tmul_add _ _ _⟩

/-- Scalars act on `1 ⊗ x` through the quotient map. -/
theorem one_tmul_smul {M : Type*} [AddCommGroup M] [Module R M] (J : Ideal R) (r : R) (x : M) :
    (1 : R ⧸ J) ⊗ₜ[R] (r • x) = Ideal.Quotient.mk J r • ((1 : R ⧸ J) ⊗ₜ[R] x) := by
  rw [TensorProduct.tmul_smul, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]

end Module

section Convolution

open WithConv

variable {R : Type u} [CommRing R] {C : Type v} [AddCommGroup C] [Module R C] [Coalgebra R C]

/-- The convolution product of `WithConv` is the convolution `conv` of linear forms. -/
theorem ofConv_mul (f g : WithConv (C →ₗ[R] R)) : (f * g).ofConv = conv f.ofConv g.ofConv := by
  ext c
  rw [LinearMap.convMul_apply]
  simp only [conv, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  generalize TensorProduct.map f.ofConv g.ofConv (comul c) = t
  induction t with
  | tmul x z => simp
  | add s t hs ht => rw [map_add, map_add, hs, ht]

variable (J : Ideal R)

/-- Reduction modulo `J` of the convolution ring of linear forms. -/
def convReduce : WithConv (C →ₗ[R] R) →+* WithConv (C →ₗ[R] R ⧸ J) where
  toFun f := toConv ((Ideal.Quotient.mkₐ R J).toLinearMap ∘ₗ f.ofConv)
  map_one' := by
    ext c
    simp [LinearMap.convOne_apply]
  map_mul' f g := by
    ext c
    exact congrArg (· c) (LinearMap.algHom_comp_convMul_distrib (Ideal.Quotient.mkₐ R J) f g)
  map_zero' := by
    ext c
    simp
  map_add' f g := by
    ext c
    simp

theorem convReduce_apply (f : WithConv (C →ₗ[R] R)) (c : C) :
    convReduce J f c = Ideal.Quotient.mk J (f c) := rfl

theorem convReduce_eq_zero_iff (f : WithConv (C →ₗ[R] R)) :
    convReduce J f = 0 ↔ ValuesIn J f.ofConv := by
  constructor
  · intro h c
    have := congrArg (fun φ : WithConv (C →ₗ[R] R ⧸ J) => φ c) h
    simp only [convReduce_apply] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  · intro h
    ext c
    change Ideal.Quotient.mk J (f c) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (h c)

/-- Linear forms with values in a nilpotent ideal are nilpotent for convolution. -/
theorem isNilpotent_of_valuesIn (hJ : IsNilpotent J) (f : WithConv (C →ₗ[R] R))
    (hf : ValuesIn J f.ofConv) : IsNilpotent f := by
  obtain ⟨n, hn⟩ := hJ
  refine ⟨n, ?_⟩
  have key : ∀ k : ℕ, ValuesIn (J ^ k) (f ^ k).ofConv := by
    intro k
    induction k with
    | zero =>
      intro c
      rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    | succ k ih =>
      rw [pow_succ f k, ofConv_mul, pow_succ J k]
      exact ih.conv_mul hf
  ext c
  have := key n c
  rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  simpa using this

omit [Coalgebra R C] in
/-- A linear form with values in `J` on a spanning family takes all its values in `J`. -/
theorem valuesIn_of_span {ι : Type*} {y : ι → C} (hsp : Submodule.span R (Set.range y) = ⊤)
    (f : C →ₗ[R] R) (h : ∀ i, f (y i) ∈ J) : ValuesIn J f := by
  intro x
  have hle : Submodule.span R (Set.range y) ≤ Submodule.comap f J := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact h i
  rw [hsp] at hle
  exact hle Submodule.mem_top

/-- **Lifting convolution idempotents.** A linear form that is a convolution idempotent modulo a
nilpotent ideal `J` is congruent modulo `J` to a convolution idempotent. -/
theorem exists_conv_idempotent_lift (hJ : IsNilpotent J) (χ₀ : C →ₗ[R] R)
    (h : ValuesIn J (conv χ₀ χ₀ - χ₀)) :
    ∃ χ : C →ₗ[R] R, conv χ χ = χ ∧ ValuesIn J (χ - χ₀) := by
  have key : ∃ χ' : WithConv (C →ₗ[R] R), IsIdempotentElem χ' ∧
      convReduce J χ' = convReduce J (toConv χ₀) := by
    refine exists_isIdempotentElem_eq_of_ker_isNilpotent (convReduce J) ?_
      (convReduce J (toConv χ₀)) (RingHom.mem_range_self _ _) ?_
    · intro x hx
      exact isNilpotent_of_valuesIn J hJ x
        ((convReduce_eq_zero_iff J x).mp (RingHom.mem_ker.mp hx))
    · rw [IsIdempotentElem, ← map_mul, ← sub_eq_zero, ← map_sub, convReduce_eq_zero_iff,
        WithConv.ofConv_sub, ofConv_mul]
      exact h
  obtain ⟨χ', hχ'idem, hχ'⟩ := key
  refine ⟨χ'.ofConv, by rw [← ofConv_mul, hχ'idem.eq], ?_⟩
  have : convReduce J (χ' - toConv χ₀) = 0 := by rw [map_sub, hχ', sub_self]
  rw [convReduce_eq_zero_iff] at this
  exact this

end Convolution

section GroupLike

open WithConv

variable {R : Type u} [CommRing R] {C : Type v} [AddCommGroup C] [Module R C] [Coalgebra R C]

/-- The projection `ract χ` attached to a convolution idempotent `χ` that is the coordinate form
of `y a` modulo `J` has range spanned by `ract χ (y a)`, which is congruent to `y a` modulo `J`. -/
theorem ract_eq_smul_of_idempotent (J : Ideal R) (hJ : IsNilpotent J) {N : Type w}
    [DecidableEq N] {y : N → C} (hsp : Submodule.span R (Set.range y) = ⊤)
    (hy : ∀ a, comul (R := R) (y a) - y a ⊗ₜ[R] y a ∈ J • (⊤ : Submodule R (C ⊗[R] C)))
    (a : N) {χ : C →ₗ[R] R} (hχχ : conv χ χ = χ)
    (hχy : ∀ c, χ (y c) - (if c = a then 1 else 0) ∈ J) :
    ract χ (y a) - y a ∈ J • (⊤ : Submodule R C) ∧
      ∀ x, ∃ r : R, ract χ x = r • ract χ (y a) := by
  classical
  have hPP : ∀ x, ract χ (ract χ x) = ract χ x := fun x => by rw [ract_ract, hχχ]
  have hPy : ∀ c, ract χ (y c) - (if c = a then (1 : R) else 0) • y c ∈
      J • (⊤ : Submodule R C) := by
    intro c
    have h1 := map_mem_smul_top ((TensorProduct.rid R C).toLinearMap ∘ₗ χ.lTensor C) J (hy c)
    have h2 : ract χ (y c) - (if c = a then (1 : R) else 0) • y c =
        ((TensorProduct.rid R C).toLinearMap ∘ₗ χ.lTensor C) (comul (y c) - y c ⊗ₜ y c) +
          (χ (y c) - (if c = a then 1 else 0)) • y c := by
      simp only [ract, map_sub, LinearMap.coe_comp, Function.comp_apply, LinearMap.lTensor_tmul,
        LinearEquiv.coe_coe, TensorProduct.rid_tmul, sub_smul]
      abel
    rw [h2]
    exact add_mem h1 (Submodule.smul_mem_smul (hχy c) Submodule.mem_top)
  have hPyc : ∀ c, c ≠ a → ract χ (y c) ∈ J • (⊤ : Submodule R C) := by
    intro c hc
    simpa [hc] using hPy c
  refine ⟨by simpa using hPy a, ?_⟩
  have hV : LinearMap.range (ract χ) ≤ Submodule.span R {ract χ (y a)} := by
    apply le_of_le_sup_smul_of_isNilpotent J hJ
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ Submodule.span R (Set.range y) := hsp ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, rfl⟩ := hz
      by_cases hc : c = a
      · subst hc
        exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
      · apply Submodule.mem_sup_right
        rw [← hPP (y c)]
        have := Submodule.mem_map_of_mem (f := ract χ) (hPyc c hc)
        rwa [Submodule.map_smul'', ← LinearMap.range_eq_map] at this
    | zero => simp
    | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx
  intro x
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (hV (LinearMap.mem_range_self _ x))
  exact ⟨r, hr.symm⟩

/-- If the range of `ract χ` is spanned by `g' = ract χ y₀` and the counit of `g'` is a unit,
then `g'` is a unit multiple of a group-like element. -/
theorem isGroupLikeElem_smul_of_ract (χ : C →ₗ[R] R) (y₀ : C)
    (hPV : ∀ x, ∃ r : R, ract χ x = r • ract χ y₀) {ui : R}
    (hui : ui * counit (R := R) (ract χ y₀) = 1) :
    IsGroupLikeElem R (ui • ract χ y₀) := by
  set g' := ract χ y₀ with hg'
  have hlt : ∀ t : C ⊗[R] C, ∃ w : C, (ract χ).lTensor C t = w ⊗ₜ g' := by
    intro t
    induction t with
    | tmul x z =>
      obtain ⟨r, hr⟩ := hPV z
      exact ⟨r • x, by rw [LinearMap.lTensor_tmul, hr, TensorProduct.smul_tmul]⟩
    | add s t hs ht =>
      obtain ⟨w₁, hw₁⟩ := hs
      obtain ⟨w₂, hw₂⟩ := ht
      exact ⟨w₁ + w₂, by rw [map_add, hw₁, hw₂, TensorProduct.add_tmul]⟩
  obtain ⟨w, hw⟩ := hlt (comul y₀)
  have hcomul : comul (R := R) g' = w ⊗ₜ g' := by
    rw [hg', ← lTensor_ract_comul χ y₀]
    exact hw
  have hwg : counit (R := R) g' • w = g' := by
    have h := Coalgebra.lTensor_counit_comul (R := R) g'
    rw [hcomul, LinearMap.lTensor_tmul] at h
    have := congrArg (TensorProduct.rid R C) h
    simpa using this
  have hw' : w = ui • g' := by rw [← hwg, smul_smul, hui, one_smul]
  refine ⟨?_, ?_⟩
  · rw [map_smul, smul_eq_mul, hui]
  · rw [map_smul, hcomul, hw', TensorProduct.tmul_smul]

/-- A group-like element congruent modulo a nilpotent ideal to `y₀`, where `χ y₀ ≡ 1` for a
convolution idempotent `χ` whose projection `ract χ` has range spanned by a group-like `g`,
equals `g`. -/
theorem eq_of_isGroupLikeElem_of_ract (J : Ideal R) (hJ : IsNilpotent J) {χ : C →ₗ[R] R}
    (hχχ : conv χ χ = χ) {g y₀ : C} (hg : IsGroupLikeElem R g) (hχ1 : χ y₀ - 1 ∈ J)
    (hPV : ∀ x, ∃ r : R, ract χ x = r • g) {h : C} (hh : IsGroupLikeElem R h)
    (hhy : h - y₀ ∈ J • (⊤ : Submodule R C)) : h = g := by
  have hχh : χ h * χ h = χ h := by
    have := congrArg (fun f : C →ₗ[R] R => f h) hχχ
    simpa only [conv, LinearMap.coe_comp, Function.comp_apply, hh.comul_eq_tmul_self,
      TensorProduct.map_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul,
      smul_eq_mul] using this
  have hχh1 : χ h - 1 ∈ J := by
    have h1 := form_mem_of_mem_smul_top χ J hhy
    have : χ h - 1 = χ (h - y₀) + (χ y₀ - 1) := by rw [map_sub]; ring
    rw [this]
    exact J.add_mem h1 hχ1
  have hχh_eq : χ h = 1 := by
    have hidem : IsIdempotentElem (1 - χ h) := IsIdempotentElem.one_sub hχh
    have hnil : IsNilpotent (1 - χ h) := by
      obtain ⟨n, hn⟩ := hJ
      refine ⟨n, ?_⟩
      have := Ideal.pow_mem_pow (J.neg_mem hχh1) n
      rwa [hn, Ideal.zero_eq_bot, Ideal.mem_bot, neg_sub] at this
    have := hidem.eq_zero_of_isNilpotent hnil
    rw [sub_eq_zero] at this
    exact this.symm
  have hPh : ract χ h = h := by
    simp only [ract, LinearMap.coe_comp, Function.comp_apply, hh.comul_eq_tmul_self,
      LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul, hχh_eq, one_smul]
  obtain ⟨r, hr⟩ := hPV h
  rw [hPh] at hr
  have hεh := hh.counit_eq_one
  rw [hr, map_smul, smul_eq_mul, hg.counit_eq_one, mul_one] at hεh
  rw [hr, hεh, one_smul]

/-- **Lifting group-like elements.** Let `J` be a nilpotent ideal and `y` a basis of a coalgebra
whose members are group-like modulo `J`. Then each `y a` is congruent modulo `J` to a group-like
element, and to only one. -/
theorem exists_isGroupLikeElem_sub_mem (J : Ideal R) (hJ : IsNilpotent J) {N : Type w}
    {y : N → C} (hli : LinearIndependent R y) (hsp : Submodule.span R (Set.range y) = ⊤)
    (hy : ∀ a, comul (R := R) (y a) - y a ⊗ₜ[R] y a ∈ J • (⊤ : Submodule R (C ⊗[R] C)))
    (a : N) :
    ∃ g : C, (IsGroupLikeElem R g ∧ g - y a ∈ J • (⊤ : Submodule R C)) ∧
      ∀ h : C, IsGroupLikeElem R h → h - y a ∈ J • (⊤ : Submodule R C) → h = g := by
  classical
  -- the coordinate form of `y a`
  obtain ⟨χ₀, hχ₀⟩ : ∃ χ₀ : C →ₗ[R] R, ∀ c, χ₀ (y c) = if c = a then 1 else 0 := by
    let b : Module.Basis N R C := Module.Basis.mk hli (by rw [hsp])
    refine ⟨b.coord a, fun c => ?_⟩
    rw [← Module.Basis.mk_apply hli (by rw [hsp]) c, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply]
  -- it is a convolution idempotent modulo `J`
  have hidem₀ : ValuesIn J (conv χ₀ χ₀ - χ₀) := by
    apply valuesIn_of_span J hsp
    intro c
    have h1 := form_mem_of_mem_smul_top
      ((TensorProduct.lid R R).toLinearMap ∘ₗ TensorProduct.map χ₀ χ₀) J (hy c)
    have h2 : (conv χ₀ χ₀ - χ₀) (y c) =
        ((TensorProduct.lid R R).toLinearMap ∘ₗ TensorProduct.map χ₀ χ₀)
          (comul (y c) - y c ⊗ₜ y c) := by
      simp only [LinearMap.sub_apply, map_sub, conv, LinearMap.coe_comp, Function.comp_apply,
        TensorProduct.map_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul, smul_eq_mul, hχ₀]
      split_ifs <;> simp
    rw [h2]
    exact h1
  -- lift it to a convolution idempotent
  obtain ⟨χ, hχχ, hχJ⟩ := exists_conv_idempotent_lift J hJ χ₀ hidem₀
  have hχy : ∀ c, χ (y c) - (if c = a then 1 else 0) ∈ J := by
    intro c
    rw [← hχ₀ c]
    simpa using hχJ (y c)
  have hχ1 : χ (y a) - 1 ∈ J := by simpa using hχy a
  -- the projection `ract χ` and the element `g' = ract χ (y a)`
  obtain ⟨hg'y, hPV⟩ := ract_eq_smul_of_idempotent J hJ hsp hy a hχχ hχy
  set g' := ract χ (y a) with hg'
  -- the counit of `g'` is a unit
  have hu1 : counit (R := R) g' - 1 ∈ J := by rwa [hg', counit_ract]
  have hu : IsUnit (counit (R := R) g') := by
    have hnil : IsNilpotent (counit (R := R) g' - 1) := by
      obtain ⟨n, hn⟩ := hJ
      refine ⟨n, ?_⟩
      have := Ideal.pow_mem_pow hu1 n
      rwa [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    simpa using hnil.isUnit_add_one
  obtain ⟨ui, hui⟩ : ∃ ui : R, ui * counit (R := R) g' = 1 :=
    ⟨↑hu.unit⁻¹, hu.val_inv_mul⟩
  have hgl : IsGroupLikeElem R (ui • g') := isGroupLikeElem_smul_of_ract χ (y a) hPV hui
  refine ⟨ui • g', ⟨hgl, ?_⟩, fun h hh hhy => ?_⟩
  · have hui1 : ui - 1 ∈ J := by
      have : ui - 1 = ui * -(counit (R := R) g' - 1) := by
        rw [mul_neg, mul_sub, hui, mul_one]
        ring
      rw [this]
      exact J.mul_mem_left _ (J.neg_mem hu1)
    have : ui • g' - y a = ui • (g' - y a) + (ui - 1) • y a := by
      rw [smul_sub, sub_smul, one_smul]
      abel
    rw [this]
    exact add_mem (Submodule.smul_mem _ _ hg'y) (Submodule.smul_mem_smul hui1 Submodule.mem_top)
  · refine eq_of_isGroupLikeElem_of_ract J hJ hχχ hgl hχ1 (fun x => ?_) hh hhy
    obtain ⟨r, hr⟩ := hPV x
    refine ⟨r * counit (R := R) g', ?_⟩
    rw [hr, smul_smul, mul_assoc, mul_comm (counit (R := R) g') ui, hui, mul_one]

end GroupLike

section Bialgebra

variable {R : Type u} [CommRing R] {C : Type v} [CommRing C] [Bialgebra R C]

/-- `J • ⊤` is closed under multiplication by elements of the algebra. -/
theorem mul_mem_smul_top (J : Ideal R) {x : C} (hx : x ∈ J • (⊤ : Submodule R C)) (z : C) :
    x * z ∈ J • (⊤ : Submodule R C) := by
  refine Submodule.smul_induction_on hx (fun r hr c _ => ?_) (fun a b ha hb => ?_)
  · rw [smul_mul_assoc]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [add_mul]
    exact add_mem ha hb

/-- **Lifting split bialgebras through nilpotent thickenings.** Let `J` be a nilpotent ideal of
`R` and `C` a flat commutative `R`-bialgebra. Let `y : N → C` be a family that modulo `J` spans,
is linearly independent, consists of group-like elements, and is multiplicative. Then there is a
bialgebra isomorphism `C ≃ R[N]` sending each `y a` to `xᵃ` modulo `J`. -/
theorem exists_bialgEquiv_of_isNilpotent [Module.Flat R C] (J : Ideal R) (hJ : IsNilpotent J)
    {N : Type w} [AddCommMonoid N] (y : N → C)
    (hspan : Submodule.span R (Set.range y) ⊔ J • ⊤ = ⊤)
    (hind : ∀ c : N →₀ R, Finsupp.linearCombination R y c ∈ J • (⊤ : Submodule R C) →
      ∀ i, c i ∈ J)
    (hcomul : ∀ a, comul (R := R) (y a) - y a ⊗ₜ[R] y a ∈ J • (⊤ : Submodule R (C ⊗[R] C)))
    (hmul : ∀ a b, y a * y b - y (a + b) ∈ J • (⊤ : Submodule R C)) :
    ∃ θ : C ≃ₐc[R] AddMonoidAlgebra R N, ∀ a,
      θ (y a) - AddMonoidAlgebra.single a 1 ∈ J • (⊤ : Submodule R (AddMonoidAlgebra R N)) := by
  classical
  obtain ⟨hli, hsp⟩ := linearIndependent_of_flat_of_isNilpotent J hJ y hspan hind
  choose g hg hgu using fun a => exists_isGroupLikeElem_sub_mem J hJ hli hsp hcomul a
  have hgy : ∀ a, g a - y a ∈ J • (⊤ : Submodule R C) := fun a => (hg a).2
  -- `g` is again a basis
  have hgspan : Submodule.span R (Set.range g) ⊔ J • ⊤ = ⊤ := by
    have hle : Submodule.span R (Set.range y) ≤ Submodule.span R (Set.range g) ⊔ J • ⊤ := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      have : g a - (g a - y a) ∈ Submodule.span R (Set.range g) ⊔ J • ⊤ :=
        sub_mem (Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩))
          (Submodule.mem_sup_right (hgy a))
      rwa [sub_sub_cancel] at this
    rw [hsp] at hle
    exact top_le_iff.mp hle
  have hgind : ∀ c : N →₀ R, Finsupp.linearCombination R g c ∈ J • (⊤ : Submodule R C) →
      ∀ i, c i ∈ J := by
    intro c hc
    apply hind c
    have : Finsupp.linearCombination R y c =
        Finsupp.linearCombination R g c - c.sum (fun i r => r • (g i - y i)) := by
      simp only [Finsupp.linearCombination_apply, smul_sub, Finsupp.sum_sub]
      abel
    rw [this]
    exact sub_mem hc (Submodule.finsuppSum_mem R _ _ _ fun i _ => Submodule.smul_mem _ _ (hgy i))
  obtain ⟨hgli, hgsp⟩ := linearIndependent_of_flat_of_isNilpotent J hJ g hgspan hgind
  -- `g` is multiplicative
  have hgmul : ∀ a b, g a * g b = g (a + b) := by
    intro a b
    apply hgu (a + b) _ ((hg a).1.mul (hg b).1)
    have : g a * g b - y (a + b) =
        (g a - y a) * g b + (g b - y b) * y a + (y a * y b - y (a + b)) := by ring
    rw [this]
    exact add_mem (add_mem (mul_mem_smul_top J (hgy a) _) (mul_mem_smul_top J (hgy b) _))
      (hmul a b)
  have hg0 : g 0 = 1 := by
    have h : ∀ x : C, g 0 * x = x := by
      intro x
      have hx : x ∈ Submodule.span R (Set.range g) := hgsp ▸ Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨c, rfl⟩ := hz
        rw [hgmul, zero_add]
      | zero => rw [mul_zero]
      | add x z _ _ hx hz => rw [mul_add, hx, hz]
      | smul r x _ hx => rw [mul_smul_comm, hx]
    simpa using h 1
  -- the bialgebra map `R[N] → C`
  let F : Multiplicative N →* C :=
    { toFun := fun a => g a.toAdd
      map_one' := by simp only [toAdd_one, hg0]
      map_mul' := fun a b => by simp only [toAdd_mul]; exact (hgmul _ _).symm }
  let Φa : AddMonoidAlgebra R N →ₐ[R] C := AddMonoidAlgebra.lift R C N F
  have hΦa : ∀ a, Φa (AddMonoidAlgebra.single a 1) = g a := fun a => by simp [Φa, F]
  have hΦa_apply : ∀ p : AddMonoidAlgebra R N, Φa p = Finsupp.linearCombination R g p.coeff := by
    intro p
    rw [AddMonoidAlgebra.lift_apply, Finsupp.linearCombination_apply]
    rfl
  let Φ : AddMonoidAlgebra R N →ₐc[R] C := BialgHom.ofAlgHom Φa
    (by
      apply AddMonoidAlgebra.algHom_ext
      · intro a
        simp [hΦa, (hg a).1.counit_eq_one]
      · exact Subsingleton.elim _ _)
    (by
      apply AddMonoidAlgebra.algHom_ext
      · intro a
        simp [hΦa, (hg a).1.comul_eq_tmul_self]
      · exact Subsingleton.elim _ _)
  have hinj : Function.Injective Φa := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    rw [hΦa_apply] at hp
    have h0 : p.coeff = 0 := linearIndependent_iff.mp hgli _ hp
    ext a
    simp [h0]
  have hsurj : Function.Surjective Φa := by
    intro x
    have hx : x ∈ Submodule.span R (Set.range g) := hgsp ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
    refine ⟨AddMonoidAlgebra.ofCoeff c, ?_⟩
    rw [hΦa_apply, Finsupp.linearCombination_apply]
    exact hc
  let Ψ : AddMonoidAlgebra R N ≃ₐc[R] C := BialgEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  refine ⟨Ψ.symm, fun a => ?_⟩
  have h1 : Ψ.symm (g a) = AddMonoidAlgebra.single a 1 := by
    have : Ψ (AddMonoidAlgebra.single a 1) = g a := hΦa a
    rw [← this]
    exact Ψ.symm_apply_apply _
  have h2 := map_mem_smul_top Ψ.symm.toAlgEquiv.toLinearMap J
    (show y a - g a ∈ J • (⊤ : Submodule R C) by
      have := Submodule.neg_mem _ (hgy a)
      rwa [neg_sub] at this)
  rw [← h1]
  simpa [map_sub] using h2

/-- The comultiplication of a scalar extension `(R ⧸ J) ⊗ C` on `1 ⊗ x`. -/
theorem comul_one_tmul (J : Ideal R) (x : C) :
    comul (R := R ⧸ J) ((1 : R ⧸ J) ⊗ₜ[R] x) =
      TensorProduct.AlgebraTensorModule.distribBaseChange R (R ⧸ J) C C
        ((1 : R ⧸ J) ⊗ₜ[R] comul (R := R) x) := by
  rw [TensorProduct.comul_tmul]
  have h1 : comul (R := R ⧸ J) (1 : R ⧸ J) = 1 ⊗ₜ 1 := rfl
  rw [h1]
  generalize comul (R := R) x = t
  induction t with
  | tmul c d => simp
  | add s t hs ht => rw [TensorProduct.tmul_add, map_add, hs, ht, TensorProduct.tmul_add, map_add]

/-- **Lifting a split reduction.** Let `J` be a nilpotent ideal of `R` and `C` a flat commutative
`R`-bialgebra. If `(R ⧸ J) ⊗ C` is isomorphic as a bialgebra to the group algebra
`(R ⧸ J)[N]`, then `C` is isomorphic as a bialgebra to `R[N]`. -/
theorem exists_bialgEquiv_of_baseChange [Module.Flat R C] (J : Ideal R) (hJ : IsNilpotent J)
    {N : Type w} [AddCommMonoid N]
    (e : (R ⧸ J) ⊗[R] C ≃ₐc[R ⧸ J] AddMonoidAlgebra (R ⧸ J) N) :
    Nonempty (C ≃ₐc[R] AddMonoidAlgebra R N) := by
  classical
  choose y hy using fun a : N => exists_one_tmul_eq J (e.symm (AddMonoidAlgebra.single a 1))
  have hey : ∀ a, e ((1 : R ⧸ J) ⊗ₜ[R] y a) = AddMonoidAlgebra.single a 1 := fun a => by
    rw [hy a, BialgEquiv.apply_symm_apply]
  -- the reduction of a linear combination of the `y a`
  have hcoeff : ∀ (k : N →₀ R) (a : N),
      (e ((1 : R ⧸ J) ⊗ₜ[R] Finsupp.linearCombination R y k)).coeff a =
        Ideal.Quotient.mk J (k a) := by
    intro k
    induction k using Finsupp.induction_linear with
    | zero => intro a; simp
    | add k₁ k₂ h₁ h₂ =>
      intro a
      rw [map_add, TensorProduct.tmul_add, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
        h₁, h₂, Finsupp.add_apply, map_add]
    | single b r =>
      intro a
      rw [Finsupp.linearCombination_single, one_tmul_smul, map_smul, hey,
        AddMonoidAlgebra.smul_single', mul_one, AddMonoidAlgebra.coeff_single,
        Finsupp.single_apply, Finsupp.single_apply]
      split_ifs <;> simp
  have hsurj : ∀ t : (R ⧸ J) ⊗[R] C, ∃ k : N →₀ R,
      (1 : R ⧸ J) ⊗ₜ[R] Finsupp.linearCombination R y k = t := by
    intro t
    rw [← e.symm_apply_apply t]
    induction e t using AddMonoidAlgebra.induction_linear with
    | zero => exact ⟨0, by simp⟩
    | add p q hp hq =>
      obtain ⟨k₁, hk₁⟩ := hp
      obtain ⟨k₂, hk₂⟩ := hq
      exact ⟨k₁ + k₂, by rw [map_add, TensorProduct.tmul_add, hk₁, hk₂, map_add]⟩
    | single b r =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      refine ⟨Finsupp.single b r, ?_⟩
      rw [Finsupp.linearCombination_single, one_tmul_smul, hy b, ← map_smul,
        AddMonoidAlgebra.smul_single', mul_one]
  refine (exists_bialgEquiv_of_isNilpotent J hJ y ?_ ?_ ?_ ?_).elim fun θ _ => ⟨θ⟩
  · rw [eq_top_iff]
    intro c _
    obtain ⟨k, hk⟩ := hsurj ((1 : R ⧸ J) ⊗ₜ[R] c)
    have hd : c - Finsupp.linearCombination R y k ∈ J • (⊤ : Submodule R C) := by
      rw [← one_tmul_eq_zero_iff, TensorProduct.tmul_sub, hk, sub_self]
    have : Finsupp.linearCombination R y k + (c - Finsupp.linearCombination R y k) ∈
        Submodule.span R (Set.range y) ⊔ J • ⊤ :=
      add_mem (Submodule.mem_sup_left (by
        rw [← Finsupp.range_linearCombination]
        exact LinearMap.mem_range_self _ k)) (Submodule.mem_sup_right hd)
    rwa [add_sub_cancel] at this
  · intro k hk a
    rw [← one_tmul_eq_zero_iff] at hk
    have := hcoeff k a
    rw [hk, map_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this.symm
  · intro a
    have hg : IsGroupLikeElem (R ⧸ J) ((1 : R ⧸ J) ⊗ₜ[R] y a) := by
      rw [hy a]
      exact (AddMonoidAlgebra.isGroupLikeElem_single_one a).map e.symm
    rw [← one_tmul_eq_zero_iff]
    apply (TensorProduct.AlgebraTensorModule.distribBaseChange R (R ⧸ J) C C).injective
    rw [TensorProduct.tmul_sub, map_sub, ← comul_one_tmul, hg.comul_eq_tmul_self,
      TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, sub_self, map_zero]
  · intro a b
    rw [← one_tmul_eq_zero_iff, TensorProduct.tmul_sub]
    have hm : (1 : R ⧸ J) ⊗ₜ[R] (y a * y b) =
        ((1 : R ⧸ J) ⊗ₜ[R] y a) * ((1 : R ⧸ J) ⊗ₜ[R] y b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hm, hy a, hy b, hy (a + b), ← map_mul, AddMonoidAlgebra.single_mul_single, one_mul,
      sub_self]

end Bialgebra

end Langlands.GroupScheme.CompleteLocalDeformation
