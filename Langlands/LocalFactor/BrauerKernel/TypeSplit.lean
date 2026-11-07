import Langlands.LocalFactor.BrauerKernel.Trace
import Langlands.LocalFactor.NonabelianBrauerPresentation
import Langlands.LocalFactor.CommonClosureSpectral
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-! # Separating an actual Brauer relation by unramified types -/

noncomputable section

universe uG uF uV

namespace Langlands.LocalFactor.BrauerKernel

/-- Geometric sequences with distinct ratios are linearly independent. -/
theorem eq_zero_of_sum_mul_pow_eq_zero {ι : Type*} [Fintype ι] (x : ι → ℂ)
    (hx : Function.Injective x) (a : ι → ℂ) (h : ∀ k : ℕ, ∑ i, a i * x i ^ k = 0) :
    ∀ i, a i = 0 := by
  let f : ι → (Multiplicative ℕ →* ℂ) := fun i => powersHom ℂ (x i)
  have hf : Function.Injective f := by
    intro i j hij
    apply hx
    have := DFunLike.congr_fun hij (Multiplicative.ofAdd 1)
    simpa [f] using this
  have hli : LinearIndependent ℂ (fun i => (f i : Multiplicative ℕ → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative ℕ) ℂ).comp f hf
  rw [Fintype.linearIndependent_iff] at hli
  apply hli a
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  simpa [f] using h (Multiplicative.toAdd k)

/-- Separation of unramified types: if exponentials of pairwise separated rates
multiply functions invariant under a translation of nonzero degree, and the sum
vanishes, then every function vanishes. -/
theorem type_separation {W : Type*} [Group W] (deg : W →* Multiplicative ℤ) (c : ℂ)
    {ι : Type*} [Fintype ι] (τ : ι → ℂ)
    (hτ : ∀ i j, i ≠ j → ∀ m : ℤ, m ≠ 0 → Complex.exp (-(τ i - τ j) * c * m) ≠ 1)
    (B : ι → W → ℂ) (n₀ : W) (hn₀ : deg n₀ ≠ 1) (hB : ∀ i w, B i (w * n₀) = B i w)
    (h : ∀ w, ∑ i, Complex.exp (-τ i * c) ^ (deg w).toAdd * B i w = 0) :
    ∀ i w, B i w = 0 := by
  intro i w
  let d : ℤ := (deg n₀).toAdd
  have hd : d ≠ 0 := by
    intro h0
    apply hn₀
    change Multiplicative.ofAdd d = 1 at *
    simp [d, h0]
  have hBk : ∀ j (k : ℕ), B j (w * n₀ ^ k) = B j w := by
    intro j k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mul_assoc, hB, ih]
  have hdeg : ∀ k : ℕ, (deg (w * n₀ ^ k)).toAdd = (deg w).toAdd + k * d := by
    intro k
    simp [d, map_mul, map_pow, toAdd_mul, toAdd_pow]
  let x : ι → ℂ := fun j => Complex.exp (-τ j * c) ^ d
  let a : ι → ℂ := fun j => Complex.exp (-τ j * c) ^ (deg w).toAdd * B j w
  have hx : Function.Injective x := by
    intro j j' hjj'
    by_contra hne
    apply hτ j j' hne d hd
    have h1 : x j / x j' = 1 := by rw [hjj', div_self (zpow_ne_zero _ (Complex.exp_ne_zero _))]
    simp only [x, ← Complex.exp_int_mul] at h1
    rw [← Complex.exp_sub] at h1
    convert h1 using 2
    ring
  have hsum : ∀ k : ℕ, ∑ j, a j * x j ^ k = 0 := by
    intro k
    have hk := h (w * n₀ ^ k)
    rw [← hk]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [a, x, hBk, hdeg]
    rw [zpow_add₀ (Complex.exp_ne_zero _), ← zpow_natCast, ← zpow_mul, mul_comm (k : ℤ) d]
    ring
  have ha := eq_zero_of_sum_mul_pow_eq_zero x hx a hsum i
  rcases mul_eq_zero.mp ha with h0 | h0
  · exact absurd h0 (zpow_ne_zero _ (Complex.exp_ne_zero _))
  · exact h0

end Langlands.LocalFactor.BrauerKernel

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

variable {G : Type uG} [Group G] (S : Subgroup G) [S.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- A character of the ambient group factors out of the Frobenius sum. -/
theorem frobeniusFunctional_mul_character (g : G) (Ω : G →* ℂˣ) (f : S → ℂ) :
    frobeniusFunctional S g (fun s => (Ω (s : G) : ℂ) * f s) =
      (Ω g : ℂ) * frobeniusFunctional S g f := by
  classical
  rw [frobeniusFunctional_apply, frobeniusFunctional_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs with hq
  · congr 1
    have hfac : ((FiniteRepresentation.Induction.factor S (q.out * g) : S) : G) =
        q.out * g * q.out⁻¹ := by
      change q.out * g * (FiniteRepresentation.Induction.coset S (q.out * g)).out⁻¹ = _
      rw [hq]
    rw [hfac, map_mul, map_mul, map_inv, mul_comm (Ω q.out), mul_assoc, mul_inv_cancel,
      mul_one]
  · simp

/-- Right translation by a normal subgroup of the inducing subgroup, on which the
function is invariant, does not change the Frobenius sum. -/
theorem frobeniusFunctional_mul_right (N : Subgroup G) [N.Normal] (hN : N ≤ S)
    (f : S → ℂ) (hf : ∀ (s : S) (n : G) (hn : n ∈ N), f (s * ⟨n, hN hn⟩) = f s)
    (g n : G) (hn : n ∈ N) :
    frobeniusFunctional S (g * n) f = frobeniusFunctional S g f := by
  classical
  rw [frobeniusFunctional_apply, frobeniusFunctional_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hc : FiniteRepresentation.Induction.coset S (q.out * (g * n)) =
      FiniteRepresentation.Induction.coset S (q.out * g) := by
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    apply hN
    have : q.out * g * (q.out * (g * n))⁻¹ = (q.out * g) * n⁻¹ * (q.out * g)⁻¹ := by group
    rw [this]
    exact Subgroup.Normal.conj_mem inferInstance _ (N.inv_mem hn) _
  rw [hc]
  split_ifs with hq
  · obtain ⟨c, hcdef⟩ : ∃ c, c = FiniteRepresentation.Induction.coset S (q.out * g) :=
      ⟨_, rfl⟩
    have hm : c.out * n * c.out⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance _ hn _
    have hfac : FiniteRepresentation.Induction.factor S (q.out * (g * n)) =
        FiniteRepresentation.Induction.factor S (q.out * g) * ⟨_, hN hm⟩ := by
      apply Subtype.ext
      change q.out * (g * n) *
          (FiniteRepresentation.Induction.coset S (q.out * (g * n))).out⁻¹ =
        q.out * g * (FiniteRepresentation.Induction.coset S (q.out * g)).out⁻¹ *
          (c.out * n * c.out⁻¹)
      rw [hc, ← hcdef]
      group
    rw [hfac, hf _ _ hm]
  · rfl

end Langlands.VirtualRepresentation.ExactGrothendieckGroup

namespace Langlands.LocalFactor.NonabelianBrauer

open CommonClosure VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The subgroup `W_L ∩ W_E` of `W_E` attached to a generator. -/
abbrev Generator.nested {E : Extension F} (g : Generator F E) :
    Subgroup (weilSubgroup F E) :=
  (weilSubgroup F g.extension).subgroupOf (weilSubgroup F E)

/-- The Frobenius sum at `w ∈ W_E` of a character of the generator's Weil subgroup. -/
def frobeniusSum {E : Extension F} (g : Generator F E)
    (ψ : weilSubgroup F g.extension →* ℂˣ) (w : weilSubgroup F E) : ℂ :=
  ExactGrothendieckGroup.frobeniusFunctional g.nested w
    (fun s => (ψ (nestedWeilEquiv F E g.extension g.inclusion s) : ℂ))

/-- The trace of an actual generator class is the difference of two Frobenius sums. -/
theorem trace_generatorClass (e : ReciprocityFamily F) (E : Extension F)
    (g : Generator F E) (w : weilSubgroup F E) :
    ExactGrothendieckGroup.trace (ContinuousPredicate F E)
        (generatorClass.{uF, uV} F e E g) w =
      frobeniusSum F g (weilCharacter F e g.extension g.first).toMonoidHom w -
        frobeniusSum F g (weilCharacter F e g.extension g.second).toMonoidHom w := by
  rw [generatorClass, CommonClosure.trace_induce, map_sub, characterClass, characterClass,
    ExactGrothendieckGroup.trace_characterClass, ExactGrothendieckGroup.trace_characterClass,
    frobeniusSum, frobeniusSum, ← map_sub]
  rfl

/-- A field character's Weil character divided by the base-degree twist with exponent `t`. -/
def twistedWeilCharacter (e : ReciprocityFamily F) (L : Extension F)
    (χ : FieldCharacter F L) (t : ℂ) : weilSubgroup F L →* ℂˣ :=
  (weilCharacter F e L χ).toMonoidHom * (CommonClosureSpectral.character F L (-t)).toMonoidHom

theorem character_neg_mul (L : Extension F) (t : ℂ) (v : weilSubgroup F L) :
    (CommonClosureSpectral.character F L (-t) v : ℂ) *
      (CommonClosureSpectral.character F L t v : ℂ) = 1 := by
  rw [CommonClosureSpectral.character_apply, CommonClosureSpectral.character_apply,
    ← mul_zpow, ← Complex.exp_add]
  simp

theorem weilCharacter_eq_twisted (e : ReciprocityFamily F) (L : Extension F)
    (χ : FieldCharacter F L) (t : ℂ) (v : weilSubgroup F L) :
    (weilCharacter F e L χ v : ℂ) =
      (CommonClosureSpectral.character F L t v : ℂ) * (twistedWeilCharacter F e L χ t v : ℂ) := by
  change _ = _ * ((weilCharacter F e L χ v : ℂ) * (CommonClosureSpectral.character F L (-t) v : ℂ))
  rw [mul_comm (weilCharacter F e L χ v : ℂ), ← mul_assoc, mul_comm _ (CommonClosureSpectral.character F L (-t) v : ℂ),
    character_neg_mul, one_mul]

/-- The base-degree twist does not depend on the ambient intermediate field. -/
theorem character_nested (E L : Extension F) (h : E.field ≤ L.field) (t : ℂ)
    (s : (weilSubgroup F L).subgroupOf (weilSubgroup F E)) :
    (CommonClosureSpectral.character F L t (nestedWeilEquiv F E L h s) : ℂ) =
      (CommonClosureSpectral.character F E t (s : weilSubgroup F E) : ℂ) := by
  rw [CommonClosureSpectral.character_apply, CommonClosureSpectral.character_apply]
  rfl

/-- Frobenius sums of Weil characters split off the base-degree twist. -/
theorem frobeniusSum_weilCharacter (e : ReciprocityFamily F) {E : Extension F}
    (g : Generator F E) (χ : FieldCharacter F g.extension) (t : ℂ) (w : weilSubgroup F E) :
    frobeniusSum F g (weilCharacter F e g.extension χ).toMonoidHom w =
      (CommonClosureSpectral.character F E t w : ℂ) *
        frobeniusSum F g (twistedWeilCharacter F e g.extension χ t) w := by
  unfold frobeniusSum
  refine Eq.trans ?_ (ExactGrothendieckGroup.frobeniusFunctional_mul_character g.nested w
    (CommonClosureSpectral.character F E t).toMonoidHom _)
  congr 1
  funext s
  change (weilCharacter F e g.extension χ _ : ℂ) = _
  rw [weilCharacter_eq_twisted F e g.extension χ t, character_nested]
  rfl

/-- Right translation by a normal subgroup on which the character is trivial does not
change a Frobenius sum. -/
theorem frobeniusSum_mul_right {E : Extension F} (g : Generator F E)
    (ψ : weilSubgroup F g.extension →* ℂˣ) (N : Subgroup (weilSubgroup F E)) [N.Normal]
    (hN : N ≤ g.nested)
    (hψ : ∀ (n : weilSubgroup F E) (hn : n ∈ N),
      ψ (nestedWeilEquiv F E g.extension g.inclusion ⟨n, hN hn⟩) = 1)
    (w n : weilSubgroup F E) (hn : n ∈ N) :
    frobeniusSum F g ψ (w * n) = frobeniusSum F g ψ w := by
  unfold frobeniusSum
  apply ExactGrothendieckGroup.frobeniusFunctional_mul_right g.nested N hN
  · intro s m hm
    rw [map_mul, map_mul, hψ m hm, mul_one]
  · exact hn

open Classical in
/-- The component of a presentation in the unramified type `τ`, for chosen exponents
of the first and second characters of every generator. -/
def typeComponent (e : ReciprocityFamily F) {E : Extension F} (z : Presentation F E)
    (t₁ t₂ : Generator F E → ℂ) (τ : ℂ) (w : weilSubgroup F E) : ℂ :=
  ∑ g ∈ z.support, (z g : ℂ) *
    ((if t₁ g = τ then frobeniusSum F g (twistedWeilCharacter F e g.extension g.first (t₁ g)) w
      else 0) -
     (if t₂ g = τ then frobeniusSum F g (twistedWeilCharacter F e g.extension g.second (t₂ g)) w
      else 0))

/-- The trace of an actual presentation, generator by generator. -/
theorem trace_virtualPresentation_apply (e : ReciprocityFamily F) (E : Extension F)
    (z : Presentation F E) (w : weilSubgroup F E) :
    ExactGrothendieckGroup.trace (ContinuousPredicate F E)
        (virtualPresentation.{uF, uV} F e E z) w =
      ∑ g ∈ z.support, (z g : ℂ) *
        (frobeniusSum F g (weilCharacter F e g.extension g.first).toMonoidHom w -
          frobeniusSum F g (weilCharacter F e g.extension g.second).toMonoidHom w) := by
  rw [virtualPresentation, Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_zsmul, Pi.smul_apply, trace_generatorClass, zsmul_eq_mul]

open Classical in
/-- Regrouping the generator traces by the chosen exponents. -/
theorem trace_eq_sum_typeComponent (e : ReciprocityFamily F) (E : Extension F)
    (z : Presentation F E) (t₁ t₂ : Generator F E → ℂ) (w : weilSubgroup F E) :
    ∑ g ∈ z.support, (z g : ℂ) *
        (frobeniusSum F g (weilCharacter F e g.extension g.first).toMonoidHom w -
          frobeniusSum F g (weilCharacter F e g.extension g.second).toMonoidHom w) =
      ∑ τ ∈ z.support.image t₁ ∪ z.support.image t₂,
        (CommonClosureSpectral.character F E τ w : ℂ) * typeComponent F e z t₁ t₂ τ w := by
  simp only [typeComponent, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g hg => ?_
  have h₁ : t₁ g ∈ z.support.image t₁ ∪ z.support.image t₂ :=
    Finset.mem_union_left _ (Finset.mem_image_of_mem t₁ hg)
  have h₂ : t₂ g ∈ z.support.image t₁ ∪ z.support.image t₂ :=
    Finset.mem_union_right _ (Finset.mem_image_of_mem t₂ hg)
  rw [frobeniusSum_weilCharacter F e g g.first (t₁ g),
    frobeniusSum_weilCharacter F e g g.second (t₂ g)]
  simp only [mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib]
  rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp only [h₁, h₂, ↓reduceIte]
  ring

/-- An element of nonzero base degree in every finite-index subgroup of `W_E`. -/
theorem exists_mem_baseDegree_ne_one (E : Extension F) (N : Subgroup (weilSubgroup F E))
    [N.FiniteIndex] : ∃ n ∈ N, CommonClosureSpectral.baseDegree F E n ≠ 1 := by
  obtain ⟨x, hx⟩ := Weil.Local.localDegree_surjective F (Multiplicative.ofAdd (1 : ℤ))
  obtain ⟨k, hk, -, hkmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := weilSubgroup F E)) x
  let y : weilSubgroup F E := ⟨x ^ k, hkmem⟩
  obtain ⟨m, hm, -, hmmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := N)) y
  refine ⟨y ^ m, hmmem, ?_⟩
  change Weil.Local.localDegree F ((x ^ k) ^ m) ≠ 1
  rw [map_pow, map_pow, hx, ← ofAdd_nsmul, ← ofAdd_nsmul]
  intro h
  have h' := congrArg Multiplicative.toAdd h
  simp only [toAdd_ofAdd, toAdd_one, nsmul_eq_mul, mul_one, mul_eq_zero,
    Nat.cast_eq_zero] at h'
  omega

open Classical in
/-- **Type separation of actual Brauer relations.** Suppose the first and second
characters of every generator are written as twisted characters times base-degree
twists with exponents `t₁` and `t₂`, that all twisted characters are trivial on a
finite-index normal subgroup `N`, and that any two distinct exponents are not
congruent modulo `2πi/log q_F · ℚ`. Then every type component of an actual relation
vanishes identically on `W_E`. -/
theorem typeComponent_eq_zero (e : ReciprocityFamily F) (E : Extension F)
    (z : Presentation F E) (hz : presentationMap.{uF, uV} F e E z = 0)
    (t₁ t₂ : Generator F E → ℂ) (N : Subgroup (weilSubgroup F E)) [N.Normal]
    [N.FiniteIndex] (hNle : ∀ g ∈ z.support, N ≤ g.nested)
    (htriv₁ : ∀ (g : Generator F E) (hg : g ∈ z.support) (n : weilSubgroup F E)
      (hn : n ∈ N), twistedWeilCharacter F e g.extension g.first (t₁ g)
        (nestedWeilEquiv F E g.extension g.inclusion ⟨n, hNle g hg hn⟩) = 1)
    (htriv₂ : ∀ (g : Generator F E) (hg : g ∈ z.support) (n : weilSubgroup F E)
      (hn : n ∈ N), twistedWeilCharacter F e g.extension g.second (t₂ g)
        (nestedWeilEquiv F E g.extension g.inclusion ⟨n, hNle g hg hn⟩) = 1)
    (hsep : ∀ τ ∈ z.support.image t₁ ∪ z.support.image t₂,
      ∀ τ' ∈ z.support.image t₁ ∪ z.support.image t₂, τ ≠ τ' → ∀ m : ℤ, m ≠ 0 →
        Complex.exp (-(τ - τ') *
          (Real.log (CommonClosureSpectral.baseCardinality F) : ℂ) * m) ≠ 1) :
    ∀ τ w, typeComponent F e z t₁ t₂ τ w = 0 := by
  let T := z.support.image t₁ ∪ z.support.image t₂
  have hvp : virtualPresentation.{uF, uV} F e E z = 0 := congrArg Subtype.val hz
  have hsum : ∀ w, ∑ τ ∈ T, (CommonClosureSpectral.character F E τ w : ℂ) *
      typeComponent F e z t₁ t₂ τ w = 0 := by
    intro w
    rw [← trace_eq_sum_typeComponent, ← trace_virtualPresentation_apply.{uF, uV}, hvp,
      map_zero]
    rfl
  obtain ⟨n₀, hn₀N, hn₀⟩ := exists_mem_baseDegree_ne_one F E N
  have hinv : ∀ τ w, typeComponent F e z t₁ t₂ τ (w * n₀) = typeComponent F e z t₁ t₂ τ w := by
    intro τ w
    unfold typeComponent
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [frobeniusSum_mul_right F g _ N (hNle g hg) (htriv₁ g hg) w n₀ hn₀N,
      frobeniusSum_mul_right F g _ N (hNle g hg) (htriv₂ g hg) w n₀ hn₀N]
  intro τ w
  by_cases hτ : τ ∈ T
  · have key := BrauerKernel.type_separation
      (CommonClosureSpectral.baseDegree F E).toMonoidHom
      (Real.log (CommonClosureSpectral.baseCardinality F) : ℂ)
      (fun i : T => (i : ℂ))
      (fun i j hij m hm => hsep i i.property j j.property
        (fun h => hij (Subtype.ext h)) m hm)
      (fun i w => typeComponent F e z t₁ t₂ i w) n₀ hn₀
      (fun i w => hinv i w)
      (fun w => by
        rw [← hsum w, ← Finset.sum_coe_sort T]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [CommonClosureSpectral.character_apply]
        rfl)
    exact key ⟨τ, hτ⟩ w
  · unfold typeComponent
    refine Finset.sum_eq_zero fun g hg => ?_
    have h₁ : t₁ g ≠ τ := fun h => hτ (h ▸ Finset.mem_union_left _ (Finset.mem_image_of_mem t₁ hg))
    have h₂ : t₂ g ≠ τ := fun h => hτ (h ▸ Finset.mem_union_right _ (Finset.mem_image_of_mem t₂ hg))
    simp [h₁, h₂]

end Langlands.LocalFactor.NonabelianBrauer
