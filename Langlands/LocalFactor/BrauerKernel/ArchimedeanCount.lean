import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-! # Counting real places and regrouping products by types -/

noncomputable section

set_option autoImplicit false

namespace Langlands.LocalFactor.NonabelianBrauer

open NumberField NumberField.InfinitePlace

section Regroup

variable {G : Type*} [CommGroup G] {ι : Type*}

theorem prod_zpow_eq_zpow_sum' (s : Finset ι) (f : ι → ℤ) (a : G) :
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, zpow_add]

/-- **Regrouping by types.** Let `g ↦ (t₁ g, t₂ g)` be pairs of types with integer weights `e g`,
and let the weighted type counts vanish: `Σ_g e g ([t₁ g = τ] - [t₂ g = τ]) = 0` for every type
`τ`. Then `Π_g (h (t₁ g) / h (t₂ g)) ^ e g = 1` for every map `h` from types to a commutative
group. -/
theorem prod_types_eq_one {T : Type*} [DecidableEq T] (S : Finset ι) (e : ι → ℤ)
    (t₁ t₂ : ι → T) (h : T → G)
    (hdim : ∀ τ, ∑ g ∈ S, e g * ((if t₁ g = τ then 1 else 0) - (if t₂ g = τ then 1 else 0)) = 0) :
    ∏ g ∈ S, (h (t₁ g) * (h (t₂ g))⁻¹) ^ e g = 1 := by
  classical
  let U : Finset T := S.image t₁ ∪ S.image t₂
  have hfac : ∀ g ∈ S, (h (t₁ g) * (h (t₂ g))⁻¹) ^ e g =
      ∏ τ ∈ U, h τ ^ (e g * ((if t₁ g = τ then 1 else 0) - (if t₂ g = τ then 1 else 0))) := by
    intro g hg
    have h1 : t₁ g ∈ U := Finset.mem_union_left _ (Finset.mem_image_of_mem _ hg)
    have h2 : t₂ g ∈ U := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hg)
    have hsplit : ∀ τ ∈ U, h τ ^ (e g * ((if t₁ g = τ then 1 else 0) -
        (if t₂ g = τ then 1 else 0))) =
        (if t₁ g = τ then h τ ^ e g else 1) * (if t₂ g = τ then (h τ ^ e g)⁻¹ else 1) := by
      intro τ _
      split_ifs <;> simp [zpow_neg]
    rw [Finset.prod_congr rfl hsplit, Finset.prod_mul_distrib, Finset.prod_ite_eq U (t₁ g),
      Finset.prod_ite_eq U (t₂ g)]
    simp only [h1, h2, ↓reduceIte, mul_zpow, inv_zpow]
  rw [Finset.prod_congr rfl hfac, Finset.prod_comm]
  refine Finset.prod_eq_one fun τ _ => ?_
  rw [prod_zpow_eq_zpow_sum', hdim τ, zpow_zero]

/-- **Regrouping powers over places by types.** With the hypothesis of `prod_types_eq_one`
for the weights `e i * N i`, a product over `i` of quotients of `N i`-th powers of products over a
finite type `ρ` of values depending only on the types is `1`. -/
theorem prod_types_pow_eq_one {T ρ : Type*} [DecidableEq T] [Fintype ρ] (S : Finset ι)
    (e : ι → ℤ) (N : ι → ℕ) (t₁ t₂ : ι → T) (h : T → ρ → G)
    (hdim : ∀ τ, ∑ g ∈ S, e g * N g * ((if t₁ g = τ then 1 else 0) -
      (if t₂ g = τ then 1 else 0)) = 0) :
    ∏ i ∈ S, ((∏ r, h (t₁ i) r ^ N i) * (∏ r, h (t₂ i) r ^ N i)⁻¹) ^ e i = 1 := by
  have hfac : ∀ i ∈ S, ((∏ r, h (t₁ i) r ^ N i) * (∏ r, h (t₂ i) r ^ N i)⁻¹) ^ e i =
      ∏ r, (h (t₁ i) r * (h (t₂ i) r)⁻¹) ^ (e i * N i) := by
    intro i _
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [← inv_pow, ← mul_pow, ← zpow_natCast, ← zpow_mul, mul_comm (N i : ℤ)]
  rw [Finset.prod_congr rfl hfac, Finset.prod_comm]
  exact Finset.prod_eq_one fun r _ =>
    prod_types_eq_one S (fun i => e i * N i) t₁ t₂ (fun τ => h τ r) hdim

end Regroup

section Count

open scoped Classical

variable {k M : Type*} [Field k] [Field M] [NumberField k] [NumberField M] [Algebra k M]

/-- The real place below a real place. -/
def realComap (u : {u : InfinitePlace M // u.IsReal}) : {r : InfinitePlace k // r.IsReal} :=
  ⟨u.1.comap (algebraMap k M), u.2.comap _⟩

/-- In a totally real extension, each real place has exactly `[M : k]` real places above it. -/
theorem card_realComap_fiber [IsTotallyReal M] (r : {r : InfinitePlace k // r.IsReal}) :
    (Finset.univ.filter fun u : {u : InfinitePlace M // u.IsReal} =>
      realComap u = r).card = Module.finrank k M := by
  classical
  have hcount := unramifedPlacesOver_ncard_add_eq_finrank (L := M) r.1
  have hram : ramifiedPlacesOver M r.1 = ∅ := by
    ext w
    simp only [ramifiedPlacesOver, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
      not_and]
    intro _ hw
    exact hw (isUnramified_iff.mpr (Or.inl (IsTotallyReal.isReal w)))
  rw [hram, Set.ncard_empty, mul_zero, add_zero] at hcount
  rw [← hcount, ← Set.ncard_coe_finset]
  refine Set.ncard_congr (fun u _ => u.1) ?_ ?_ ?_
  · intro u hu
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu
    refine ⟨?_, isUnramified_iff.mpr (Or.inl u.2)⟩
    have hu' : u.1.comap (algebraMap k M) = r.1 := congrArg Subtype.val hu
    rw [← hu']
    exact ⟨rfl⟩
  · intro u₁ u₂ _ _ h
    exact Subtype.ext h
  · intro w hw
    refine ⟨⟨w, IsTotallyReal.isReal w⟩, ?_, rfl⟩
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    apply Subtype.ext
    exact @LiesOver.comap_eq _ _ _ _ _ w r.1 hw.1

/-- In a totally real extension, a product over the real places of `M` of a function of the
place below is the product over the real places of `k` of its `[M : k]`-th powers. -/
theorem prod_realComap [IsTotallyReal M] {G : Type*} [CommMonoid G]
    (f : {r : InfinitePlace k // r.IsReal} → G) :
    ∏ u : {u : InfinitePlace M // u.IsReal}, f (realComap u) =
      ∏ r : {r : InfinitePlace k // r.IsReal}, f r ^ Module.finrank k M := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ (realComap (k := k) (M := M))
    (fun u => f (realComap u))]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [Finset.prod_congr rfl (fun u hu => by rw [(Finset.mem_filter.mp hu).2]),
    Finset.prod_const, card_realComap_fiber]

end Count

end Langlands.LocalFactor.NonabelianBrauer
