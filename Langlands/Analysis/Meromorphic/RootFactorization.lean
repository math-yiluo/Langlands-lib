import Langlands.Analysis.Meromorphic.CoordinateGluing
import Langlands.Analysis.Meromorphic.ScalarIdentity

/-! # Finite sums of products of root factors

On a finite-dimensional complex vector space `X` with a family of linear forms `L β`, a *root
factor* on a set `D` is a scalar function that is either entire in linear coordinates, or
meromorphic in linear coordinates with domain `D` and invariant on `D` under translation by the
kernel of one form `L β` with `β` in an allowed set `R`. This module studies the functions that
agree on `D` with a finite sum of finite products of root factors: they are closed under sums,
products, shrinking of `D` and linear changes of variables that carry the kernels into kernels,
and finitely many of them admit representations with common numbers of summands and factors.

It also proves that meromorphy in linear coordinates is preserved by translations, and that a
meromorphic function which is invariant under one translation on a nonempty open set is
invariant under it on its whole domain of holomorphy. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

open scoped Manifold
open Set

section Translation

variable {m : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

/-- Meromorphy on `ℂᵐ` is preserved by translations. -/
theorem IsMeromorphicOn.comp_add_const {f : (Fin m → ℂ) → V} {U : Set (Fin m → ℂ)}
    (hf : IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) f U) (c : Fin m → ℂ) :
    IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) (fun s => f (s + c)) ((· + c) ⁻¹' U) := by
  obtain ⟨hUo, hUd, hhol, hloc⟩ := hf
  let T : (Fin m → ℂ) ≃ₜ (Fin m → ℂ) := Homeomorph.addRight c
  have hT : Differentiable ℂ (fun s : Fin m → ℂ => s + c) :=
    differentiable_id.add_const c
  refine ⟨hUo.preimage (continuous_id.add continuous_const), hUd.preimage T.isOpenMap, fun μ => ?_,
    fun s₀ => ?_⟩
  · have h := mdifferentiableOn_iff_differentiableOn.1 (hhol μ)
    exact mdifferentiableOn_iff_differentiableOn.2
      (h.comp hT.differentiableOn (mapsTo_preimage _ _))
  · obtain ⟨W, hWo, hWc, hsW, g, h, hg, ⟨s₁, hs₁W, hs₁⟩, hh, hgh⟩ := hloc (s₀ + c)
    refine ⟨(· + c) ⁻¹' W, hWo.preimage (continuous_id.add continuous_const), ?_, hsW,
      fun s => g (s + c), fun s => h (s + c), ?_, ⟨s₁ - c, by simpa using hs₁W, by simpa using hs₁⟩,
      fun μ => ?_, fun s hs => hgh _ hs⟩
    · have himage : (· + c) ⁻¹' W = (fun s => s - c) '' W := by
        ext s
        constructor
        · intro hs
          exact ⟨s + c, hs, by simp⟩
        · rintro ⟨t, ht, rfl⟩
          simpa using ht
      rw [himage]
      exact hWc.image _ (continuous_sub_right c).continuousOn
    · exact mdifferentiableOn_iff_differentiableOn.2
        ((mdifferentiableOn_iff_differentiableOn.1 hg).comp hT.differentiableOn
          (mapsTo_preimage _ _))
    · exact mdifferentiableOn_iff_differentiableOn.2
        ((mdifferentiableOn_iff_differentiableOn.1 (hh μ)).comp hT.differentiableOn
          (mapsTo_preimage _ _))

end Translation

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

/-- Meromorphy in linear coordinates is preserved by translations. -/
theorem IsMeromorphicInCoordinatesOn.comp_add_const {f : X → ℂ} {D : Set X}
    (hf : IsMeromorphicInCoordinatesOn f D) (ν : X) :
    IsMeromorphicInCoordinatesOn (fun x => f (x + ν)) ((· + ν) ⁻¹' D) := by
  refine ⟨hf.1, fun n e => ?_⟩
  have h := (hf.2 n e).comp_add_const (e.symm ν)
  have h1 : (fun x => f (x + ν)) ∘ e = fun s => (f ∘ e) (s + e.symm ν) := by
    funext s
    simp [map_add]
  have h2 : e ⁻¹' ((· + ν) ⁻¹' D) = (· + e.symm ν) ⁻¹' (e ⁻¹' D) := by
    ext s
    simp [map_add]
  rw [h1, h2]
  exact h

/-- A function meromorphic in linear coordinates that is invariant under the translation by
`ν` on the part of its domain of holomorphy over a nonempty open set of one chart is invariant
under this translation on its whole domain of holomorphy. -/
theorem IsMeromorphicInCoordinatesOn.translate_invariant_of_open {f : X → ℂ} {D : Set X}
    (hf : IsMeromorphicInCoordinatesOn f D) (ν : X) {n : ℕ} (e : (Fin n → ℂ) ≃ₗ[ℂ] X)
    {O : Set (Fin n → ℂ)} (hO : IsOpen O) (hne : O.Nonempty)
    (heq : ∀ s ∈ O, e s ∈ D → e s + ν ∈ D → f (e s + ν) = f (e s)) :
    ∀ x ∈ D, x + ν ∈ D → f (x + ν) = f x := by
  have hg := hf.comp_add_const ν
  have hE := hg.eqOn_of_eqOn_open hf e hO hne (fun s hs => by
    simpa using heq s hs.1 hs.2.2 hs.2.1)
  intro x hx hxν
  exact hE ⟨hxν, hx⟩

/-! ### Entire functions in linear coordinates -/

/-- A scalar function on `X` is entire in linear coordinates when it is complex differentiable
on `ℂᵐ` in every complex linear coordinate system `ℂᵐ ≃ X`. -/
def IsEntireInCoordinates (f : X → ℂ) : Prop :=
  ∀ (m : ℕ) (e : (Fin m → ℂ) ≃ₗ[ℂ] X), Differentiable ℂ (f ∘ e)

theorem isEntireInCoordinates_const (c : ℂ) : IsEntireInCoordinates (fun _ : X => c) :=
  fun _ _ => differentiable_const c

theorem IsEntireInCoordinates.mul {f g : X → ℂ} (hf : IsEntireInCoordinates f)
    (hg : IsEntireInCoordinates g) : IsEntireInCoordinates (fun x => f x * g x) :=
  fun m e => (hf m e).mul (hg m e)

/-- Entire functions stay entire under a linear change of variables. -/
theorem IsEntireInCoordinates.comp_linearEquiv {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    {f : Y → ℂ} (hf : IsEntireInCoordinates f) (e : X ≃ₗ[ℂ] Y) :
    IsEntireInCoordinates (f ∘ e) :=
  fun m e₀ => hf m (e₀.trans e)

/-- An entire function is meromorphic in linear coordinates with any domain of holomorphy that
is open and dense in coordinates. -/
theorem IsEntireInCoordinates.isMeromorphicInCoordinatesOn [FiniteDimensional ℂ X] {f : X → ℂ}
    (hf : IsEntireInCoordinates f) {D : Set X} (hD : IsOpenDenseInCoordinates D) :
    IsMeromorphicInCoordinatesOn f D :=
  (isMeromorphicInCoordinatesOn_univ hf).congr_mono hD (subset_univ D) fun _ _ => rfl

/-! ### Root factors -/

variable {ι : Type*}

/-- A root factor on `D` for the linear forms `L β` and the allowed indices `R`: a function that
is entire in linear coordinates, or meromorphic in linear coordinates with domain `D` and
invariant on `D` under translation by the kernel of `L β` for one `β ∈ R`. -/
def IsRootFactorOn (L : ι → X →ₗ[ℂ] ℂ) (R : Set ι) (D : Set X) (f : X → ℂ) : Prop :=
  IsEntireInCoordinates f ∨
    (IsMeromorphicInCoordinatesOn f D ∧ ∃ β ∈ R, ∀ x ∈ D, ∀ ν : X, L β ν = 0 → x + ν ∈ D →
      f (x + ν) = f x)

/-- A function has a root factorization on `D` when it agrees on `D` with a finite sum of
finite products of root factors on `D`. -/
def HasRootFactorizationOn (L : ι → X →ₗ[ℂ] ℂ) (R : Set ι) (D : Set X) (f : X → ℂ) : Prop :=
  ∃ (J n : ℕ) (fac : Fin J → Fin n → X → ℂ), (∀ j t, IsRootFactorOn L R D (fac j t)) ∧
    ∀ x ∈ D, f x = ∑ j, ∏ t, fac j t x

variable {L : ι → X →ₗ[ℂ] ℂ} {R : Set ι} {D D' : Set X} {f g : X → ℂ}

theorem IsEntireInCoordinates.isRootFactorOn (hf : IsEntireInCoordinates f) :
    IsRootFactorOn L R D f :=
  Or.inl hf

theorem isRootFactorOn_const (c : ℂ) : IsRootFactorOn L R D (fun _ => c) :=
  (isEntireInCoordinates_const c).isRootFactorOn

/-- Root factors on `D` are root factors on every part of `D` that is open and dense in
coordinates. -/
theorem IsRootFactorOn.mono (hf : IsRootFactorOn L R D f) (hD' : IsOpenDenseInCoordinates D')
    (hsub : D' ⊆ D) : IsRootFactorOn L R D' f := by
  rcases hf with hf | ⟨hm, β, hβ, hinv⟩
  · exact Or.inl hf
  · exact Or.inr ⟨hm.congr_mono hD' hsub fun _ _ => rfl, β, hβ,
      fun x hx ν hν hxν => hinv x (hsub hx) ν hν (hsub hxν)⟩

/-- Pullback of a root factor along a linear change of variables `e : X ≃ Y`: if for every
allowed form `L' β'` on `Y` there is an allowed form `L β` on `X` whose kernel `e` maps into the
kernel of `L' β'`, then `f ∘ e` is a root factor on the preimage. -/
theorem IsRootFactorOn.comp_linearEquiv {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    {κ : Type*} {L' : κ → Y →ₗ[ℂ] ℂ} {R' : Set κ} {D' : Set Y} {f : Y → ℂ}
    (hf : IsRootFactorOn L' R' D' f) (e : X ≃ₗ[ℂ] Y)
    (htrans : ∀ β' ∈ R', ∃ β ∈ R, ∀ ν : X, L β ν = 0 → L' β' (e ν) = 0) :
    IsRootFactorOn L R (e ⁻¹' D') (f ∘ e) := by
  rcases hf with hf | ⟨hm, β', hβ', hinv⟩
  · exact Or.inl (hf.comp_linearEquiv e)
  · obtain ⟨β, hβ, hker⟩ := htrans β' hβ'
    refine Or.inr ⟨hm.comp_linearEquiv e, β, hβ, fun x hx ν hν hxν => ?_⟩
    have hxν' : e x + e ν ∈ D' := by simpa [map_add] using hxν
    simpa [map_add] using hinv (e x) hx (e ν) (hker ν hν) hxν'

theorem HasRootFactorizationOn.of_isRootFactorOn (hf : IsRootFactorOn L R D f) :
    HasRootFactorizationOn L R D f :=
  ⟨1, 1, fun _ _ => f, fun _ _ => hf, fun x _ => by simp⟩

theorem hasRootFactorizationOn_zero : HasRootFactorizationOn L R D (fun _ => 0) :=
  ⟨0, 0, fun j => j.elim0, fun j => j.elim0, fun x _ => by simp⟩

theorem HasRootFactorizationOn.mono (hf : HasRootFactorizationOn L R D f)
    (hD' : IsOpenDenseInCoordinates D') (hsub : D' ⊆ D) : HasRootFactorizationOn L R D' f := by
  obtain ⟨J, n, fac, hfac, heq⟩ := hf
  exact ⟨J, n, fac, fun j t => (hfac j t).mono hD' hsub, fun x hx => heq x (hsub hx)⟩

theorem HasRootFactorizationOn.congr (hf : HasRootFactorizationOn L R D f)
    (hfg : ∀ x ∈ D, g x = f x) : HasRootFactorizationOn L R D g := by
  obtain ⟨J, n, fac, hfac, heq⟩ := hf
  exact ⟨J, n, fac, hfac, fun x hx => (hfg x hx).trans (heq x hx)⟩

theorem HasRootFactorizationOn.add (hf : HasRootFactorizationOn L R D f)
    (hg : HasRootFactorizationOn L R D g) :
    HasRootFactorizationOn L R D (fun x => f x + g x) := by
  obtain ⟨J₁, n₁, a, ha, hfa⟩ := hf
  obtain ⟨J₂, n₂, b, hb, hgb⟩ := hg
  let c : Fin (J₁ + J₂) → Fin (n₁ + n₂) → X → ℂ := fun j t =>
    Fin.addCases (fun j₁ => Fin.addCases (a j₁) (fun _ _ => 1) t)
      (fun j₂ => Fin.addCases (fun _ _ => 1) (b j₂) t) j
  refine ⟨J₁ + J₂, n₁ + n₂, c, fun j t => ?_, fun x hx => ?_⟩
  · refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j <;>
      refine Fin.addCases (fun t₁ => ?_) (fun t₂ => ?_) t <;>
      simp only [c, Fin.addCases_left, Fin.addCases_right]
    · exact ha j₁ t₁
    · exact isRootFactorOn_const 1
    · exact isRootFactorOn_const 1
    · exact hb j₂ t₂
  · show f x + g x = _
    rw [hfa x hx, hgb x hx, Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl fun j₁ _ => ?_
      simp [c, Fin.prod_univ_add]
    · refine Finset.sum_congr rfl fun j₂ _ => ?_
      simp [c, Fin.prod_univ_add]

theorem HasRootFactorizationOn.mul (hf : HasRootFactorizationOn L R D f)
    (hg : HasRootFactorizationOn L R D g) :
    HasRootFactorizationOn L R D (fun x => f x * g x) := by
  obtain ⟨J₁, n₁, a, ha, hfa⟩ := hf
  obtain ⟨J₂, n₂, b, hb, hgb⟩ := hg
  let c : Fin (J₁ * J₂) → Fin (n₁ + n₂) → X → ℂ := fun j t =>
    Fin.addCases (a (finProdFinEquiv.symm j).1) (b (finProdFinEquiv.symm j).2) t
  refine ⟨J₁ * J₂, n₁ + n₂, c, fun j t => ?_, fun x hx => ?_⟩
  · refine Fin.addCases (fun t₁ => ?_) (fun t₂ => ?_) t <;>
      simp only [c, Fin.addCases_left, Fin.addCases_right]
    · exact ha _ t₁
    · exact hb _ t₂
  · show f x * g x = _
    rw [hfa x hx, hgb x hx, Finset.sum_mul_sum, ← Finset.sum_product',
      ← finProdFinEquiv.sum_comp (fun j => ∏ t, c j t x), Finset.univ_product_univ]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [c, Fin.prod_univ_add, Equiv.symm_apply_apply, Fin.addCases_left,
      Fin.addCases_right]

theorem HasRootFactorizationOn.sum {κ : Type*} (s : Finset κ) {F : κ → X → ℂ}
    (hF : ∀ i ∈ s, HasRootFactorizationOn L R D (F i)) :
    HasRootFactorizationOn L R D (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (hasRootFactorizationOn_zero : HasRootFactorizationOn L R D _)
  | @insert i s hi ih =>
    have h := (hF i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))
    refine h.congr fun x _ => ?_
    rw [Finset.sum_insert hi]

/-- Pullback of a root factorization along a linear change of variables `e : X ≃ Y`: if for
every allowed form `L' β'` on `Y` there is an allowed form `L β` on `X` whose kernel `e` maps
into the kernel of `L' β'`, then `f ∘ e` has a root factorization on the preimage. -/
theorem HasRootFactorizationOn.comp_linearEquiv {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    {κ : Type*} {L' : κ → Y →ₗ[ℂ] ℂ} {R' : Set κ} {D' : Set Y} {f : Y → ℂ}
    (hf : HasRootFactorizationOn L' R' D' f) (e : X ≃ₗ[ℂ] Y)
    (htrans : ∀ β' ∈ R', ∃ β ∈ R, ∀ ν : X, L β ν = 0 → L' β' (e ν) = 0) :
    HasRootFactorizationOn L R (e ⁻¹' D') (f ∘ e) := by
  obtain ⟨J, n, fac, hfac, heq⟩ := hf
  exact ⟨J, n, fun j t => fac j t ∘ e, fun j t => (hfac j t).comp_linearEquiv e htrans,
    fun x hx => heq (e x) hx⟩

/-! ### Common numbers of summands and factors -/

/-- A root factorization can be written with any larger number of summands and any larger
number of factors, provided there is at least one more factor than before. -/
theorem HasRootFactorizationOn.exists_bound (hf : HasRootFactorizationOn L R D f) :
    ∃ N : ℕ, ∀ J' n' : ℕ, N ≤ J' → N ≤ n' → ∃ fac : Fin J' → Fin n' → X → ℂ,
      (∀ j t, IsRootFactorOn L R D (fac j t)) ∧ ∀ x ∈ D, f x = ∑ j, ∏ t, fac j t x := by
  classical
  obtain ⟨J, n, fac, hfac, heq⟩ := hf
  refine ⟨max J (n + 1), fun J' n' hJ hn => ?_⟩
  have hJ' : J ≤ J' := (le_max_left _ _).trans hJ
  have hn' : n + 1 ≤ n' := (le_max_right _ _).trans hn
  let fac' : Fin J' → Fin n' → X → ℂ := fun j t =>
    if hj : (j : ℕ) < J then
      (if ht : (t : ℕ) < n then fac ⟨j, hj⟩ ⟨t, ht⟩ else fun _ => 1)
    else fun _ => 0
  refine ⟨fac', fun j t => ?_, fun x hx => ?_⟩
  · simp only [fac']
    split_ifs
    · exact hfac _ _
    · exact isRootFactorOn_const 1
    · exact isRootFactorOn_const 0
  · rw [heq x hx]
    -- products
    have hprod : ∀ j : Fin J', ∏ t, fac' j t x =
        if hj : (j : ℕ) < J then ∏ t : Fin n, fac ⟨j, hj⟩ t x else 0 := by
      intro j
      by_cases hj : (j : ℕ) < J
      · simp only [hj, ↓reduceDIte]
        let G : ℕ → ℂ := fun t => if ht : t < n then fac ⟨j, hj⟩ ⟨t, ht⟩ x else 1
        have h1 : ∏ t : Fin n', fac' j t x = ∏ t : Fin n', G t := by
          refine Finset.prod_congr rfl fun t _ => ?_
          simp only [fac', hj, ↓reduceDIte, G]
          split_ifs <;> rfl
        have h2 : ∏ t : Fin n, fac ⟨j, hj⟩ t x = ∏ t : Fin n, G t := by
          refine Finset.prod_congr rfl fun t _ => ?_
          simp [G]
        rw [h1, h2, Fin.prod_univ_eq_prod_range G, Fin.prod_univ_eq_prod_range G]
        refine (Finset.prod_subset (Finset.range_subset_range.2 (by omega)) fun t ht hnt => ?_).symm
        have : ¬ t < n := by simpa using hnt
        simp [G, this]
      · simp only [hj, ↓reduceDIte]
        refine Finset.prod_eq_zero (i := ⟨0, by omega⟩) (Finset.mem_univ _) ?_
        simp [fac', hj]
    simp only [hprod]
    let H : ℕ → ℂ := fun j => if hj : j < J then ∏ t : Fin n, fac ⟨j, hj⟩ t x else 0
    have h1 : ∑ j : Fin J', (if hj : (j : ℕ) < J then ∏ t : Fin n, fac ⟨j, hj⟩ t x else 0) =
        ∑ j : Fin J', H j := rfl
    have h2 : ∑ j : Fin J, ∏ t, fac j t x = ∑ j : Fin J, H j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [H]
    rw [h1, h2, Fin.sum_univ_eq_sum_range H, Fin.sum_univ_eq_sum_range H]
    refine Finset.sum_subset (Finset.range_subset_range.2 hJ') fun j _ hnj => ?_
    have : ¬ j < J := by simpa using hnj
    simp [H, this]

/-- Finitely many functions with root factorizations on `D` have root factorizations on `D`
with common numbers of summands and of factors. -/
theorem exists_uniform_rootFactorization {k : ℕ} {coeff : Fin k → X → ℂ}
    (h : ∀ i, HasRootFactorizationOn L R D (coeff i)) :
    ∃ (J n : ℕ) (fac : Fin k → Fin J → Fin n → X → ℂ),
      (∀ i j t, IsRootFactorOn L R D (fac i j t)) ∧
        ∀ i, ∀ x ∈ D, coeff i x = ∑ j, ∏ t, fac i j t x := by
  choose N hN using fun i => (h i).exists_bound
  let M := Finset.univ.sup N
  have hM : ∀ i, N i ≤ M := fun i => Finset.le_sup (Finset.mem_univ i)
  choose fac hfac heq using fun i => hN i M M (hM i) (hM i)
  exact ⟨M, M, fac, hfac, heq⟩

end Langlands.Analysis.Meromorphic
