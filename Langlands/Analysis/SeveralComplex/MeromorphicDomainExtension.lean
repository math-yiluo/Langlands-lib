import Langlands.Analysis.Meromorphic.LinearCoordinates
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! # Enlarging the domain of holomorphy of a meromorphic function

A scalar meromorphic function on a finite-dimensional complex vector space
(`IsMeromorphicInCoordinatesOn`) that admits, near every point of a set `Λ`, a
holomorphic function agreeing with it on its domain of holomorphy, is the same
meromorphic function as one whose domain of holomorphy contains `Λ`. The
statement is uniform in a family of functions indexed by a type `Γ`: the
neighbourhoods of the points of `Λ` may not depend on the index. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

open scoped Manifold
open Set Topology

section Coordinates

variable {n m : ℕ}

/-- For scalar functions on `ℂⁿ`, holomorphy in the sense of `IsHolomorphicOn` is complex
differentiability. -/
theorem isHolomorphicOn_iff_differentiableOn (f : (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ)) :
    IsHolomorphicOn 𝓘(ℂ, Fin n → ℂ) f U ↔ DifferentiableOn ℂ f U := by
  constructor
  · intro h
    have h1 := h (ContinuousLinearMap.id ℂ ℂ)
    rw [mdifferentiableOn_iff_differentiableOn] at h1
    simpa using h1
  · intro h μ
    rw [mdifferentiableOn_iff_differentiableOn]
    exact μ.differentiable.comp_differentiableOn h

/-- Meromorphy on `ℂⁿ` is invariant under continuous linear changes of coordinates. -/
theorem IsMeromorphicOn.comp_continuousLinearEquiv_scalar {f : (Fin n → ℂ) → ℂ}
    {U : Set (Fin n → ℂ)} (hf : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f U)
    (L : (Fin m → ℂ) ≃L[ℂ] (Fin n → ℂ)) :
    IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) (f ∘ L) (L ⁻¹' U) := by
  obtain ⟨hUo, hUd, hhol, hloc⟩ := hf
  refine ⟨hUo.preimage L.continuous, hUd.preimage L.toHomeomorph.isOpenMap, ?_, ?_⟩
  · rw [isHolomorphicOn_iff_differentiableOn] at hhol ⊢
    exact hhol.comp L.differentiableOn (fun x hx => hx)
  · intro s₀
    obtain ⟨W, hWo, hWc, hsW, g, h, hg, ⟨s, hsW', hgs⟩, hh, hgh⟩ := hloc (L s₀)
    refine ⟨L ⁻¹' W, hWo.preimage L.continuous, ?_, hsW, g ∘ L, h ∘ L,
      (hg.differentiableOn.comp L.differentiableOn (fun x hx => hx)).mdifferentiableOn,
      ⟨L.symm s, by simpa using hsW', by simpa using hgs⟩, ?_, ?_⟩
    · rw [← L.image_symm_eq_preimage]
      exact hWc.image _ L.symm.continuous.continuousOn
    · rw [isHolomorphicOn_iff_differentiableOn] at hh ⊢
      exact hh.comp L.differentiableOn (fun x hx => hx)
    · intro x hx
      exact hgh (L x) hx

/-- A function on a complex vector space is meromorphic in linear coordinates as soon as it is
meromorphic in one linear coordinate system. -/
theorem isMeromorphicInCoordinatesOn_of_scalarCoordinates {X : Type*} [AddCommGroup X] [Module ℂ X]
    {f : X → ℂ} {U : Set X} {n₀ : ℕ} (e₀ : (Fin n₀ → ℂ) ≃ₗ[ℂ] X)
    (h : IsMeromorphicOn 𝓘(ℂ, Fin n₀ → ℂ) (f ∘ e₀) (e₀ ⁻¹' U)) :
    IsMeromorphicInCoordinatesOn f U := by
  refine ⟨LinearEquiv.finiteDimensional e₀, fun n e => ?_⟩
  let L : (Fin n → ℂ) ≃L[ℂ] (Fin n₀ → ℂ) := (e.trans e₀.symm).toContinuousLinearEquiv
  have hL := h.comp_continuousLinearEquiv_scalar L
  have h1 : (f ∘ e₀) ∘ L = f ∘ e := by
    funext s
    simp [L]
  have h2 : L ⁻¹' (e₀ ⁻¹' U) = e ⁻¹' U := by
    ext s
    simp [L]
  rw [h1, h2] at hL
  exact hL

/-- A meromorphic function stays meromorphic when its domain of holomorphy `U` is enlarged to
an open set `U'` on which a holomorphic function `f'` agreeing with `f` on `U` is given. -/
theorem IsMeromorphicOn.of_extension {f f' : (Fin n → ℂ) → ℂ} {U U' : Set (Fin n → ℂ)}
    (hf : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f U) (hUU' : U ⊆ U') (hU' : IsOpen U')
    (hf' : DifferentiableOn ℂ f' U') (hff' : ∀ s ∈ U, f' s = f s) :
    IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f' U' := by
  obtain ⟨hUo, hUd, _, hloc⟩ := hf
  refine ⟨hU', hUd.mono hUU', (isHolomorphicOn_iff_differentiableOn _ _).2 hf', ?_⟩
  intro s₀
  obtain ⟨W, hWo, hWc, hsW, g, h, hg, hgne, hh, hgh⟩ := hloc s₀
  refine ⟨W, hWo, hWc, hsW, g, h, hg, hgne, hh, ?_⟩
  rw [isHolomorphicOn_iff_differentiableOn] at hh
  have hEq : EqOn (fun s => g s • f' s) h (U' ∩ W ∩ U) := by
    intro s hs
    simp only
    rw [hff' s hs.2]
    exact hgh s ⟨hs.2, hs.1.2⟩
  have hfin := hEq.of_subset_closure
    (ContinuousOn.smul (hg.differentiableOn.mono inter_subset_right).continuousOn
      (hf'.mono inter_subset_left).continuousOn)
    (hh.mono inter_subset_right).continuousOn inter_subset_left
    (hUd.open_subset_closure_inter (hU'.inter hWo))
  intro s hs
  exact hfin ⟨hs.1, hs.2⟩

end Coordinates

section Gluing

variable {n : ℕ} {Γ : Type*}

open Classical in
/-- Gluing in fixed coordinates: a family `E · g` holomorphic on a dense open `D`, together with
holomorphic functions `h i g` on open sets `W i` agreeing with `E · g` on `W i ∩ D`, has a
common holomorphic extension to `D ∪ ⋃ i, W i`, equal to `E` on `D` and outside `⋃ i, W i`. -/
theorem exists_differentiableOn_union_extension (E : (Fin n → ℂ) → Γ → ℂ)
    {D : Set (Fin n → ℂ)} (hDo : IsOpen D) (hDd : Dense D)
    (hE : ∀ g, DifferentiableOn ℂ (fun s => E s g) D)
    {ι : Type*} (W : ι → Set (Fin n → ℂ)) (hW : ∀ i, IsOpen (W i))
    (h : ι → Γ → (Fin n → ℂ) → ℂ) (hh : ∀ i g, DifferentiableOn ℂ (h i g) (W i))
    (hhE : ∀ i g, ∀ s ∈ W i, s ∈ D → h i g s = E s g) :
    ∃ E' : (Fin n → ℂ) → Γ → ℂ,
      (∀ g, DifferentiableOn ℂ (fun s => E' s g) (D ∪ ⋃ i, W i)) ∧ (∀ s ∈ D, E' s = E s) ∧
        ∀ s, (∀ i, s ∉ W i) → E' s = E s := by
  let E' : (Fin n → ℂ) → Γ → ℂ := fun s g =>
    if s ∈ D then E s g else if hs : ∃ i, s ∈ W i then h (Classical.choose hs) g s else E s g
  -- two local extensions agree on the overlap of their domains
  have hagree : ∀ i j g, EqOn (h i g) (h j g) (W i ∩ W j) := by
    intro i j g
    have hEq : EqOn (h i g) (h j g) (W i ∩ W j ∩ D) := by
      intro s hs
      rw [hhE i g s hs.1.1 hs.2, hhE j g s hs.1.2 hs.2]
    exact hEq.of_subset_closure ((hh i g).mono inter_subset_left).continuousOn
      ((hh j g).mono inter_subset_right).continuousOn inter_subset_left
      (hDd.open_subset_closure_inter ((hW i).inter (hW j)))
  have hEW : ∀ i g, ∀ s ∈ W i, E' s g = h i g s := by
    intro i g s hs
    by_cases hD : s ∈ D
    · simp only [E', hD, ite_true]
      exact (hhE i g s hs hD).symm
    · have hex : ∃ i, s ∈ W i := ⟨i, hs⟩
      simp only [E', hD, ite_false, hex, dite_true]
      exact hagree _ i g ⟨Classical.choose_spec hex, hs⟩
  have hED : ∀ g, ∀ s ∈ D, E' s g = E s g := by
    intro g s hs
    simp only [E', hs, ite_true]
  refine ⟨E', fun g => ?_, fun s hs => funext fun g => hED g s hs, ?_⟩
  · intro s hs
    apply DifferentiableAt.differentiableWithinAt
    rcases hs with hs | hs
    · have hev : (fun t => E' t g) =ᶠ[𝓝 s] fun t => E t g :=
        Filter.eventuallyEq_of_mem (hDo.mem_nhds hs) (fun t ht => hED g t ht)
      exact ((hE g).differentiableAt (hDo.mem_nhds hs)).congr_of_eventuallyEq hev
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hs
      have hev : (fun t => E' t g) =ᶠ[𝓝 s] h i g :=
        Filter.eventuallyEq_of_mem ((hW i).mem_nhds hi) (fun t ht => hEW i g t ht)
      exact ((hh i g).differentiableAt ((hW i).mem_nhds hi)).congr_of_eventuallyEq hev
  · intro s hs
    funext g
    have hex : ¬ ∃ i, s ∈ W i := fun ⟨i, hi⟩ => hs i hi
    by_cases hD : s ∈ D
    · simp only [E', hD, ite_true]
    · simp only [E', hD, ite_false, hex, dite_false]

/-- **Enlarging the domain of holomorphy.** Let `E λ g` be meromorphic in `λ ∈ X` with one domain
of holomorphy `D` for every `g ∈ Γ`, and let `O ⊆ X`. Suppose that for every `λ₀ ∈ Λ` there are
linear coordinates `e` and one open neighbourhood `W` of `e⁻¹ λ₀` with `e(W) ⊆ O` such that, for
every `g`, some holomorphic function on `W` agrees with `E (e ·) g` on `W ∩ e⁻¹ D`. Then there
are `E'` and `D' ⊇ D ∪ Λ` such that `E' · g` is meromorphic with domain of holomorphy `D'` for
every `g`, and `E' = E` on `D` and outside `O`. -/
theorem exists_isMeromorphicInCoordinatesOn_extension {X : Type*} [AddCommGroup X] [Module ℂ X]
    (E : X → Γ → ℂ) (D : Set X)
    (hE : ∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D) (O Λ : Set X)
    (hloc : ∀ lam₀ ∈ Λ, ∃ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] X) (W : Set (Fin n → ℂ)),
      IsOpen W ∧ e.symm lam₀ ∈ W ∧ e '' W ⊆ O ∧ ∀ g, ∃ h : (Fin n → ℂ) → ℂ,
        DifferentiableOn ℂ h W ∧ ∀ s ∈ W, e s ∈ D → h s = E (e s) g) :
    ∃ (E' : X → Γ → ℂ) (D' : Set X), Λ ⊆ D' ∧ D ⊆ D' ∧
      (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E' lam g) D') ∧
      (∀ lam ∈ D, E' lam = E lam) ∧ ∀ lam ∉ O, E' lam = E lam := by
  rcases isEmpty_or_nonempty Γ with hΓ | ⟨⟨g₀⟩⟩
  · exact ⟨E, univ, subset_univ _, subset_univ _, fun g => isEmptyElim g, fun _ _ => rfl,
      fun _ _ => rfl⟩
  have : FiniteDimensional ℂ X := (hE g₀).1
  let n₀ := Module.finrank ℂ X
  let e₀ : (Fin n₀ → ℂ) ≃ₗ[ℂ] X := (Module.finBasis ℂ X).equivFun.symm
  let D₀ : Set (Fin n₀ → ℂ) := e₀ ⁻¹' D
  have hmer : ∀ g, IsMeromorphicOn 𝓘(ℂ, Fin n₀ → ℂ) (fun s => E (e₀ s) g) D₀ :=
    fun g => (hE g).2 n₀ e₀
  have hD₀o : IsOpen D₀ := (hmer g₀).1
  have hD₀d : Dense D₀ := (hmer g₀).2.1
  have hEhol : ∀ g, DifferentiableOn ℂ (fun s => E (e₀ s) g) D₀ := fun g =>
    (isHolomorphicOn_iff_differentiableOn _ _).1 (hmer g).2.2.1
  -- the local data, transported to the coordinates `e₀`
  choose nl el Wl hWlo hWlmem hWlO hl using hloc
  let ι := Λ
  let L : ∀ i : ι, (Fin n₀ → ℂ) ≃L[ℂ] (Fin (nl i.1 i.2) → ℂ) := fun i =>
    (e₀.trans (el i.1 i.2).symm).toContinuousLinearEquiv
  let W₀ : ι → Set (Fin n₀ → ℂ) := fun i => L i ⁻¹' Wl i.1 i.2
  have hW₀ : ∀ i, IsOpen (W₀ i) := fun i => (hWlo i.1 i.2).preimage (L i).continuous
  choose hfun hhfun hhE using hl
  let h₀ : ι → Γ → (Fin n₀ → ℂ) → ℂ := fun i g => hfun i.1 i.2 g ∘ L i
  have hh₀ : ∀ i g, DifferentiableOn ℂ (h₀ i g) (W₀ i) := fun i g =>
    (hhfun i.1 i.2 g).comp (L i).differentiableOn (fun x hx => hx)
  have hL : ∀ i s, el i.1 i.2 (L i s) = e₀ s := by
    intro i s
    simp [L]
  have hh₀E : ∀ i g, ∀ s ∈ W₀ i, s ∈ D₀ → h₀ i g s = E (e₀ s) g := by
    intro i g s hs hsD
    have := hhE i.1 i.2 g (L i s) hs (by rw [hL]; exact hsD)
    simp only [h₀, Function.comp_apply, this, hL]
  obtain ⟨E₀', hE₀'hol, hE₀'D, hE₀'out⟩ := exists_differentiableOn_union_extension
    (fun s g => E (e₀ s) g) hD₀o hD₀d hEhol W₀ hW₀ h₀ hh₀ hh₀E
  let D₀' : Set (Fin n₀ → ℂ) := D₀ ∪ ⋃ i, W₀ i
  have hD₀'o : IsOpen D₀' := hD₀o.union (isOpen_iUnion hW₀)
  have hD : ∀ lam ∈ D, e₀.symm lam ∈ D₀ := by
    intro lam hlam
    show e₀ (e₀.symm lam) ∈ D
    simpa using hlam
  refine ⟨fun lam g => E₀' (e₀.symm lam) g, e₀.symm ⁻¹' D₀', ?_, ?_, ?_, ?_, ?_⟩
  · intro lam hlam
    refine Or.inr (mem_iUnion.2 ⟨⟨lam, hlam⟩, ?_⟩)
    show L ⟨lam, hlam⟩ (e₀.symm lam) ∈ Wl lam hlam
    simpa [L] using hWlmem lam hlam
  · intro lam hlam
    exact Or.inl (hD lam hlam)
  · intro g
    apply isMeromorphicInCoordinatesOn_of_scalarCoordinates e₀
    have hpre : e₀ ⁻¹' (e₀.symm ⁻¹' D₀') = D₀' := by
      ext s
      simp
    rw [hpre]
    have hcomp : ((fun lam => E₀' (e₀.symm lam) g) ∘ e₀) = fun s => E₀' s g := by
      funext s
      simp
    rw [hcomp]
    exact (hmer g).of_extension subset_union_left hD₀'o (hE₀'hol g)
      (fun s hs => congrFun (hE₀'D s hs) g)
  · intro lam hlam
    funext g
    have := congrFun (hE₀'D (e₀.symm lam) (hD lam hlam)) g
    simpa using this
  · intro lam hlam
    funext g
    have hnot : ∀ i, e₀.symm lam ∉ W₀ i := by
      intro i hi
      apply hlam
      have hmem : el i.1 i.2 (L i (e₀.symm lam)) ∈ O := hWlO i.1 i.2 ⟨_, hi, rfl⟩
      simpa [hL] using hmem
    have := congrFun (hE₀'out (e₀.symm lam) hnot) g
    simpa using this

end Gluing

/-- **Enlarging the domain of holomorphy of a meromorphic family** (statement form of
`exists_isMeromorphicInCoordinatesOn_extension`). -/
def MeromorphicDomainExtensionStatement : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (Γ : Type) (E : X → Γ → ℂ) (D : Set X),
    (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D) → ∀ (O Λ : Set X),
    (∀ lam₀ ∈ Λ, ∃ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] X) (W : Set (Fin n → ℂ)),
      IsOpen W ∧ e.symm lam₀ ∈ W ∧ e '' W ⊆ O ∧ ∀ g, ∃ h : (Fin n → ℂ) → ℂ,
        DifferentiableOn ℂ h W ∧ ∀ s ∈ W, e s ∈ D → h s = E (e s) g) →
    ∃ (E' : X → Γ → ℂ) (D' : Set X), Λ ⊆ D' ∧ D ⊆ D' ∧
      (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E' lam g) D') ∧
      (∀ lam ∈ D, E' lam = E lam) ∧ ∀ lam ∉ O, E' lam = E lam

theorem meromorphicDomainExtension : MeromorphicDomainExtensionStatement :=
  fun _ _ _ _ E D hE O Λ hloc => exists_isMeromorphicInCoordinatesOn_extension E D hE O Λ hloc

end Langlands.Analysis.Meromorphic
