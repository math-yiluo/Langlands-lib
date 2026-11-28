import Langlands.Global.AdelicEisensteinImaginaryJointContinuityReduction

/-! # Joint continuity of locally holomorphic finite Eisenstein families -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Global

open Set
open Langlands.Analysis.Meromorphic

/-- Identify a finite weighted sum of scalar meromorphic functions by agreement on one open
patch in linear coordinates. Each summand may have its own holomorphy domain. -/
theorem eqOn_meromorphic_sum_of_eqOn_open
    {V ι : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Fintype ι]
    {m : ℕ} (e : (Fin m → ℂ) ≃ₗ[ℂ] V)
    {f : ι → V → ℂ} {b : ι → V → ℂ} {E : V → ℂ} {D : ι → Set V} {O : Set V}
    (hE : IsMeromorphicInCoordinatesOn E O)
    (hf : ∀ j, IsMeromorphicInCoordinatesOn (f j) (D j))
    (hb : ∀ j, IsMeromorphicInCoordinatesOn (b j) univ)
    {U : Set (Fin m → ℂ)} (hU : IsOpen U) (hne : U.Nonempty)
    (hEq : ∀ s ∈ U ∩ e ⁻¹' (O ∩ ⋂ j, D j), E (e s) = ∑ j, b j (e s) * f j (e s)) :
    EqOn E (fun s => ∑ j, b j s * f j s) (O ∩ ⋂ j, D j) := by
  classical
  have hD := isOpenDenseInCoordinates_iInter_of_finite
    (fun j => (hf j).isOpenDenseInCoordinates)
  have hsum : IsMeromorphicInCoordinatesOn (fun s => ∑ j, b j s * f j s) (⋂ j, D j) := by
    have hfun : (∑ j, b j * f j) = (fun s => ∑ j, b j s * f j s) := by
      funext s
      simp only [Finset.sum_apply, Pi.mul_apply]
    rw [← hfun]
    exact IsMeromorphicInCoordinatesOn.sum (h := fun j => b j * f j) Finset.univ hD
      fun j _ => ((hb j).mul (hf j)).congr_mono hD
        (fun _ hs => ⟨mem_univ _, mem_iInter.mp hs j⟩) (fun _ _ => rfl)
  exact hE.eqOn_of_eqOn_open hsum e hU hne hEq

/-- Joint continuity of a holomorphic finite sum of families with common root forms.
The sum can agree with the individual terms only on a dense subset of its holomorphy domain. -/
theorem continuousOn_of_sum_rootHyperplane_cleared
    {X ι β : Type*} [TopologicalSpace X] [Fintype ι] {m : ℕ}
    {L : β → (Fin m → ℂ) →ₗ[ℂ] ℂ} {b : ι → (Fin m → ℂ) → ℂ}
    {f : ι → (Fin m → ℂ) → X → ℂ} {E : (Fin m → ℂ) → X → ℂ}
    {O D : Set (Fin m → ℂ)} (hO : IsOpen O) (hD : Dense D)
    (hE : ∀ g, DifferentiableOn ℂ (fun s => E s g) O) (hb : ∀ j, Continuous (b j))
    (hEq : ∀ g, EqOn (fun s => E s g) (fun s => ∑ j, b j s * f j s g) (O ∩ D))
    (hclear : ∀ s₀ ∈ O, ∀ j, ∃ (S : Finset β) (k : ℕ) (W : Set (Fin m → ℂ))
      (N : (Fin m → ℂ) → X → ℂ),
      (∀ α ∈ S, ∃ w, L α w ≠ 0) ∧ IsOpen W ∧ s₀ ∈ W ∧
      ContinuousOn (fun q : (Fin m → ℂ) × X => N q.1 q.2) (W ×ˢ univ) ∧
      ∀ g, ∀ s ∈ W ∩ D, N s g = (∏ α ∈ S, L α (s - s₀)) ^ k * f j s g) :
    ContinuousOn (fun q : (Fin m → ℂ) × X => E q.1 q.2) (O ×ˢ univ) := by
  classical
  rintro ⟨s₀, g₀⟩ ⟨hs₀, -⟩
  choose Sj kj Wj Nj hLj hWj hsWj hNj hjEq using hclear s₀ hs₀
  let S := Finset.univ.biUnion Sj
  let k := Finset.univ.sup kj
  let W := ⋂ j, Wj j
  have hS (j : ι) : Sj j ⊆ S := Finset.subset_biUnion_of_mem Sj (Finset.mem_univ j)
  have hk (j : ι) : kj j ≤ k := Finset.le_sup (Finset.mem_univ j)
  have hW : IsOpen W := isOpen_iInter_of_finite hWj
  have hsW : s₀ ∈ W := mem_iInter.mpr hsWj
  let p (A : Finset β) (s : Fin m → ℂ) := ∏ α ∈ A, L α (s - s₀)
  have hp (A : Finset β) : Continuous (p A) :=
    continuous_finsetProd _ fun α _ =>
      (L α).continuous_of_finiteDimensional.comp (continuous_id.sub continuous_const)
  let a (j : ι) (s : Fin m → ℂ) : ℂ :=
    p (S \ Sj j) s ^ k * p (Sj j) s ^ (k - kj j) * b j s
  have ha (j : ι) : Continuous (a j) :=
    (((hp _).pow _).mul ((hp _).pow _)).mul (hb j)
  let N (s : Fin m → ℂ) (g : X) := ∑ j, a j s * Nj j s g
  have hN : ContinuousOn (fun q : (Fin m → ℂ) × X => N q.1 q.2) (W ×ˢ univ) := by
    refine continuousOn_finsetSum _ fun j _ => ?_
    exact ((ha j).comp continuous_fst).continuousOn.mul
      ((hNj j).mono fun q hq => ⟨mem_iInter.mp hq.1 j, hq.2⟩)
  have hEq' (g : X) : EqOn (fun s => N s g) (fun s => p S s ^ k * E s g) ((W ∩ O) ∩ D) := by
    intro s hs
    have hsO : s ∈ O := hs.1.2
    have hEs : E s g = ∑ j, b j s * f j s g := hEq g ⟨hsO, hs.2⟩
    change (∑ j, a j s * Nj j s g) = p S s ^ k * E s g
    rw [hEs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsplit : p (S \ Sj j) s * p (Sj j) s = p S s := Finset.prod_sdiff (hS j)
    rw [hjEq j g s ⟨mem_iInter.mp hs.1.1 j, hs.2⟩, ← hsplit, mul_pow]
    calc
      a j s * (p (Sj j) s ^ kj j * f j s g) =
          p (S \ Sj j) s ^ k * (p (Sj j) s ^ (k - kj j) * p (Sj j) s ^ kj j) *
            (b j s * f j s g) := by dsimp only [a]; ring
      _ = _ := by rw [← pow_add, Nat.sub_add_cancel (hk j)]
  have hL (α : β) (hα : α ∈ S) : ∃ w, L α w ≠ 0 := by
    obtain ⟨j, -, hαj⟩ := Finset.mem_biUnion.mp hα
    exact hLj j α hαj
  have hcover : W ∩ O ⊆ closure ((W ∩ O) ∩ D) :=
    hD.open_subset_closure_inter (hW.inter hO)
  have hEqWO (g : X) : EqOn (fun s => N s g) (fun s => p S s ^ k * E s g) (W ∩ O) := by
    have hNc : ContinuousOn (fun t => N t g) (W ∩ O) :=
      hN.comp (f := fun t => (t, g)) (continuous_id.prodMk continuous_const).continuousOn
        (fun t ht => ⟨ht.1, mem_univ g⟩)
    have hEc : ContinuousOn (fun t => p S t ^ k * E t g) (W ∩ O) :=
      ((hp S).pow k).continuousOn.mul ((hE g).continuousOn.mono inter_subset_right)
    exact (hEq' g).of_subset_closure hNc hEc inter_subset_left hcover
  exact (continuousAt_of_rootHyperplane_cleared (E' := E) hO hE S L hL k hW hsW hs₀ hN
    (fun g s hs hsO => hEqWO g ⟨hs, hsO⟩) g₀).continuousWithinAt

/-- A finite entire-weighted family is jointly continuous on its holomorphy domain if it
agrees with the individual, locally cleared continuations on an open convergence patch. -/
def FiniteMeromorphicFamilyJointContinuityStatement : Prop :=
  ∀ {X ι β V : Type*} [TopologicalSpace X] [Fintype ι]
    [AddCommGroup V] [Module ℂ V] {m : ℕ} (e : (Fin m → ℂ) ≃ₗ[ℂ] V)
    (L : β → (Fin m → ℂ) →ₗ[ℂ] ℂ) (b : ι → V → ℂ)
    (f : ι → V → X → ℂ) (E : V → X → ℂ) (D : ι → Set V) (O : Set V),
    (∀ g, IsMeromorphicInCoordinatesOn (fun s => E s g) O) →
    (∀ j g, IsMeromorphicInCoordinatesOn (fun s => f j s g) (D j)) →
    (∀ j, IsMeromorphicInCoordinatesOn (b j) univ) →
    ∀ U : Set (Fin m → ℂ), IsOpen U → U.Nonempty →
    (∀ g, ∀ s ∈ U ∩ e ⁻¹' (O ∩ ⋂ j, D j), E (e s) g = ∑ j, b j (e s) * f j (e s) g) →
    (∀ s₀ ∈ e ⁻¹' O, ∀ j, ∃ (S : Finset β) (k : ℕ) (W : Set (Fin m → ℂ))
      (N : (Fin m → ℂ) → X → ℂ),
      (∀ α ∈ S, ∃ w, L α w ≠ 0) ∧ IsOpen W ∧ s₀ ∈ W ∧
      ContinuousOn (fun q : (Fin m → ℂ) × X => N q.1 q.2) (W ×ˢ univ) ∧
      ∀ g, ∀ s ∈ W ∩ e ⁻¹' D j, N s g = (∏ α ∈ S, L α (s - s₀)) ^ k * f j (e s) g) →
    ContinuousOn (fun q : (Fin m → ℂ) × X => E (e q.1) q.2) ((e ⁻¹' O) ×ˢ univ)

/-- Identify the sum by meromorphic uniqueness, then use common clearing and Cauchy's
integral formula for joint continuity. -/
theorem finiteMeromorphicFamilyJointContinuity :
    FiniteMeromorphicFamilyJointContinuityStatement := by
  intro X ι β V _ _ _ _ m e L b f E D O hE hf hb U hU hne hEq hclear
  rcases isEmpty_or_nonempty X with hX | hX
  · rintro ⟨s, g⟩
    exact (hX.false g).elim
  obtain ⟨g₀⟩ := hX
  let : FiniteDimensional ℂ V := FiniteDimensional.of_surjective e.toLinearMap e.surjective
  let Dc := e ⁻¹' (⋂ j, D j)
  have hDc : Dense Dc := (isOpenDenseInCoordinates_iInter_of_finite
    (fun j => (hf j g₀).isOpenDenseInCoordinates) m e).2
  have hbc (j : ι) : Continuous (b j ∘ e) := continuousOn_univ.mp (by
    simpa only [preimage_univ] using
      (differentiableOn_of_isHolomorphicOn ((hb j).2 m e).2.2.1).continuousOn)
  refine continuousOn_of_sum_rootHyperplane_cleared (O := e ⁻¹' O) (D := Dc)
    (L := L) (f := fun j s g => f j (e s) g) ((hE g₀).2 m e).1 hDc
    (fun g => differentiableOn_of_isHolomorphicOn ((hE g).2 m e).2.2.1) hbc ?_ ?_
  · intro g s hs
    exact eqOn_meromorphic_sum_of_eqOn_open e (hE g) (fun j => hf j g) hb hU hne (hEq g) hs
  · intro s₀ hs₀ j
    obtain ⟨S, k, W, N, hS, hW, hs₀W, hN, hNE⟩ := hclear s₀ hs₀ j
    exact ⟨S, k, W, N, hS, hW, hs₀W, hN,
      fun g s hs => hNE g s ⟨hs.1, mem_iInter.mp hs.2 j⟩⟩

end Langlands.Global
