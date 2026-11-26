import Langlands.BaseChange.TwistedCharacter.SpectrumLines
import Langlands.BaseChange.TwistedPseudoCoefficientOrbitSeparation
import Langlands.Representation.Filtration.SimpleSubquotientFactorProof
import Langlands.Representation.Smooth.IrreducibleCompositionFactors
import Langlands.Representation.Twist.AdmissibilityProof

/-! # Visibility of unramified twists at a common compact open level -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis

universe uG z uι

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- A compact open subgroup sees every unramified twist of a representation it sees. -/
theorem fixedVectors_ne_bot_of_isUnramifiedTwistOf (θ : G ≃* G)
    {V W : Type z} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {π : Representation ℂ G W}
    (h : IsUnramifiedTwistOf θ ρ π) (J : OpenSubgroup G) (hJ : IsCompact (J : Set G))
    (hρ : fixedVectors ρ J.toSubgroup ≠ ⊥) : fixedVectors π J.toSubgroup ≠ ⊥ := by
  obtain ⟨ψ, hψ, _, ⟨e⟩⟩ := h
  apply (fixedVectors_ne_bot_iff_of_equiv e J.toSubgroup).mpr
  rwa [fixedVectors_twist_eq_of_le_ker ψ ρ J.toSubgroup (fun g hg => hψ _ hJ g hg)]

/-- Nonzero smooth representations in a finite family, and every invariant unramified twist
of any family member, have nonzero fixed vectors at one common compact open level. -/
theorem exists_compact_open_fixed_unramifiedTwists (θ : G ≃* G)
    (hθ : ∀ U : OpenSubgroup G,
      ∃ J : OpenSubgroup G, J ≤ U ∧ IsCompact (J : Set G) ∧ ∀ j ∈ J, θ.symm j ∈ J)
    {ι : Type uι} [Fintype ι]
    {V : ι → Type z} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] [∀ i, Nontrivial (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)) (hρ : ∀ i, IsSmooth (ρ i)) :
    ∃ J : OpenSubgroup G, IsCompact (J : Set G) ∧ (∀ j ∈ J, θ.symm j ∈ J) ∧
      ∀ i (W : Type z) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G W),
        IsUnramifiedTwistOf θ (ρ i) π → fixedVectors π J.toSubgroup ≠ ⊥ := by
  classical
  choose v hv using fun i => exists_ne (0 : V i)
  choose U hU using fun i => hρ i (v i)
  obtain ⟨J, hJU, hJ, hθJ⟩ := hθ (Finset.univ.inf U)
  refine ⟨J, hJ, hθJ, fun i W _ _ π hπ => ?_⟩
  apply fixedVectors_ne_bot_of_isUnramifiedTwistOf θ hπ J hJ
  apply (fixedVectors (ρ i) J.toSubgroup).ne_bot_iff.mpr
  refine ⟨v i, fun j => hU i ⟨j.val, ?_⟩, hv i⟩
  exact hJU.trans (Finset.inf_le (Finset.mem_univ i)) j.property

/-- One compact open level sees the twists of every irreducible constituent of a finite
family of finite-length smooth representations. -/
theorem exists_compact_open_fixed_constituentTwists (θ : G ≃* G)
    (hθ : ∀ U : OpenSubgroup G,
      ∃ J : OpenSubgroup G, J ≤ U ∧ IsCompact (J : Set G) ∧ ∀ j ∈ J, θ.symm j ∈ J)
    {ι : Type uι} [Fintype ι] (A : ι → SmoothRep.{0,uG,z} ℂ G)
    (hA : ∀ i, (A i).HasFiniteLength) :
    ∃ J : OpenSubgroup G, IsCompact (J : Set G) ∧ (∀ j ∈ J, θ.symm j ∈ J) ∧
      ∀ i (D : SmoothRep.{0,uG,z} ℂ G), D.IsIrreducible → SmoothRep.IsSubquotient D (A i) →
        ∀ (W : Type z) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G W),
          IsUnramifiedTwistOf θ D.representation π → fixedVectors π J.toSubgroup ≠ ⊥ := by
  classical
  let s (i : ι) := SmoothRep.IrreducibleGrothendieckProof.chosenSeries ⟨A i, hA i⟩
  let C := Σ i, Fin (s i).1
  let B (j : C) := SmoothRep.IrreducibleGrothendieckProof.gradedSmooth (s j.1).2.val j.2
  have hirr (j : C) : (B j).representation.IsIrreducible := (s j.1).2.property j.2
  let _ (j : C) : Nontrivial (B j) := CharacterSeparation.nontrivial_of_isIrreducible (hirr j)
  obtain ⟨J, hJ, hθJ, hvis⟩ := exists_compact_open_fixed_unramifiedTwists θ hθ
    (fun j : C => (B j).representation) (fun j => (B j).isSmooth)
  refine ⟨J, hJ, hθJ, ?_⟩
  rintro i D hDirr ⟨S, T, ⟨e⟩⟩ W _ _ π ⟨ψ, hψ, hψθ, ⟨f⟩⟩
  obtain ⟨j, ⟨e'⟩⟩ := simpleSubquotientFactor ℂ G (A i) (s i).1 (s i).2.val
    (s i).2.property D S T hDirr ⟨SmoothRep.equivOfIso e⟩
  exact hvis ⟨i, j⟩ W π ⟨ψ, hψ, hψθ, ⟨f.trans (twistEquiv ψ e')⟩⟩

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] (θ : G ≃* G)

/-- The orbit of a nonzero smooth representation is disjoint from the span of the other
essentially tempered characters and the irreducibles invisible at a suitable compact open level. -/
theorem exists_disjoint_twistedOrbitSpan_otherTempered_invisible
    (hθ : ∀ U : OpenSubgroup G,
      ∃ J : OpenSubgroup G, J ≤ U ∧ IsCompact (J : Set G) ∧ ∀ j ∈ J, θ.symm j ∈ J)
    {V : Type z} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (τ : Representation ℂ G V) (hτ : IsSmooth τ) :
    ∃ J : OpenSubgroup G, IsCompact (J : Set G) ∧ (∀ j ∈ J, θ.symm j ∈ J) ∧
      Disjoint (twistedOrbitSpan μ θ τ)
        (twistedOtherEssentiallyTemperedSpan μ θ τ ⊔ twistedInvisibleSpan.{uG,z} μ θ J) := by
  obtain ⟨J, hJ, hθJ, hvis⟩ := exists_compact_open_fixed_unramifiedTwists θ hθ
    (fun _ : Unit => τ) (fun _ => hτ)
  let P (W : Type z) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G W) : Prop :=
    ¬ IsUnramifiedTwistOf θ τ π
  have h := disjoint_twistedSpectrumSpan μ θ (fun _ _ _ => IsUnramifiedTwistOf θ τ) P hθ
    (fun hρ hπ ⟨e⟩ => by
      obtain ⟨ψ, hψ, hψθ, ⟨eρ⟩⟩ := hρ
      exact hπ ⟨ψ, hψ, hψθ, ⟨e.symm.trans eρ⟩⟩)
  refine ⟨J, hJ, hθJ, h.mono_right (sup_le ?_ ?_)⟩
  · apply Submodule.span_mono
    rintro d ⟨W, iAdd, iMod, π, hπ, A, hirr, h, rfl⟩
    exact ⟨W, iAdd, iMod, π, hπ, A, hirr, h.1, rfl⟩
  · apply Submodule.span_mono
    rintro d ⟨W, iAdd, iMod, π, hπ, A, hirr, h, rfl⟩
    let := iAdd
    let := iMod
    exact ⟨W, iAdd, iMod, π, hπ, A, hirr, fun ho => hvis () W π ho h, rfl⟩

end Langlands.BaseChange
