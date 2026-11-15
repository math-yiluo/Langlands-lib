import Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocusOpenA
import Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocusClosedOfGeneric

/-! # Openness of the étale locus of a closed subscheme of an étale chart

A set `E` in a noetherian quasi-sober space is open if it is stable under generization and
every `y ∈ E` has an open neighbourhood `V` with `V ∩ closure {y} ⊆ E`
(`isOpen_of_specializes`, by noetherian induction on closed sets). For the étale locus of
`ξ ∈ F(Spec (R'/𝔍))` stability under generization is `infinitesimallyEtaleAt_of_le`; the
neighbourhoods come from `exists_open_of_not_le_nilradical` when the prime of `R` below `y` is
not nilpotent, and from the statement of Murre's generic case (the hypothesis of
`ClosedOfGenericStatement`) together with `infinitesimallyEtaleAt_of_noLargerLift` otherwise.
This proves `ClosedOfGenericStatement` (`closedEtaleLocusOpen_of_generic`). -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing
  TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace EtaleLocus

/-- In a noetherian quasi-sober space, a set stable under generization is open if every point
`y` of it has an open neighbourhood whose specializations of `y` lie in the set. -/
theorem isOpen_of_specializes {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    [QuasiSober X] (E : Set X) (hG : ∀ ⦃x y : X⦄, x ⤳ y → y ∈ E → x ∈ E)
    (hN : ∀ y ∈ E, ∃ V : Set X, IsOpen V ∧ y ∈ V ∧ ∀ w ∈ V, y ⤳ w → w ∈ E) : IsOpen E := by
  have key : ∀ s : Closeds X, IsClosed ((s : Set X) \ E) := by
    intro s
    apply wellFounded_lt.induction s
    clear s
    intro s H
    rcases eq_or_ne s ⊥ with rfl | h₀
    · simp
    by_cases h₁ : IsPreirreducible (s : Set X)
    · have hirr : IsIrreducible (s : Set X) := ⟨Closeds.coe_nonempty.2 h₀, h₁⟩
      obtain ⟨η, hη⟩ := QuasiSober.sober hirr s.isClosed
      by_cases hηE : η ∈ E
      · obtain ⟨V, hVo, hηV, hV⟩ := hN η hηE
        let s' : Closeds X := s ⊓ ⟨Vᶜ, hVo.isClosed_compl⟩
        have hs' : s' < s := by
          refine lt_of_le_of_ne inf_le_left fun h => ?_
          have hη' : η ∈ (s' : Set X) := by
            rw [h]
            exact hη.mem
          exact hη'.2 hηV
        have heq : (s : Set X) \ E = (s' : Set X) \ E := by
          ext w
          constructor
          · rintro ⟨hws, hwE⟩
            exact ⟨⟨hws, fun hwV => hwE (hV w hwV (hη.specializes hws))⟩, hwE⟩
          · rintro ⟨⟨hws, -⟩, hwE⟩
            exact ⟨hws, hwE⟩
        rw [heq]
        exact H s' hs'
      · have heq : (s : Set X) \ E = s := by
          ext w
          exact ⟨fun h => h.1, fun hws => ⟨hws, fun hwE => hηE (hG (hη.specializes hws) hwE)⟩⟩
        rw [heq]
        exact s.isClosed
    · simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at h₁
      obtain ⟨z₁, z₂, hz₁, hz₂, h, hz₁', hz₂'⟩ := h₁
      lift z₁ to Closeds X using hz₁
      lift z₂ to Closeds X using hz₂
      have e : (s : Set X) \ E = ((s ⊓ z₁ : Closeds X) : Set X) \ E ∪
          ((s ⊓ z₂ : Closeds X) : Set X) \ E := by
        ext w
        simp only [Set.mem_sdiff, Set.mem_union, Closeds.coe_inf, Set.mem_inter_iff]
        constructor
        · rintro ⟨hws, hwE⟩
          rcases h hws with h1 | h2
          · exact Or.inl ⟨⟨hws, h1⟩, hwE⟩
          · exact Or.inr ⟨⟨hws, h2⟩, hwE⟩
        · rintro (⟨⟨hws, -⟩, hwE⟩ | ⟨⟨hws, -⟩, hwE⟩) <;> exact ⟨hws, hwE⟩
      rw [e]
      exact (H _ (inf_lt_left.2 hz₁')).union (H _ (inf_lt_left.2 hz₂'))
  have := key ⊤
  rw [Closeds.coe_top, ← Set.compl_eq_univ_sdiff] at this
  exact isClosed_compl_iff.1 this

/-- Murre's Lemma 2 for closed subschemes of étale charts follows from the generic case. -/
theorem closedEtaleLocusOpen_of_generic : ClosedOfGenericStatement.{u, v} := by
  intro hgen R _ F hMC hloc hquot R' _ _ _ 𝔍 ξ
  have hF5 : NilpotentInjective F := hMC.2.2.2.2.2.2.1
  have : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing R R'
  refine isOpen_of_specializes (X := PrimeSpectrum (R' ⧸ 𝔍))
    {y | InfinitesimallyEtaleAt F ξ y} ?_ ?_
  · intro x y hxy hy
    exact infinitesimallyEtaleAt_of_le hF5 hloc ξ hy ((PrimeSpectrum.le_iff_specializes x y).2 hxy)
  · intro y hy
    by_cases hp : y.asIdeal.comap (algebraMap R (R' ⧸ 𝔍)) ≤ nilradical R
    · obtain ⟨V, hVo, hyV, hV⟩ := hgen R F hMC R' 𝔍 ξ y hy hp
      exact ⟨V, hVo, hyV, fun w hw _ =>
        infinitesimallyEtaleAt_of_noLargerLift hF5 hloc ξ w (hV w hw).1 (hV w hw).2⟩
    · obtain ⟨V, hVo, hyV, hV⟩ := exists_open_of_not_le_nilradical hF5 hquot ξ y hy hp
      exact ⟨V, hVo, hyV, fun w hw hyw =>
        hV w hw ((PrimeSpectrum.le_iff_specializes y w).2 hyw)⟩

end EtaleLocus

end Langlands.AlgebraicGeometry.UnramifiedFunctor
