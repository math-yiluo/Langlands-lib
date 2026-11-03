import Langlands.GroupScheme.SplitSolvableFixedPointStatement
import Langlands.GroupScheme.SchemeActionOrbitDescent
import Langlands.GroupScheme.ElementaryOrbitLimit

/-! # Split-solvable fixed points on pseudo-complete schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SchemeAction

variable {S : Scheme.{u}} {H : GroupScheme S} {X : Over S}

/-- All-test triviality of the acting group makes every point fixed. -/
theorem isFixed_of_range_id_eq_bot (a : SchemeAction H X)
    (hH : SubgroupFunctor.range (𝟙 H) = ⊥) {T : Over S} (x : T ⟶ X) :
    a.IsFixed x := by
  intro T' b h
  have hh : h ∈ (SubgroupFunctor.range (𝟙 H)).carrier T' := by
    exact ⟨h, rfl⟩
  rw [hH, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hh
  rw [hh, a.act_one]

end SchemeAction

namespace SplitSolvable

variable {k : Type u} [Field k]

/-- Induction along an actual finite series with elementary represented quotients. -/
theorem exists_isFixed_of_hasSeries
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    (n : ℕ) (hH : HasSeries n H)
    {X : Over (Spec (CommRingCat.of k))} (hX : IsPseudoComplete X)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X)
    (a : SchemeAction H X) :
    ∃ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X, a.IsFixed y := by
  induction n generalizing H with
  | zero =>
      exact ⟨x, a.isFixed_of_range_id_eq_bot hH x⟩
  | succ n ih =>
      obtain ⟨N, V, j, q, hj, _, _, _, hq, hV, hN⟩ := hH
      have : IsClosedImmersion j.hom.hom.left := hj
      have : IsAffineHom N.X.hom := by
        rw [← Over.w j.hom.hom]
        infer_instance
      obtain ⟨xN, hxN⟩ := ih hN (a.restrict j)
      let : QuasiCompact q.hom.hom.left := SchemeAction.quasiCompact_quotient q
      let : Flat q.hom.hom.left := hq.1
      let : Surjective q.hom.hom.left := hq.2.1
      obtain ⟨ρ, hρ⟩ := a.exists_orbitMap_factor j q hq xN hxN
      exact a.exists_isFixed_of_elementary_equivariant hX q hV ρ
        (a.equivariant_of_orbitMap_factor q xN ρ hρ)

end SplitSolvable

/-- CGP, Proposition C.1.5, for the unchanged split-solvability and
pseudo-completeness predicates, with fixedness on every relative test. -/
theorem splitSolvablePseudoCompleteFixedPoint :
    SplitSolvablePseudoCompleteFixedPointStatement.{u} := by
  intro k _ H hH X hX hx a
  let : IsAffineHom H.X.hom := hH.isAffineHom
  obtain ⟨n, hn⟩ := hH.hasSeries
  obtain ⟨x⟩ := hx
  exact SplitSolvable.exists_isFixed_of_hasSeries n hn hX x a

end Langlands.GroupScheme
