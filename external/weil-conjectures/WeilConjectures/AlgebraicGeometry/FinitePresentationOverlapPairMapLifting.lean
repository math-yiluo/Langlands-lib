/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocalOverlapTransitions
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.OverlapPairCanonicalComparisons
import WeilConjectures.AlgebraicGeometry.FinitePresentationOverlapPairSingleStage
import WeilConjectures.AlgebraicGeometry.OverlapPairRefinementPersistence

/-! # Descent of a map on one pairwise overlap

Source: Stacks Project, Tags 01ZR and 05N7.
(blueprint: lem-pc-fp-overlap-pair-map-lifting). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry

/-- The limit map factors through every later stage.
(blueprint: lem-pc-fp-overlap-pair-map-lifting). -/
lemma overlapLimitMap_stage_comp {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cone (R.op ⋙ Scheme.Spec))
    {i j k : I} {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (hij : i ≤ j) (hjk : j ≤ k) :
    overlapLimitMap R c f (hij.trans hjk) ≫ overlapStageMap R f hij hjk =
      overlapLimitMap R c f hij := by
  dsimp only [overlapLimitMap, overlapStageMap]
  rw [← baseChangeMap_comp]
  congr 1
  ext
  simpa using c.w (homOfLE hjk).op


-- Preserve the original unused existential binder in the public signature.
set_option linter.unusedVariables false in
/-- Descend the conjugated transition on one pairwise overlap, with persistence at later stages.
Source: Stacks Project, Tag 01ZR, first proof (Zariski gluing), and Tag 05N7 (2), (3).
(blueprint: lem-pc-fp-overlap-pair-map-lifting).

Proof: The overlap of the two fixed affine charts is quasi-compact because the ambient
scheme is quasi-separated. Cover it by finitely many affine opens, and cover their
pairwise intersections by finitely many affine opens. The restrictions of N a and N b
are finitely presented and quasi-coherent. Conjugate the restriction map of M by e a
and e b. On each affine chart, the limit ring is the directed colimit of the stage
rings and module pullback is extension of scalars. Apply Tag 05N7 (2) to lift the map
on each chart. Apply (3) on the finite refinement intersections to make the local
maps agree at a common later stage. Glue to a map on the entire pairwise overlap.
Its limit pullback is the prescribed map by construction and the sheaf condition.
Pull this map back to every subsequent stage. Pullback composition and the canonical
iterated comparisons give the displayed square there. This argument concerns just
one pair: it asserts neither a common stage for all pairs nor natural overlap
transitions on arbitrary test schemes. If the overlap is empty its unique map works.
For a preorder use the partial-order quotient of the nonempty tail above j. -/
theorem exists_finitePresentation_overlap_pair_map_lifting
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    [Finite U.I₀] [∀ a, IsAffine (U.X a)]
    (N : (a : U.I₀) → (U.X a).Modules)
    (hN : ∀ a, (N a).IsFinitePresentation) (hNq : ∀ a, (N a).IsQuasicoherent)
    (M : (pullback f (c.π.app (op i))).Modules)
    (e : ∀ a, (Scheme.Modules.pullback (U.pullbackHom
      (baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))) a)).obj (N a) ≅
      (Scheme.Modules.pullback ((U.pullback₁ (baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)))).f a)).obj M)
    (a b : U.I₀) :
    ∃ (k : I) (hjk : j ≤ k), ∀ (l : I) (hjl : j ≤ l), k ≤ l →
      let q := overlapStageMap R f hij hjl
      let V := U.pullback₁ q
      let p := overlapLimitMap R c f (hij.trans hjl)
      let A := fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)
      let W := V.pullback₁ p
      let D := (modulesPseudofunctor.toDescentData W.f).obj M
      let ε := overlapIteratedComparison U q p (overlapLimitMap R c f hij)
        (overlapLimitMap_stage_comp R c f hij hjl) N M e
      ∃ φ : (Scheme.Modules.pullback (pullback.fst (V.f a) (V.f b))).obj (A a) ⟶
          (Scheme.Modules.pullback (pullback.snd (V.f a) (V.f b))).obj (A b),
        overlapPairSquare V A p D ε a b φ := by
  obtain ⟨k, hjk, hk⟩ := exists_overlap_pair_map_at_stage
    R c hc i f j hij U N hN hNq M e a b
  refine ⟨k, hjk, ?_⟩
  intro l hjl hkl
  have hs := overlap_pair_map_refinement_persistence U
    (overlapStageMap R f hij hjk) (overlapStageMap R f hij hjl)
    (overlapStageMap R f (hij.trans hjk) hkl)
    (overlapStageMap_comp R f hij hjk hkl)
    (overlapLimitMap R c f (hij.trans hjk))
    (overlapLimitMap R c f (hij.trans hjl)) (overlapLimitMap R c f hij)
    (overlapLimitMap_stage_comp R c f hij hjk)
    (overlapLimitMap_stage_comp R c f hij hjl)
    (overlapLimitMap_stage_comp R c f (hij.trans hjk) hkl) N M e a b
  exact hs hk

end AlgebraicGeometry
