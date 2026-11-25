/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
import WeilConjectures.AlgebraicGeometry.LocalOverlapTransitions
import WeilConjectures.AlgebraicGeometry.FinitePresentationOverlapMapLifting
import WeilConjectures.AlgebraicGeometry.FinitePresentationOverlapCoherence

/-! # Eventual compatibility of fixed local models

Source: Stacks Project, Tags 01ZR and 05N7.
(blueprint: lem-pc-fp-local-overlap-models). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Overlap identifications between fixed local models become compatible at a later stage.
Source: Stacks Project, Limits, Tag 01ZR, first proof (Zariski gluing); Algebra,
Tag 05N7, map and equality clauses.
(blueprint: lem-pc-fp-local-overlap-models).

Proof: Conjugate the restriction identifications of M by the given component
isomorphisms e. This gives comparisons between the two local models on each limit
overlap, with specified inverses. Quasi-separatedness makes the pairwise overlaps
of the finite affine cover quasi-compact. Cover these by finitely many affines, and
likewise cover the intersections in these refinements and the triple overlaps.
On each such affine, the coordinate rings form a directed colimit and quasi-coherent
pullback is extension of scalars. The map clause of 05N7 lifts the comparisons and
inverses between the fixed finitely presented modules. Its equality clause makes
the inverse identities, agreement on refinement intersections, and triple cocycle
identities hold at a stage. There are finitely many maps and equations, so directedness
gives one common stage k above j. Glue the maps across the refinement intersections;
their inverses glue too, and the cocycle follows on the finite triple-overlap cover.
Pull these glued overlap maps to any test scheme mapping to two cover members; their
functoriality, self identity, and composition law give D in the pseudofunctor's
all-test-schemes definition. Its components are the pulled-back N; this gives their
isomorphisms without asserting any new finite-presentation result. Compose the given
e with the pullback-composition comparisons to obtain the component maps η.hom.
By the way the overlap maps were lifted these commute with the transitions, hence
define the morphism η. Every component is a composite of isomorphisms. The empty cover
has unique datum and morphism and vacuous component conditions. No finiteness property
of M is needed here: it is already locally identified with the supplied finite models.
For a preorder use the partial-order quotient of the nonempty tail above j. -/
theorem exists_finitePresentation_local_overlap_models
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
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)))).f a)).obj M) :
    ∃ (k : I) (hjk : j ≤ k),
      let q := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (Over.homMk (Spec.map (R.map (homOfLE hjk)))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      let V : (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u} :=
        U.pullback₁ q
      let p := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))
      ∃ D : modulesPseudofunctor.DescentData V.f,
        (∀ a, Nonempty ((D.obj a : (V.X a).Modules) ≅
          (Scheme.Modules.pullback (U.pullbackHom q a)).obj (N a))) ∧
        ∃ η : (Pseudofunctor.DescentData.pullFunctor modulesPseudofunctor
          (f := V.f) (f' := (V.pullback₁ p).f)
          (p := p) (α := fun a ↦ a) (p' := fun a ↦ V.pullbackHom p a)
          (fun a ↦ V.pullbackHom_map p a)).obj D ⟶
          (modulesPseudofunctor.toDescentData (V.pullback₁ p).f).obj M,
          ∀ a, IsIso (η.hom a) := by
  classical
  obtain ⟨k, hjk, T, hT, hcmp⟩ :=
    exists_finitePresentation_overlap_map_lifting R c hc i f j hij U N hN hNq M e
  obtain ⟨l, hkl, hcoh, hcomp⟩ :=
    exists_finitePresentation_overlap_eventual_coherence R c hc i f j hij U N hN hNq M
      k hjk T hT hcmp
  let q₀ := overlapStageMap R f hij hjk
  let q := overlapStageMap R f hij (hjk.trans hkl)
  let V : (pullback f (Spec.map
      (R.map (homOfLE (hij.trans (hjk.trans hkl)))))).OpenCover.{u} := U.pullback₁ q
  let r := overlapStageMap R f (hij.trans hjk) hkl
  let s := overlapRefinementHom U q₀ q r (overlapStageMap_comp R f hij hjk hkl)
  let T' := T.pull (p := r) (α := fun a ↦ a) (p' := s)
    (fun a ↦ overlapRefinementHom_map U q₀ q r
      (overlapStageMap_comp R f hij hjk hkl) a)
  let p := overlapLimitMap R c f (hij.trans (hjk.trans hkl))
  let D := T'.toDescentData hcoh
  obtain ⟨ε⟩ := hcomp
  refine ⟨l, hjk.trans hkl, D, ?_, ?_⟩
  · intro a
    obtain ⟨ea⟩ := hT a
    exact ⟨(Scheme.Modules.pullback (s a)).mapIso ea ≪≫
      pullbackCompOfEq (s a) (U.pullbackHom q₀ a)
        (U.pullbackHom q a)
        (overlapRefinementHom_comp U q₀ q r (overlapStageMap_comp R f hij hjk hkl) a)
        (N a)⟩
  · exact ⟨T'.pullComparisonHom (fun a ↦ V.pullbackHom_map p a) hcoh ε,
      fun a ↦ T'.pullComparisonHom_isIso_hom (fun a ↦ V.pullbackHom_map p a) hcoh ε a⟩

end AlgebraicGeometry
