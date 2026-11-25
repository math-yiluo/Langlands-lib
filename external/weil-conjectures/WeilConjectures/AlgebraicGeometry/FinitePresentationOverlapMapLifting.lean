/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocalOverlapTransitions
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.AlgebraicGeometry.FinitePresentationOverlapPairMapLifting
import WeilConjectures.AlgebraicGeometry.OverlapPairTransitionsAssembly
import Mathlib.Data.Finset.Order

/-! # Lifting overlap maps for fixed local models

Source: Stacks Project, Tags 01ZR and 05N7.
(blueprint: lem-pc-fp-overlap-map-lifting). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Lift natural overlap maps without asserting their identity or cocycle equations.
Source: Stacks Project, Tag 01ZR, first proof (Zariski gluing), and Tag 05N7,
map lifting and equality on intersections of refinement charts.
(blueprint: lem-pc-fp-overlap-map-lifting).

Proof: Conjugate the restriction transitions of M by e. The pairwise overlaps
of U are quasi-compact, by quasi-separatedness, and have finite affine covers.
For each chart, identify the coordinate ring at the limit with the directed
colimit of the stage rings, and identify quasi-coherent pullback with scalar
extension. Apply the map clause of 05N7 to the conjugated comparison on each
chart. Apply the equality clause on finite affine covers of intersections of
these charts to make their restrictions agree. A common upper bound exists for
this finite collection of maps and equations. Glue the chart maps on every
pairwise overlap, and pull these glued maps back to all test schemes. The
pullback composition comparison proves naturality. The objects are the actual
pullbacks of N, so their local isomorphisms can be identities. At the limit the
maps recover the conjugated transitions; compose e with the canonical iterated
pullback comparisons to obtain the component comparison to M. This comparison
commutes with the maps by their construction. No diagonal or triple cocycle
equations are claimed at the finite stage. The empty cover gives empty families.
For a preorder, apply the affine result to the partial-order quotient of the
nonempty tail above j. -/
theorem exists_finitePresentation_overlap_map_lifting
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
      let q := overlapStageMap R f hij hjk
      let V : (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u} :=
        U.pullback₁ q
      let p := overlapLimitMap R c f (hij.trans hjk)
      ∃ T : modulesPseudofunctor.OverlapTransitions V.f,
        (∀ a, Nonempty ((T.obj a : (V.X a).Modules) ≅
          (Scheme.Modules.pullback (U.pullbackHom q a)).obj (N a))) ∧
        Nonempty ((T.pull (p := p) (α := fun a ↦ a)
          (fun a ↦ V.pullbackHom_map p a)).Comparison
          ((modulesPseudofunctor.toDescentData (V.pullback₁ p).f).obj M)) := by
  classical
  let : Fintype U.I₀ := Fintype.ofFinite U.I₀
  have one (ab : U.I₀ × U.I₀) :=
    exists_finitePresentation_overlap_pair_map_lifting R c hc i f j hij U N hN hNq M e
      ab.1 ab.2
  let stage : U.I₀ × U.I₀ → I := fun ab ↦ (one ab).choose
  have hlift (ab : U.I₀ × U.I₀) := (one ab).choose_spec.choose_spec
  let : Nonempty I := ⟨j⟩
  obtain ⟨k, hk⟩ := (insert j (Finset.univ.image stage)).exists_le
  have hjk : j ≤ k := hk j (Finset.mem_insert_self _ _)
  let q := overlapStageMap R f hij hjk
  let V : (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u} :=
    U.pullback₁ q
  let p := overlapLimitMap R c f (hij.trans hjk)
  let A : (a : V.I₀) → (V.X a).Modules :=
    fun a ↦ (Scheme.Modules.pullback (U.pullbackHom q a)).obj (N a)
  let W : (pullback f (c.π.app (op i))).OpenCover.{u} := V.pullback₁ p
  let D := (modulesPseudofunctor.toDescentData W.f).obj M
  let ε : ∀ a, (Scheme.Modules.pullback (V.pullbackHom p a)).obj (A a) ≅ D.obj a :=
    overlapIteratedComparison U q p (overlapLimitMap R c f hij)
      (overlapLimitMap_stage_comp R c f hij hjk) N M e
  have pair (a b : U.I₀) := hlift (a, b) k hjk
    (hk (stage (a, b)) (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, rfl⟩)))
  let φ := fun (a b : U.I₀) ↦ (pair a b).choose
  have hφ := fun (a b : U.I₀) ↦ (pair a b).choose_spec
  have ha := exists_overlap_pair_transitions_comparison V A p D ε φ
  have hb := ha (by
    intro a b
    exact hφ a b)
  rcases hb with ⟨T, hT, hcomparison⟩
  refine ⟨k, hjk, ?_⟩
  change ∃ T : modulesPseudofunctor.OverlapTransitions V.f,
    (∀ a, Nonempty (T.obj a ≅ A a)) ∧
      Nonempty ((T.pull (p := p) (α := fun a ↦ a)
        (fun a ↦ V.pullbackHom_map p a)).Comparison D)
  refine ⟨T, ?_, hcomparison⟩
  intro a
  exact ⟨eqToIso (hT a)⟩

end AlgebraicGeometry
