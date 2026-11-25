/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.ClosedImmersionTwistCohomologyBound
import WeilConjectures.AlgebraicGeometry.ClosedImmersionTwistVanishingStep

/-! # Fixed-degree projective Serre vanishing

Source: Stacks Project, Tag 01YS (4).
(blueprint: lem-pc-c2-closed-immersion-fixed-degree-vanishing)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- Fixed-degree projective Serre vanishing, split from the affine restriction theorem.
Source: Stacks Project, Tag 01YS (4), proof by descending induction.
(blueprint: lem-pc-c2-closed-immersion-fixed-degree-vanishing)

Proof: projective space over A and its closed subscheme X are locally Noetherian.
Thus the quasi-coherent finitely presented F is coherent, as is its pushforward G.
The standard N+1 affine opens give H^j(G)=0 for j>N. Descend from that bound,
for all coherent modules G simultaneously. Choose a surjection from a finite
sum of twists O(a) onto G; its kernel K is coherent. Tensor the kernel sequence
with the invertible O(t), preserving exactness. For t at least every -a, the
positive-degree cohomology of the finite sum vanishes by the projective twist
calculation. The induction hypothesis kills H^(j+1)(K(t)) for all sufficiently
large t. The long exact sequence therefore kills H^j(G(t)) for such t.
Apply this at j=q and replace the resulting integer threshold by its maximum
with zero. The projection formula identifies G(t) with i_*(F tensor i^*O(t));
closed immersions are affine, so their cohomology comparison identifies its
cohomology with that on X. This proves the required natural-number threshold. -/
theorem exists_isZero_closedImmersion_twist_degree
    (A : Type u) [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} {N : ℕ}
    (i : X ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A))) [IsClosedImmersion i]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] (q : ℕ) (hq : 0 < q) :
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
        (tensorObj F (ProjectiveSpace.twistRestrict i t))) := by
  let P (r : ℕ) : Prop := ∀ {Y : Scheme.{u}}
    (j : Y ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A))) [IsClosedImmersion j]
    (G : Y.Modules) [G.IsQuasicoherent]
    [G.IsFinitePresentation], ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      IsZero ((RingedSpace.moduleCohomology Y.toRingedSpace r).obj
        (tensorObj G (ProjectiveSpace.twistRestrict j t)))
  have hbase (r : ℕ) (hr : N < r) : P r := by
    intro Y j _ G _ _
    exact ⟨0, fun t _ ↦ isZero_closedImmersion_twist_above_dimension A j G r t hr⟩
  by_cases hlarge : N < q
  · exact hbase q hlarge i F
  · have hqN : q ≤ N + 1 := by omega
    have hd : P q := Nat.decreasingInduction' (P := P) (n := N + 1) (m := q)
      (fun r _ hqr hn Y j _ G _ _ ↦
        exists_isZero_closedImmersion_twist_of_next_degree
          A j r (by omega) hn G) hqN (hbase (N + 1) (by omega))
    exact hd i F

end AlgebraicGeometry.Scheme.Modules
