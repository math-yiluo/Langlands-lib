/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSortingOperators
public import Mathlib.Algebra.Homology.Homotopy
import WeilConjectures.AlgebraicGeometry.AlternatingCechSortedContraction
import WeilConjectures.AlgebraicGeometry.AlternatingCechSortingBoundaryTransport
import WeilConjectures.AlgebraicGeometry.AlternatingCechFirstSortingIdentity
import WeilConjectures.CategoryTheory.SiteCechComplex

/-!
# The second Čech sorting identity

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM.
(blueprint: lem-pc-alternating-cech-second-sorting-identity)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The repeated-tuple operator contracts stable sorting minus alternating projection.

Source: Stacks 01FM, equation 20.23.6.2, transported by signed stable sorting.
(blueprint: lem-pc-alternating-cech-second-sorting-identity)

Proof: Restrict signed stable sorting κ to nondecreasing tuples: it is identity there,
and its values on arbitrary tuples are recovered by signed stable-sorting pullback.
The first identity implies κ commutes with d, since d squared is zero. On the complex
of nondecreasing tuples define K by duplicating the first repeated value at position a,
with sign (-1)^a; set K to zero on increasing tuples. The first-repeat filter in the
formula selects precisely that a, and no a when the tuple is increasing.
Expand dK+Kd on a nondecreasing tuple. For a strictly increasing tuple every face is
strictly increasing, so all terms vanish. Otherwise let a be the first equality.
Terms deleting an entry before a pair with the corresponding face term, whose first
equality is in position a-1, with opposite signs. Terms deleting an entry after the
repeated pair similarly match a face term with first equality a. The two face terms
deleting the equal occurrences coincide and have opposite signs, so cancel even if
that face has no remaining equality. The duplicated tuple has three equal consecutive
entries at a, a+1, a+2. Deleting these gives the original tuple with total coefficient
(-1)^a*((-1)^a+(-1)^(a+1)+(-1)^(a+2))=1. These are all terms, proving id minus the
operator killing repeated tuples. Transports of paired terms agree because all their
projections agree. Pull this identity back by signed stable sorting and precompose
with κ. The concrete pulled-back operator is cechSecondSortingHom: a duplicated
nondecreasing tuple is already stably sorted. The resulting right side is κ-P,
where P is the unique strictly increasing sorted permutation on injective tuples
and zero otherwise, exactly cechAlternatingProjectionMap. Degree zero has no repeated
tuple and both sides vanish. Empty I gives zero groups. -/
theorem cechSecondSortingIdentity (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) (p : ℕ) :
    (Homotopy.nullHomotopicMap' (cechSecondSortingFamily X U F S)).f p =
      cechStableSortingMap X U F S p - cechAlternatingProjectionMap X U F S p := by
  classical
  apply AddCommGrpCat.ext
  intro s
  funext t
  rw [cechSortingBoundaryTransport X U F S p s t]
  change _ = (cechStableSortingMap X U F S p) s t -
    (cechAlternatingProjectionMap X U F S p) s t
  change _ = (∑ σ : Equiv.Perm (Fin (p + 1)),
    if cechStableSort t σ then
      (Equiv.Perm.sign σ : ℤ) • F.map (S.indexMap t σ).op (s (t ∘ σ)) else 0) -
    (∑ σ : Equiv.Perm (Fin (p + 1)),
    if StrictMono (t ∘ σ) then
      (Equiv.Perm.sign σ : ℤ) • F.map (S.indexMap t σ).op (s (t ∘ σ)) else 0)
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  have hs : StrictMono (t ∘ σ) → cechStableSort t σ := by
    intro h
    refine ⟨h.monotone, ?_⟩
    intro i j hij he
    exact (ne_of_lt (h hij) he).elim
  by_cases hsort : cechStableSort t σ
  · rw [ite_eq_left hsort, cechSortedContraction X U F S p s (t ∘ σ) hsort.1]
    by_cases hstrict : StrictMono (t ∘ σ)
    · simp [hsort, hstrict]
    · simp [hsort, hstrict]
  · have hstrict : ¬ StrictMono (t ∘ σ) := fun h ↦ hsort (hs h)
    simp [hsort, hstrict]

end AlgebraicGeometry.Scheme
