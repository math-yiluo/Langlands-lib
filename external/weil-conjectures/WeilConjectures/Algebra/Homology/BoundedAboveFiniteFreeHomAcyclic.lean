/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Algebra.Homology.FiniteFreeInternalHomExactSequence
import WeilConjectures.Algebra.Homology.BoundedHomExactColumns

/-! # Hom from bounded-above finite free complexes preserves bounded-below acyclicity

Source: Stacks Project, cohomology.tex, Tag 0GM8 (Lemma 20.51.4), case (2),
bounded-above finite free Hom calculation
(blueprint: lem-sc-bounded-above-finite-free-hom-acyclic).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- The total sheaf Hom from a bounded-above complex with finite free terms to a
bounded-below acyclic complex is acyclic.
Source: Stacks Project, cohomology.tex, Tag 0GM8, case (2)
(blueprint: lem-sc-bounded-above-finite-free-hom-acyclic).

Proof:
1. Choose an upper bound `N` for `E`. For every degree `p`, internal Hom from `E.X p`
   preserves short exact sequences by `lem-sc-finite-free-internal-hom-exact`:
   a finite free basis identifies the internal Homs with finite direct sums.
2. Choose a lower bound `M` for `A`. A degree-`m` cocycle section of the total Hom
   (`def-pur-hom-complex`) has components `z^p : E^p → A^(p+m)` only for
   `M-m ≤ p ≤ N`. Seek a degree-`m-1` section `h` with
   `d_A h^p + (-1)^m h^(p+1) d_E = z^p`. Set `h^p = 0` above `N` and descend.
   At degree `p`, the obstruction `z^p - (-1)^m h^(p+1) d_E` is a cycle: use the
   cocycle equation for `z`, the equation already solved at `p+1`, and `d_E² = 0`.
   Acyclicity identifies cycles with boundaries (`def-pc-acyclic-complex-modules`).
   Step 1 therefore lifts this obstruction through the differential locally on a covering.
   Below `M-m+1`, the target of `h^p` vanishes, so take `h^p = 0`; at the last degree
   the remaining obstruction is zero because the cycles in degree `M` are zero.
   There are only finitely many degrees needing lifts, hence finitely many covering
   refinements. On the final covering, `d(h) = z`. Every cocycle section is locally
   a boundary, so every cohomology sheaf of the total Hom vanishes. -/
theorem acyclic_homComplex_of_boundedAbove_finiteFree
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify J AddCommGrpCat.{max u v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    {R : Sheaf J CommRingCat.{w}}
    (E A : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
    (hEbounded : ∃ N : ℤ, ∀ p : ℤ, N < p → IsZero (E.X p))
    (hEfree : ∀ p : ℤ, ∃ r : ℕ, Nonempty (E.X p ≅ SheafOfModules.free
      (R := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
      (ULift.{w} (Fin r))))
    (hAbounded : ∃ M : ℤ, ∀ q : ℤ, q < M → IsZero (A.X q))
    (hAacyclic : A.Acyclic) : (CategoryTheory.homComplex E A).Acyclic := by
  obtain ⟨N, hN⟩ := hEbounded
  obtain ⟨M, hM⟩ := hAbounded
  apply acyclic_homComplex_of_bounded_exact_columns E A N M hN hM
  intro p q
  obtain ⟨r, ⟨e⟩⟩ := hEfree p
  exact finiteFree_internalHom_exact_sequence (E.X p) r e (A.sc q) (hAacyclic q)

end CochainComplex
