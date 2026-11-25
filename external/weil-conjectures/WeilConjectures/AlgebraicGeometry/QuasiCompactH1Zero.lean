/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.PQFCohomology

import WeilConjectures.AlgebraicGeometry.H1ClosedPointAffineBasicOpen
import WeilConjectures.AlgebraicGeometry.H1FiniteBasicCoverUnitIdeal

/-! # Serre's quasi-compact vanishing criterion

Source: Stacks Project, Tag 01XF, label lemma-quasi-compact-h1-zero-covering
(blueprint: lem-pqf-quasicompact-h1-zero).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A quasi-compact scheme whose first cohomology vanishes on every
quasi-coherent ideal sheaf is affine.

Source: Stacks Project, Cohomology of Schemes, Lemma Tag 01XF, lines 283--388
(blueprint: lem-pqf-quasicompact-h1-zero).

Proof: (1) For a closed point `x`, choose an affine neighbourhood `U` and
the reduced closed subschemes on `X \ U` and `(X \ U) ∪ {x}`.  Their ideal
sheaves have quotient restricting to the residue field at `x` and supported
at `x`; the long exact sequence and the H¹ hypothesis lift its unit to a
global section whose principal open is an affine neighbourhood of `x`.
(2) The union of affine principal opens contains every closed point.  A
quasi-compact scheme is Kolmogorov, so a nonempty complement would contain a
closed point; hence finitely many such principal opens cover `X`.
(3) The sections defining this cover give a surjection from a finite free
module sheaf to `\mathcal O_X`.  Filter its kernel by the summands.  Each
successive quotient is a quasi-coherent ideal, so induction with the long
exact sequence gives H¹-vanishing for the kernel.
(4) The long exact sequence then makes the corresponding global sections
generate the unit ideal of `Γ(X, \mathcal O_X)`.
(5) The affine basic-open unit-ideal criterion applied to this finite cover
concludes that `X` is affine.  The proof uses
`lem-weil-pbc-reduced-induced-closed-subscheme`,
`lem-sc-quasi-compact-kolmogorov-closed-point`,
`lem-weil-pbc-derived-functor-long-exact`, and
`lem-weil-pbc-affine-unit-ideal-basic-opens`.
-/
theorem quasiCompact_affine_of_h1_ideal_zero (X : Scheme.{u})
    [CompactSpace X]
    (hI : ∀ (I : X.IdealSheafData), I.toModules.IsQuasicoherent →
      Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I.toModules)) :
    IsAffine X := by
  classical
  let s : Set Γ(X, ⊤) := {f | IsAffineOpen (X.basicOpen f)}
  let W : Set X := ⋃ f ∈ s, (X.basicOpen f : Set X)
  have hW : IsOpen W := isOpen_iUnion fun f ↦ isOpen_iUnion fun _ ↦
    (X.basicOpen f).isOpen
  have hcover : (Set.univ : Set X) ⊆ W := by
    intro x _
    by_contra hx
    obtain ⟨y, hy, hyclosed⟩ := hW.isClosed_compl.exists_closed_singleton ⟨x, hx⟩
    obtain ⟨f, hyf, hf⟩ :=
      exists_affineBasicOpen_of_isClosed_singleton_of_h1_ideal_zero X hI y hyclosed
    exact hy (Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨hf, hyf⟩⟩)
  obtain ⟨t, hts, htfinite, htcover⟩ := isCompact_univ.elim_finite_subcover_image
    (fun f (_ : f ∈ s) ↦ (X.basicOpen f).isOpen) hcover
  have ht : Ideal.span t = ⊤ :=
    span_eq_top_of_finite_basicOpen_cover_of_h1_ideal_zero X hI t htfinite (by
      intro x
      rcases Set.mem_iUnion.mp (htcover (Set.mem_univ x)) with ⟨f, hf⟩
      rcases Set.mem_iUnion.mp hf with ⟨hft, hxf⟩
      exact ⟨f, hft, hxf⟩)
  exact isAffine_of_isAffineOpen_basicOpen t ht (fun f hf ↦ hts hf)

end AlgebraicGeometry
