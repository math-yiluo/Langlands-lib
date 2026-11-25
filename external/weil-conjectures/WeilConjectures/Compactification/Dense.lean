/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.BoundaryPreparation
public import WeilConjectures.Compactification.NagataCompactification

/-!

# Dense compactifications

The construction `Rf_! = Rp_* j_!` of the exceptional direct image out of a compactification
`f = j ≫ p` is only well behaved when the open immersion `j` is *scheme-theoretically dense*.
This file names that condition on a `AlgebraicGeometry.Compactification` and combines the
two existing ingredients — the dense refinement of an arbitrary compactification
(`AlgebraicGeometry.Compactification.denseRefinement`) and Nagata's compactification theorem
(`AlgebraicGeometry.NagataCompactification`) — into an unconditional existence statement and
a chosen dense compactification.

## Main definitions

- `AlgebraicGeometry.Compactification.IsDense`: a compactification is dense if its open
  immersion is scheme-theoretically dominant;
- `AlgebraicGeometry.denseCompactification`: the chosen dense compactification of a
  separated, quasi-compact morphism locally of finite type over a quasi-compact
  quasi-separated base.

## Main results

- `AlgebraicGeometry.Compactification.isDense_denseRefinement`: the dense refinement of a
  compactification of a quasi-compact morphism is dense;
- `AlgebraicGeometry.exists_isDense_compactification` (blueprint:
  `lemma:nagata-two-open-dense-compactifications`): a separated, quasi-compact morphism
  locally of finite type over a quasi-compact quasi-separated base admits a dense
  compactification.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- A compactification is **dense** if its open immersion is scheme-theoretically dominant. -/
protected def Compactification.IsDense (c : Compactification f) : Prop :=
  IsSchemeTheoreticallyDominant c.i

/-- The defining property of a dense compactification, in the form usable by typeclass
search: if `c` is dense, then `c.i` is scheme-theoretically dominant. -/
theorem Compactification.IsDense.isSchemeTheoreticallyDominant {c : Compactification f}
    (hc : c.IsDense) : IsSchemeTheoreticallyDominant c.i :=
  hc


/-- The dense refinement of a compactification of a quasi-compact morphism is dense
(blueprint: `prop:nagata-dense-refinement`). -/
theorem Compactification.isDense_denseRefinement (c : Compactification f) [QuasiCompact f] :
    c.denseRefinement.IsDense :=
  c.isSchemeTheoreticallyDominant_denseRefinement_i

variable (f) in
/-- **Existence of dense compactifications** (blueprint:
`def:nagata-two-open-dense-compactifications`, `lemma:nagata-two-open-dense-compactifications`).

A separated, quasi-compact morphism locally of finite type over a quasi-compact
quasi-separated base admits a compactification whose open immersion is scheme-theoretically
dominant: compactify by Nagata's theorem and pass to the dense refinement. -/
theorem exists_isDense_compactification [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] :
    ∃ c : Compactification f, c.IsDense :=
  ⟨_, (NagataCompactification f).isDense_denseRefinement⟩

variable (f) in
/-- The **chosen dense compactification** of a separated, quasi-compact morphism locally of
finite type over a quasi-compact quasi-separated base: the dense refinement of the
compactification produced by `AlgebraicGeometry.NagataCompactification`. -/
noncomputable def denseCompactification [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] : Compactification f :=
  (NagataCompactification f).denseRefinement

variable (f) in
/-- The chosen dense compactification is dense. -/
theorem denseCompactification_isDense [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] :
    (denseCompactification f).IsDense :=
  (NagataCompactification f).isDense_denseRefinement

end AlgebraicGeometry
