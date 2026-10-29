# Closed loci detected on affine charts glue

`Langlands.AlgebraicGeometry.ClosedLocusFromAffineChartsStatement.{u}` says the
following. Take a subfunctor of the functor of points of a scheme `X` that is a
Zariski sheaf for one particular kind of cover. Suppose that over every affine
open `U` of `X` it is cut out by a closed subscheme of `U`. Then it is cut out by
one closed subscheme of `X`. This file defines the proposition only. It supplies
no proof.

## Exact interface

The statement quantifies over a scheme `X : Scheme.{u}` and a predicate
`P : ∀ ⦃Y : Scheme.{u}⦄, (Y ⟶ X) → Prop` on morphisms into `X` from schemes in
the same universe. It has three hypotheses.

1. *Stability under precomposition.* For all `f : Y' ⟶ Y` and `g : Y ⟶ X`,
   `P g` implies `P (f ≫ g)`. So `P` is a subfunctor of the functor of points
   of `X`.
2. *Locality over the affine opens of `X`.* For every `g : Y ⟶ X`, if
   `P ((g ⁻¹ᵁ V).ι ≫ g)` holds for every affine open `V` of `X`, then `P g`
   holds. Here `(g ⁻¹ᵁ V).ι` is the open immersion of the preimage `g⁻¹(V)`
   into `Y`. Only this one cover of `Y` is used, namely the preimages of all
   affine opens of `X`. Locality for arbitrary open covers of `Y` is not
   assumed.
3. *Affine charts.* For every affine open `U` of `X` there are a scheme `Z` and
   a closed immersion `ι : Z ⟶ U` such that, for every `g : Y ⟶ U`, `g`
   factors through `ι` (`∃ k, k ≫ ι = g`) if and only if `P (g ≫ U.ι)`. Here
   `U.ι` is the open immersion `U ⟶ X`. A chart is required for *every* affine
   open, not only for the members of a chosen cover.

The conclusion is that there are a scheme `Z` and a closed immersion
`ι : Z ⟶ X` such that, for every `g : Y ⟶ X`, `g` factors through `ι` if and
only if `P g`.

There is no restriction on `X`. It need not be quasi-compact, quasi-separated,
noetherian or reduced. All test schemes `Y` range over `Scheme.{u}`, the same
universe as `X`. The charts are only asserted to exist. No compatibility between
the charts on different affine opens is assumed; it follows from the hypotheses
because each chart is determined by `P`.

## Derived provenance

This is a derived, general form of a gluing step in the FLT Lean source
(`anthropic-flt-complete-lean-source-6e837e75`), module
`P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isClosedImmersion_iff_of_forall_affineOpens_chart.lean`.
That module proves the same gluing in universe `0` for one predicate over a
base `Spec R`: the pullback of a fixed rigidified line bundle along a test
morphism into `X` has trivial underlying line bundle. This statement replaces
that predicate by an arbitrary predicate `P` with properties 1 and 2 above, and
it works in an arbitrary universe `u`. The FLT proof uses exactly these two
properties of its predicate. It proves property 1 as `Triv.comp`, and it
derives the instance of property 2 that it needs from a hypothesis on global
functions of the abelian scheme.

Mathematically this is the familiar fact that a closed subscheme can be given
locally. A subfunctor of `X` that is a Zariski sheaf and is representable by a
closed subscheme over each affine open is representable by a closed subscheme
of `X`. The Lean statement is the version with exactly the hypotheses above.
No other source is cited for it.

In this project the statement is used to show that the agreement locus of two
rigidified line-bundle classes on an abelian scheme is closed. The affine
charts there come from an affine-base statement, and locality comes from
Zariski separatedness of rigidified classes.
