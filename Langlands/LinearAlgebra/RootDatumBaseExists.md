# Bases of finite reduced integral root data

This internal derived module proves base existence for a finite reduced
`RootDatum J M N` on its original integral modules. It assumes neither that
the roots span the weight lattice nor that the coroots span the coweight lattice.
The index type is finite; the two perfectly paired additive groups and the index
type may live in independent universes. No finite-generation assumption on the
ambient groups is needed for this construction.

`exists_regular_functional` constructs an integral linear functional nonzero on
every root. Its finite-avoidance lemma inducts on a finite family of nonzero
additive functionals. Given a point regular for the previous family and a point
where the next functional is nonzero, it varies their sum by an integer multiple
of the latter point. Each functional vanishes at at most one parameter, or at
none when its slope is zero. An integer outside the finite exceptional set
extends regularity. Apply this to the root pairing on the coroot module, using
the self-pairing value two, then transpose the selected point to the root dual.

`baseOf_root_eq_baseOf_coroot` identifies the indecomposable positive-root and
positive-coroot index sets whenever two regular integral functionals give
matching positive signs. It installs `Fintype J` from the supplied `Finite J`
and reuses `Langlands.GroupScheme.SplitExistence.baseOf_root_eq_baseOf_coroot`
from `GroupScheme/SplitExistence/IntegralBase`.

`nonempty_base` reuses the published `nonempty_base_int` from that same module.
Its hypotheses and conclusion are unchanged: a finite reduced integral root
datum has a base on its original modules, with no spanning premise.
`base` chooses such a base using `Classical.choice`. The chosen-base interface
remains separate from the proposition asserting existence; no compatibility
with other independently chosen bases is claimed.

The provenance is internal, from the finite-avoidance construction above and
the published integral-base results. The latter supply the matching-sign,
independence and sign-generation argument documented in their paired Markdown.
This module does not assert base compatibility with an actual Levi root subset,
a Weyl correction, or any group-scheme existence theorem.
