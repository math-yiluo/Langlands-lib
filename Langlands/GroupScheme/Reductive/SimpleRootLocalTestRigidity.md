# Simple-root rigidity checked over local coefficient algebras

This internal derived module removes supplied Weyl normalization and target
root maps from a simple-root criterion for conjugating finite homomorphisms.
It uses the existing local-ring normalization theorem only to verify equality
of already fixed homomorphisms. It constructs no cover or conjugating point.

`RelativeIsogeny.hom_ext_of_simpleRootParametrizations` works over a local
commutative ring. Its inputs are two reductive groups, closed fibrewise maximal
coordinate tori, supplied finite reduced fibrewise root data, and a common
root-datum isogeny and torus homomorphism with the actual character identities
and both torus squares. Both ambient homomorphisms are finite. A base of the
source root datum and actual parametrizations of its simple roots are supplied.
If the two homomorphisms agree after these simple-root maps, they are equal.
No opposite-root parametrizations or Weyl identities are premises.

The proof constructs a Weyl-normalized source root family over the local ring
and actual target root parametrizations. It invokes the existing finite-map
rigidity theorem for those families. Each new source simple-root map differs
from its supplied counterpart by a unit, using the existing actual
root-parametrization comparison theorem. Precomposition by the corresponding
scaling map transfers the assumed equality. The existing rigidity theorem
then proves whole-group equality.

`SimpleRootLocalTestRigidityStatement` is the universally quantified,
Prop-valued form of this local-ring criterion.
`simpleRootLocalTestRigidity` proves it by the preceding theorem.

`TorusConjugates.of_simpleRootParametrizations` works over an arbitrary
commutative ring. It has the same geometric, common-root-datum and finite-map
premises, a supplied family of actual source simple-root parametrizations,
and a torus point on a parameter scheme. Its final premise is conjugation on
each of these root maps over every test scheme refining the parameter scheme.
It concludes conjugation on every source-group point over every such test.
It requires no global normalized family and no supplied target root maps.

The proof applies `TorusConjugates.of_localAlgebraHom`. Over each local
coefficient algebra it compares the base change of the first homomorphism
with the second homomorphism followed by the inner automorphism associated to
the chosen torus point. Base change preserves the fibrewise root data, maximal
tori, closed inclusions and source root parametrizations. Both maps are finite,
and their torus restrictions agree because conjugation by the commutative
target torus fixes the original torus restriction. The assumed root
conjugation gives actual equality of the simple-root restrictions there.
The local theorem proves equality of the two homomorphisms. The existing
local-algebra test criterion promotes these equalities to the claimed
all-scheme-test conjugation, including nonreduced tests.

The provenance is direct composition of the existing local normalized-root
family construction, unique unit comparison for actual root parametrizations,
finite-map simple-root rigidity, their base-change formulas, and the
local-algebra test criterion. No additional source theorem is asserted.
The module neither supplies intrinsic compatibility of root data with an
isogeny nor proves the unconditional isogeny-torus rigidity target.
