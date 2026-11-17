# Whole-group conjugation from actual simple-root restrictions

This internal derived module supplies the transport and assembly step between
actual simple-root conjugation equations and conjugation on the whole group.
The root-datum isogeny and compatible torus map remain supplied. It does not
construct those data or a conjugating point.

## Coordinate transport and finiteness

`splitTorus.coordinateBaseChangeHom` pulls back a homomorphism between two
coordinate tori and restores the standard coordinates with the canonical
base-change isomorphisms. `coordinateBaseChangeHom_character` preserves a
specified integral character formula. `coordinateBaseChangeHom_square`
preserves the actual ambient torus square. The proofs use the published
character base-change identity, functoriality, and cancellation of the
canonical isomorphisms.

`isFinite_torusConjugateAlgebraHom` proves that the actual pulled-back ambient
homomorphism followed by the inner automorphism at an evaluated torus point
is finite. Its proof uses the Cartesian square of the original homomorphism,
stability of finite morphisms under base change, and composition with an
isomorphism.

## From simple-root comparisons to whole-group conjugation

`TorusConjugates.of_simpleRootRestrictions` works over an arbitrary commutative
ring R. The source and target are affine reductive group schemes with supplied
closed fibrewise maximal coordinate tori, finite reduced fibrewise root data
P and Q, and a root-datum isogeny r from Q to P. A supplied actual torus map
has character map r.weightMap. Both finite ambient homomorphisms have this
same torus square. Their flatness and surjectivity are not required here.

For a base b of P, the theorem also takes actual parametrizations of every
positive simple source root and its negative, and of the corresponding target
roots and their negatives. The target index for a source root alpha is
r.indexEquiv.symm alpha. The source Weyl points built from these
parametrizations must implement the corresponding root reflections. The
parameter scheme V is arbitrary over Spec R. The final input supplies
`TorusConjugatesOnRoot` for each positive simple source root: the conjugation
equation holds on every scheme refining V and at every additive coordinate.
The conclusion is `TorusConjugates` for the two full ambient homomorphisms,
with the same supplied V-point of the target torus.

The proof evaluates the supplied point over each local R-algebra A.
`torusConjugateAlgebraHom_root` gives equality of the positive simple
restrictions of the first pulled-back homomorphism and the conjugated second
homomorphism. Commutativity of the target torus preserves its restriction.
The coordinate transport lemmas preserve the common torus square and weight
formula. Root data, reductivity, maximal tori, closedness, parametrizations,
and source Weyl normalization all survive base change. Both compared maps
are finite, the second by the finiteness lemma above. The existing
`RelativeIsogeny.hom_ext_of_simpleRootRestrictions` therefore identifies the
two actual homomorphisms over A. Finally,
`TorusConjugates.of_localAlgebraHom` reconstructs the all-test conjugation
predicate over V from these local-algebra equalities.

No reduction to residue fields occurs. Coefficient algebras and test schemes
with nilpotents are included. The internal provenance is exactly the
combination of the published base-change APIs, the actual algebra-conjugate
construction and generator comparisons, and the supplied-root finite-map
extensionality theorem. Existence of compatible root data and of the
simple-root conjugation equations remains a separate obligation of the
unconditional isogeny rigidity target.
