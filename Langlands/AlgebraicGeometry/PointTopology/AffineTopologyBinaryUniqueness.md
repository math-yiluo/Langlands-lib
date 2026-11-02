# Affine topology uniqueness from binary fibre products

Author: Worker 105.

This proof develops the coordinate-algebra part of the uniqueness
argument in Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Proposition 2.1, printed page 2. Registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The hypotheses concern topologies on the actual algebra-map point sets of
finite-type coordinate algebras. They are functoriality, compatibility with
actual binary pushouts, embeddings for surjective coordinate maps, and the
given topology on the polynomial line. Finite coproduct compatibility is
derived for the needed polynomial algebras, rather than imposed.

Functoriality makes restriction along an algebra isomorphism a homeomorphism
because both that restriction and its inverse are continuous. It follows that
agreement with the evaluation topology transports along algebra isomorphisms.
The polynomial algebra with no variables has a subsingleton point set and hence
only one topology. Adjoining one variable is the actual pushout constructed in
`AffinePolynomialPushouts`. Every pair of points is compatible over the initial
base algebra, so the compatible-pair subspace is homeomorphic to the full
product. The inductive hypothesis and line axiom give the product topology on
generator values; splitting a function on `Option ι` into its old and new
coordinates is an explicitly constructed homeomorphism. This identifies the
polynomial point topology with its evaluation topology.

Finite empty/option induction, including transport along equivalences of index
types, proves this for every finite polynomial algebra. Finally, every finite-type
algebra is a quotient of a finite polynomial algebra. The quotient-embedding
axiom and the independently proved evaluation embedding have the same induced
topology, giving equality on all coordinate algebras.

Only the value ring has a topology, with continuous ring operations; no
Hausdorffness, locality or finite presentation is imposed. The base ring and
coordinate algebras have a common universe, while the value ring may lie in a
different universe. Comparison with actual scheme topology families and
existence of the full source axiom package remain separate obligations.
