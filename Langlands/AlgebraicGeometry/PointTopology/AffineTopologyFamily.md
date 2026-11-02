# Topology families and the polynomial coproduct of affine lines

Author: Worker 105.

This is derived supporting infrastructure for the uniqueness argument in Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Proposition 2.1 and the first paragraph of its proof, printed page 2.
Registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

`AffinePointTopologyFamily R S` is the type of assignments of a topology to
each actual algebra-map point set `AlgPoint R A S`, where `A` ranges over
all finite-type commutative `R`-algebras in the universe of `R`. The value
algebra `S` may occupy an independent universe. It is a type of assignments,
with no assumed functoriality, product or embedding conclusions.
`evaluationAffineTopologyFamily` supplies an actual assignment using the
published evaluation topologies. Only `S` has a topology.

`polynomialLineCofan R ι` is the cocone in Mathlib's actual `CommAlgCat R`
whose vertex is `MvPolynomial ι R` and whose factors are one-variable
polynomial algebras `MvPolynomial Unit R`. Its `i`th map sends the sole
variable to the variable indexed by `i`. `polynomialLineCofanIsColimit`
proves its coproduct universal property: a family of algebra maps from
the one-variable algebras determines the map from the multivariate
polynomial algebra by evaluating each variable at its prescribed image.
Polynomial extensionality proves factorization and uniqueness. The
construction and proof also include the empty index type.

This implements the algebraic content of viewing affine space as a
product of affine lines in the cited argument. The coordinate objects
and maps are existing polynomial algebras and actual algebra maps;
no product comparison or desired topology is included as assumed data.
The published `specPointEquiv` identifies these algebra points with
actual spectrum-valued relative scheme points. A separate uniqueness
theorem must still impose the source's topological axioms and prove
that an arbitrary satisfying assignment agrees with the evaluation
assignment; this file does not claim that theorem or all of Proposition 2.1.
