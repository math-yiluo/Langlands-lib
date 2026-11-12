# Rational-subgroup minima for actual representation-vector heights

Author: Worker 83.

This module constructs the normalized primitive-vector height for an actual
algebraic matrix representation and proves existence of a minimizing
translate in every rational subgroup. It supplies a single-representation
height-minimization step, with exact comparison of scheme points and
matrices.

## Construction and scope

Let `F : Type u` be any number field, `G` any group scheme over `F`,
and `ρ : MatrixRepresentation G (Fin n)` an actual group-scheme
homomorphism into the general linear group. No affineness, reductivity
or splitness hypothesis on `G` is needed beyond the supplied representation.

`rationalMatrix` evaluates this representation on the actual coefficient
group `RationalGroupPoints F G`. The existing `adelicMatrix` from
`AdelicRepresentationHeight` evaluates the same representation on full
adelic points.

`orbitHeight F G ρ v g` is
`PrimitiveAdelicHeight.rationalHeight F n (adelicMatrix F G ρ g) v`.
It uses maximum coordinate norms at each place, normalized finite absolute
values and the archimedean multiplicities from the existing height. This is
the height of the vector `ρ(g) v`, not a height of the matrix and its inverse.
It is positive when `v ≠ 0`.

For any subgroup `Q` of the actual rational points, any nonzero rational
vector `v`, and any adelic `g`, `exists_min_orbitHeight` produces
`q : Q` such that

`orbitHeight(v, g · rational(q)) ≤ orbitHeight(v, g · rational(r))`

for every `r : Q`. No discreteness, finite generation or algebraicity
condition on `Q` is assumed. The nonzero vector premise rules out `n = 0`
automatically; there is no hidden choice of a coordinate in zero dimension.

`minimumOrbitTranslate` chooses such a `q` in the same subgroup.
`minimumOrbitTranslate_min` says that the translated point cannot be
improved by any further right translation in `Q`.

## Implemented proof

`adelicMatrix_rational` applies the published naturality theorem
`MatrixRepresentation.affineMatrix_naturality` to the principal adele
algebra map. It identifies the actual adelic matrix of a rational point
with the entrywise principal matrix of its rational representation.
The representations on rational and adelic points are thus compared,
rather than identified by assumption.

Using this equality and the homomorphism law, `orbitHeight_mul_rational`
reduces right translation to the published
`PrimitiveAdelicHeight.rationalHeight_mul_rational`.

For the minimum, take the set of rational vectors
`{ρ(r) v | r ∈ Q}`. It is nonempty because `Q` contains the identity,
and it excludes zero because each rational representation matrix is
invertible. Apply the published
`PrimitiveAdelicHeight.exists_min_rationalHeight_on` to this set and
the fixed adelic matrix `ρ(g)`. A preimage of the minimizing vector
gives `q`. The translation formula proves the claimed inequality.
Finally, apply that inequality to `q * r` and use the principal-map
homomorphism law to prove `minimumOrbitTranslate_min`.

## Provenance and limits

This is a derived transport of the Library's proved rational-vector
minimum to an actual representation and a rational subgroup.
The mathematical context is Springer (1994), §1.8 on primitive-vector
heights and §2.3 on the height-minimal sets used in rank induction.

The module does not prove simultaneous minimality for a chain of
adapted representations. In such a chain one must also prove that
subsequent rational subgroup translations preserve the earlier heights.
It does not construct adapted representations, compare highest weights
with roots, prove a rank-one bound or provide a chamber threshold.
Those remain separate obligations for the fundamental-set theorem.

## Source

T. A. Springer, *Reduction theory over global fields*, Proc. Indian Acad.
Sci. (Math. Sci.) 104 (1994), 207–216. Registered source:
`springer-1994-reduction-global-fields`, SHA-256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`.
Used as context: §1.8, printed pp.209–210, primitive vectors and height
properties; §2.3, printed p.212, height-minimal sets for adapted
representations. The complete paper was read. The implemented proof uses
the published Library minimum theorem described above, rather than
assuming the printed simultaneous-minimum assertion.
