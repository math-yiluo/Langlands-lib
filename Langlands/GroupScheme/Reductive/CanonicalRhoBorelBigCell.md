# The canonical rho Borel pair and big-cell geometric data

This internal construction by Worker 1369 discharges the Borel-pair and Bruhat
covering inputs of the canonical rho big-cell construction using the published
`regularCocharacterBorel` and `absoluteBruhatCovering` proofs. The resulting
six-law geometric data still take a supplied split pinning, full integral
coroot span, and a supplied highest-weight representation at integral rho.
This is not a proof of the exact `SteinbergBigCellStatement`.

The local affine-parabolic instance has an explicit module-specific name so this
construction can be imported together with the canonical covariant-space
modules, whose analogous instance previously received the same generated name.

For `IsRootDatumOf.isBorelPair_polarization_rho`, fix an affine connected
reductive group over any field, its supplied split maximal torus, an actual
finite root datum on that torus, a base, and full integral coroot span. Write
`nu = P.Polarization (IntegralWeylVector.rho P b hspan)` and
`lambda = groupHom nu ≫ j`. The proved genericity of `nu` is definitionally
the regularity condition in the Borel classification theorem. Its first
clause proves that the actual affine dynamic parabolic of `lambda` is a
Borel subgroup. The original torus lies in the centralizer of each of its
cocharacters, hence in this parabolic. The represented-subgroup lifting
property constructs its factorization through the parabolic inclusion.
These facts give a Borel pair with the same original torus.

Over an algebraically closed field,
`IsRootDatumOf.bruhatCovering_polarization_rho` applies the published
absolute Bruhat covering theorem to this pair. It proves the rational-point
covering premise required by the canonical big-cell constructor, rather
than taking that covering as an assumption.

`SplitPinning.canonicalRhoBorelBigCellGeometricData` takes an algebraically
closed field `k : Type u`, an affine group scheme `G`, a supplied split
pinning `p` with finite root index, full integral coroot span, an actual
finite matrix representation, and its highest-weight certificate at rho.
The constructor obtains the actual conjugated-dual representation and
its three negative-rho extremal laws from
`negativeRhoExtremalRepresentationData`. It applies
`canonicalRhoBigCellGeometricData` to those data and the just-proved covering.
There is no additional Borel or Bruhat premise and no characteristic
assumption.

The result has left covariance, inverse right covariance, value one at
the identity, a nonzerodivisor coordinate, global opposite-parabolic
factorization wherever the coordinate takes a unit value, and a lift
through a diagonalizable subgroup for each point of the intersection.
The geometric laws keep every relative test scheme, including nonaffine,
nonreduced and empty tests. The intermediate rational-point Bruhat theorem
is used by the imported all-test unit-cell proof; it does not restrict the
test schemes in the result.

The five projection lemmas identify the original torus's diagonalizable
presentation, the actual polarized-rho parabolic, the constructed rational
opposition representative, the canonical extended negative-rho coordinate,
and the distinguished coefficient of the constructed conjugated dual.
The parabolic and weight coordinate depend only on the supplied pinning
and coroot span.

`canonicalRhoBorelBigCellData` additionally takes precisely the remaining
seventh law: cofinal powers of that same weight coordinate give finite
bases of the entire left covariant coordinate subspaces with irreducible
actual right regular rational representations. It appends this supplied
law using `withIrreduciblePowers`, preserving every geometric witness.
No cyclic subspace replaces the entire space.

The provenance is an internal derivation from the imported Library
proofs and constructions; no external source is cited. Structural existence,
full integral coroot span for simply connected groups, highest-weight
existence, and the whole-space seventh law remain obligations for the
exact host target. The general Borel-pair and covering lemmas do not
require algebraic closedness until the covering step.

Integration gives the local instances used here module-specific names to permit
joint imports. Their types, values, and local scopes are unchanged.
