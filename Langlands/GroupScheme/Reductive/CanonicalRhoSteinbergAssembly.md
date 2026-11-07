# Cofinal Steinberg powers and canonical big-cell assembly

Worker 1369's internal assembly combines the proved finite dimensionality of the
entire canonical covariant space with explicit highest-weight existence and
per-height irreducibility inputs. It constructs complete big-cell data for a
supplied split pinning and full integral coroot span. It does not prove
`SteinbergBigCellStatement`.

The arithmetic lemma `exists_pos_steinbergHeight` proves that, for a prime
natural number `q` and every bound `e`, there is a positive `r` with
`e ≤ q ^ r - 1`. The proof takes `r = e + 1` and uses the elementary strict
growth bound for powers with base greater than one.

Fix an affine group scheme `G` over a field `k : Type u`, a supplied split
pinning `p`, and full integral coroot span `hspan`. Write `rho` for its integral
Weyl vector, `nu` for the polarization of `rho`, `iP` for the actual affine
dynamic parabolic inclusion of `groupHom nu ≫ p.inclusion`, and `chi` for
the canonical extended negative-rho coordinate on that parabolic.
`isDominantWeight_nsmul_rho` proves that every natural multiple of `rho` is
dominant: its pairing with each simple coroot is the corresponding
nonnegative integer. Over an algebraically closed field,
`exists_highestWeight_nsmul_rho` specializes an explicitly supplied
`SplitDominantHighestWeightRepresentationsExistStatement` to these weights.
The highest-weight existence proposition is a premise, not an invoked proof.

With a finite root index and exponential characteristic `q`,
`canonicalRhoSteinbergBasis` constructs a basis indexed by
`Fin (Module.finrank k V)` of the full space
`V = p.canonicalRhoCovariantSubspace hspan (q ^ r - 1)`.
It installs the finite-dimensionality result proved by same-height Frobenius
restriction and applies `Module.finBasis`. It makes no irreducibility
assumption and imposes no positive-height condition.

`CanonicalRhoSteinbergHeightIrreducibility` is an unproved `Prop`-valued
interface for the remaining representation-theoretic input. For each positive
height `r`, each supplied actual highest-weight matrix representation at
`(q ^ r - 1) • rho` implies rational irreducibility of the actual right regular
representation on the entire space `V`, in every finite `Fin m` basis.
It does not replace `V` with a cyclic or matrix-coefficient subspace.

`canonicalRho_irreduciblePowers_of_heightIrreducibility` takes a prime `q`,
exponential characteristic, the explicit highest-weight existence proposition
and this explicit per-height interface. For each prescribed exponent bound
it chooses a positive height above the bound, obtains a highest-weight
representation at the corresponding multiple of `rho`, chooses the full-space
finite basis just constructed and applies the per-height input. Its conclusion
is precisely the seventh law for the same `iP` and the powers of the same `chi`.

`canonicalRhoSteinbergBigCellData` chooses a highest-weight representation at
`rho` from the supplied existence premise. It applies the existing
`canonicalRhoBorelBigCellData`, with its proved Borel pair, proved Bruhat
covering and all six geometric laws, and supplies the cofinal seventh law.
The projection lemmas identify the subgroup map and weight coordinate with
`iP` and `chi`. The geometric laws continue to quantify over every relative
test scheme without reducedness or affineness restrictions.

The provenance is an internal derivation from the imported Library
constructions, proved Frobenius detection and elementary natural-number
arithmetic. No external assertion is introduced. Split-pinning existence,
integral coroot generation, highest-weight existence and per-height whole-space
irreducibility remain explicit obligations for the exact host proposition.
