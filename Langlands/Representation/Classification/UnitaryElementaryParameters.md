# Elementary actual unitary inducing parameters

Author: Worker 1431.

This is a derived finite construction from the published actual representation
interfaces. It supplies the singleton and repeated-pair parameters needed when
assembling unitary generic inducing data. It assumes a supplied block and its
local properties; it does not prove `UnitaryGenericExhaustion`, Speh elimination,
unitary induction, or genericity.

All declarations allow an arbitrary prime `p`, `F : PadicField.{uF} p`, and
compatible `T : F.TopologicalData`. The field and representation universes
`uF` and `uV` are independent. Every supplied and constructed smooth complex
representation uses the carrier universe `max uF uV` and the topology from `T`.

## Singleton

For `r > 0` and an actual smooth representation `δ` of `GL_r(F)`,
`singletonUnitaryBlocks` is the constant family with value `δ`, indexed by the
published `CuspidalSupport.LeviAdmissibility.oneBlock r hr`. This shape has one
block of rank exactly `r`, so its total rank is `r`.

`isUnitaryGenericDatum_singleton` assumes that `δ` is irreducible,
unitarizable, and analytically square-integrable, using exactly the predicates
in `UnitaryGenericStatement`. Unitarizability here means existence of the
published invariant positive Hermitian form. The conclusion is validity of
the singleton with exponent zero. The proof copies the three block properties,
checks `-1/2 < 0 < 1/2`, and uses the identity permutation, reflexive rank
equalities, and identity block isomorphisms for Hermitian symmetry.

`singletonUnitaryProductIso` constructs the categorical isomorphism

```text
T.twistedProductInduced (oneBlock r hr) (singletonUnitaryBlocks … δ) (fun _ => 0)
  ≅ δ.
```

This isomorphism needs no irreducibility, unitarizability, or integrability
hypothesis. Its implementation applies `singleBlockNormalizedProductEquiv`
to the unique index, uses `realPowerTwist_zero` to identify the block action,
and composes with the published `castRankEquiv`. `SmoothRep.mkIso` packages
the resulting actual equivariant linear equivalence. The one-block comparison
uses the existing normalized upper-parabolic product, including its actual
action; it is not an equality merely of representation classes.

## Repeated pair

`pairedUnitaryBlocks` puts the identical actual representation `δ` at both
indices of `BlockShape.uniform 2 r hr`, whose total rank is `2 * r`.
`pairedUnitaryExponents α` assigns `α` to index zero and `-α` to index one.
Both occurrences of the block remain in the family.

`hasHermitianSymmetricParameters_paired` holds for every real `α` without a
bound. It uses `Fin.revPerm`, which swaps the two indices. Each matched rank
equality is reflexive and each transported block isomorphism is the identity.
The two exponent identities are checked separately by `fin_cases`.
Consequently this is the exact multiplicity-preserving same-block Hermitian
symmetry from `UnitaryGenericStatement`; no ordinary self-contragredience of
`δ` is assumed.

`isUnitaryGenericDatum_paired` assumes the same three block properties as the
singleton theorem and additionally `0 < α < 1/2`. It copies those properties
at both indices, verifies the strict bounds for `α` and `-α` by linear
arithmetic, and reuses the preceding symmetry theorem. Neither endpoint is
included.

## Provenance and scope

These definitions and their verification are elementary consequences of the
published block shapes, real twists, one-block evaluation, and finite parameter
predicates. They introduce no external source assertion, no assumed classifier,
and no additional existence premise. The square-integrable block and its
properties are inputs. The results support finite assembly of an exhaustion
proof but do not assert that every unitary generic representation has such
parameters or that the paired induced representation is irreducible or
unitarizable.
