# NYLL M266.014: surjectivity of the unramified norm class projection

The theorem
`Langlands.NYLL.LocalClassFieldTheory.unramifiedNormClass_surjective`
has exactly the published target type
`Langlands.NYLL.LocalClassFieldTheory.unramifiedNormClass_surjectiveStatement`.
It says that every element of
`Kˣ ⧸ unramifiedNormSubgroup K n` is the image of a field unit under
`unramifiedNormClass K n`.

The target retains arbitrary `K : Type u` with
`[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]`,
followed by unrestricted `n : Nat`. In particular, `n = 0` is included.
The theorem explicitly retains universe parameter `u`.

## Implemented proof

The proof introduces the target's field, four instances and natural number.
The published definition of `unramifiedNormClass K n` is
`QuotientGroup.mk' (unramifiedNormSubgroup K n)`. Mathlib's
`QuotientGroup.mk'_surjective`, applied to this subgroup, therefore closes the
goal by definitional equality. Every quotient class has a representative.
The existing normality instance for subgroups of the commutative group `Kˣ`
supplies the quotient-group instance.

The sole import is the published module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.QuotientStatements`,
which imports the quotient projection and its subgroup. All data and the
statement are reused by Lean name. The proof requires no valuation-surjectivity
result or positivity condition on the modulus.

## Source and adaptation

The source is Naganori Yamaguchi's ClassFieldTheory, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`,
theorem `LocalClassFieldTheory.unramifiedNormClass_surjective`, lines 156–159
(M266.014). The source passage and its preceding definitions were read.
The verified full-file SHA-256 is
`ed3c13cfacb92012fb235f48817d5f23a043588ef78d7b2ed2e7ef4afa533b12`.
The source is registered as `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/` followed by that file path.
No applicable project errata entry was found.

Worker 562 added the `Langlands.NYLL` namespace prefix, replaced the explicit
source telescope by the exact closed Library statement, introduced its
parameters in the proof, and replaced the original broad imports with the
focused published target module. The source proof term is unchanged apart
from namespace resolution. The source author and copyright header are retained,
with a modification record. The Apache-2.0 license and notices are already
published in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

## Development validation

A Lean-service check in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled this module with zero
errors and warnings. Declaration inspection reported a theorem with universe
parameter `u`, depending only on `propext`, `Classical.choice` and `Quot.sound`.
This development check is separate from independent acceptance and publication.
