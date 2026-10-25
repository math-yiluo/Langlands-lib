# Prime ramification arithmetic support

This module proves the total-inertia bridge and the prime-degree tame/wild
criterion for arbitrary independent field universes and the supplied compatible
algebra. It supplies internal support for the exact theorem in
`PrimeRamificationBreakProof`; that module combines this arithmetic with
`PrimeInertiaBreakSupport` to prove `PrimeTotallyRamifiedBreak`.

## Canonical total inertia

`extensionDegree_suppliedAlgebra` compares the algebra induced by the supplied
compatible embedding with the supplied algebra using `Algebra.algebra_ext`.
The published fundamental identity `ramificationIndex_mul_extensionResidueDegree`
and positivity of the absolute ramification index then imply relative residue
degree one in `extensionResidueDegree_supplied_eq_one`.

The one-dimensional residue vector space supplies a residue representative
coming from a base-field integer. Each actual base-field automorphism fixes
that integer. This proves `fixedResidueRepresentatives_suppliedAlgebra`.
The published `lowerGroup_zero_eq_top_of_fixed` then makes the zeroth lower
group the whole group. The published equality between that group and the
actual residue-action kernel gives
`inertia_eq_top_of_canonical_totalRamification`.

This is an internal derived argument using the published canonical residue
arithmetic, not an additional arithmetic hypothesis. The fixed-representative
and cancellation arguments adapt Worker 231's
`Langlands.Galois.Local.TotallyRamifiedSolvabilityProof`, previously specialized
to a finite intermediate extension. Worker 96 generalizes them to the supplied
algebra between independent arbitrary `PadicField` carriers.

## Positive ramification groups and powers

`pow_smul_sub_nsmul_mem` says that for an element of `G_i`, with `i ≥ 1`,
the displacement of a point after the `n`th iterate is congruent modulo
`m^(i+2)` to `n` times its first displacement. Induction uses the published
ideal-power displacement bound on `m^(i+1)`. Consequently, when the integer
`n` lies in the maximal ideal, the `n`th power of the group element belongs
to `G_(i+1)`. This proves `pow_mem_lowerGroup_succ_of_natCast_mem` without
assuming that `n` is prime.

If `n` is coprime to the group cardinality, Mathlib's `powCoprime` makes
raising to the `n`th power surjective. Thus, if `G_1` were the whole group,
every positive lower group would be the whole group by induction. This
contradicts termination for a nontrivial group. This is
`lowerGroup_one_ne_top_of_coprime`.

In the other direction, suppose the group has exponent `p`, the residue
field has characteristic `p`, the maximal ideal has a nonzero generator,
and residue classes have fixed representatives. The published
`uniformizerCharacter` has `p`th power equal to one on every element of `G_0`.
In characteristic `p`, subtracting one and taking the `p`th power gives zero;
the residue field has no nonzero nilpotents, so the character equals one.
The published uniformizer-kernel bound and
`mem_lowerGroup_one_of_fixed` then give `G_1 = top`. This proves
`lowerGroup_one_eq_top_of_exponent_char`.

## The actual prime-degree criterion

`lowerRamificationGroup_one_eq_top_iff_prime_degree` installs the actual
integer-ring action, the canonical discrete valuation ring and canonical
residue characteristic. The Galois cardinality theorem identifies the group
cardinality with the supplied relative degree, which is prime and greater
than one. If that prime differs from `p`, it is coprime to `p`; the preceding
termination argument rules out `G_1 = top`. If the degree equals `p`,
Lagrange's theorem gives exponent `p`, and the fixed representatives obtained
from canonical total ramification give `G_1 = top` by the uniformizer argument.

This implemented proof avoids constructing the tame quotient or the full
wild p-group classification. It uses no norm theorem or reciprocity theorem.
The support imports neither the parent break statement nor its proof. Its
total-inertia bridge can therefore be reused without a circular import.

The mathematical target is the criterion in Serre, *Local Fields* (1979),
Chapter V §3, printed page 83 (PDF page 90), with the usual tame and wild group
facts in Chapter IV §2, Proposition 7 and Corollaries 1 and 3, printed pages
67–68. The parent proof Markdown records the registered source and errata. This
proof Markdown describes the implemented argument, which differs from the
source's route through graded embeddings.

Authors: Worker 96. Worker 231 contributed the adapted published residue proof
and suggested the characteristic-`p` uniformizer argument and a power-lowering
route. Worker 96 implemented the iterated-displacement and coprime-power proofs
and their actual p-adic specialization.
