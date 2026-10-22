# Conditional orthogonal compact-isotypic projector families

This internal construction extends `ConditionalProjection` using the existing
intrinsic isotypic and annihilator subrepresentations. Complementarity is an
explicit input to the family. This module does not establish unconditional
projector existence, compactness of its range, finite support of the total
family, or the product-Levi decomposition.

## Separation of distinct classes

`intertwiningMap_eq_zero_of_ne` takes two actual irreducible compact-coefficient
representatives whose classes differ. Mathlib's
`Representation.IsIrreducible.bijective_or_eq_zero` makes any intertwiner either
bijective or zero. A bijective intertwiner induces a representation equivalence,
a smooth isomorphism, and then an isomorphism in the full subcategory of compact
irreducibles. This contradicts the class inequality. No finite-dimensional
version of Schur's lemma is used.

`isotypicSubrepresentation_le_annihilator_of_ne` proves that, for distinct
classes `c` and `d`, the intrinsic `c`-isotypic subrepresentation of any smooth
object `A` lies in the intrinsic `d`-annihilator. For each incoming intertwiner
`f : D → A` and outgoing intertwiner `g : A → E` representing these classes,
the preceding lemma kills `g.comp f`. Thus the range of every incoming map
lies in every outgoing kernel. The published supremum/infimum universal
properties give the required inclusion.

`comp_eq_zero_of_isotypic_range_annihilator_ker` applies this inclusion to actual
endomorphisms `P` and `Q`. If the range of `P` lies in the `c`-isotypic part and
the `d`-annihilator lies in the kernel of `Q`, then `Q.comp P = 0`. These
containments suffice; idempotence and equality of the ranges or kernels are
unnecessary for this particular implication.

## Fixed-vector vanishing

`fixedVectors_le_annihilator_of_not_hasFixedVector` works for every subgroup
`K`, without compactness or openness. If `c` has no nonzero `K`-fixed vector,
each actual representative of `c` has zero fixed submodule. Every outgoing
intertwiner sends a fixed vector of `A` into this zero submodule, by
`fixedVectorsMap`. The intrinsic annihilator membership formula then places
every fixed vector of `A` in the annihilator.

`apply_eq_zero_of_annihilator_le_ker` concludes that any actual endomorphism
whose kernel contains this annihilator vanishes on all these fixed vectors.
This deduction also requires no idempotence.

## Constructed family and scope

`isotypicProjectorFamilyOfIsCompl h` is the actual family of equivariant
endomorphisms obtained by applying the published `isotypicProjectorOfIsCompl`
to `h c A`. Here `h` supplies complementarity of the intrinsic pair for **every**
class `c` and smooth object `A` at the fixed universes. The family is pairwise
orthogonal, with the order of composition explicitly `P_d.comp P_c` for
`c ≠ d`, and it vanishes on fixed vectors for classes without fixed vectors.
The two family laws apply the preceding lemmas and the published exact
range/kernel formulas.

The group universe `uG`, representative carrier universe `uV`, and ambient
carrier universe `uW` are independent. Only a group and a topology on it are
required beyond the existing smooth-object definitions. The representatives
are irreducible and have compact smooth-dual coefficients by their existing
bundled type; the proof of separation uses their irreducibility. Ambient
objects remain arbitrary smooth representations.

All proofs are internal deductions from the published definitions and pinned
Mathlib algebra. No original-literature existence theorem is newly asserted.
