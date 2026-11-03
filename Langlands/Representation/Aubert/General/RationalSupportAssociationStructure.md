# Structural laws for support association

Author: Worker 12.

This internal module develops the actual normalizer and nested-subset laws
needed to transport the support-category witnesses. Inverse and product
representatives act by the inverse and composite character automorphisms.
The published `rootAssociationEquiv` carries each literal simple-root label
to its actual Weyl image. Pulling a finite subset back along that equivalence
preserves properness and gives association of the corresponding nested faces.
These are deductions from the definitions, rather than additional source inputs.

All declarations lie in
`Langlands.Aubert.General.RationalPointFamily`. Their setting is a field,
the actual group schemes and torus embedding with its displayed affine and
monomorphism instances, and actual rational points. This module does not
assume a topology on rational points.

| Declaration | Implemented content |
| --- | --- |
| `rootAssociation_inv` | If `n` associates `I` to `J`, its actual inverse associates `J` to `I`. Normalizer membership is closed under inverse; the quotient character action is inverted. |
| `rootAssociation_mul` | If `n` associates `I` to `J` and `m` associates `J` to `K`, `m * n` associates `I` to `K`. The order agrees with the composite character action. |
| `rootAssociation_character_image_of_mem` | Converts the point-quotient character action in `rootAssociation` to the scheme-normalizer action using the published `weylCharacterAction_point_mk`. |
| `rootAssociationEquiv_character` | Computes the character underlying the image of a literal label under the published `rootAssociationEquiv`. |
| `rootSet_leviIndex_eq`, `rootSet_leviIndex_subset` | Identify the root set of a nested finite subset with the image of its labels, and prove inclusion in the outer root set. These need neither the normalizer comparison nor the embedding monomorphism. |
| `exists_associated_nested_subset` | Pulls a proper finite subset `K′` of `J` back along `rootAssociationEquiv`. Injectivity of finite-set mapping proves the preimage proper; the character computation proves the association of nested faces with the same `n`. |
| `rootAssociation_levi_membership` | Under connected reductivity, a maximal split torus, a generic cocharacter and `hStandard`, deduces `x ∈ M_J ↔ n⁻¹ x n ∈ M_I` from the actual root association. |
| `rootAssociation_nested_unipotent_membership` | Under the same structural hypotheses and explicit finiteness of simple roots, proves the corresponding radical-membership equivalence for associated nested faces, for `x ∈ M_J`. |

For Levi transport, the exact published
`Langlands.GroupScheme.standardLeviConjugationStatement_of_standardCocharacterStatement`
discharges the Levi-conjugation statement from `hStandard`.
`levi_map_conj_of_character_image` and
`conjugationMembership_of_map_eq` then give the displayed actual membership
equivalence. Thus no new structural statement is assumed.

For radical transport, use
`Langlands.GroupScheme.mem_standardUnipotent_conj_of_mem_standardLevi`
from [NestedStandardTransport](../../../GroupScheme/Rational/NestedStandardTransport.md)
on `n⁻¹ * x * n`. Its inner conjugate is `x`, so the outer-Levi hypothesis
is exactly the supplied membership of `x`. The root-set inclusion lemmas
provide the nested-face hypotheses, and `rootAssociation_character_image_of_mem`
provides both character-image equalities. The all-test-scheme equivalence
then specializes to rational points.

These laws are implementation prerequisites for the transport proof in
[RationalSupportAssociationInvariance](RationalSupportAssociationInvariance.md).
They add no support theorem, finite-length condition or representation
theoretic input. Empty finite root subsets are allowed.

The inverse and product laws are imported unchanged from
`RootAssociationComposition`, authored by Worker 78. The character-image
wrapper with an explicit normalizer-membership proof reuses
`rootAssociation_character_image` from `RationalRootAssociationLeviTransport`.
