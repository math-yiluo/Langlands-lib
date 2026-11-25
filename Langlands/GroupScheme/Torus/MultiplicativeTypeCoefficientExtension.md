# Conditional assembly of fpqc descent and multiplicative-type extensions

`Langlands.GroupScheme.ExtensionReduction.extensionDiagonalizingCover`
constructs an actual fppf covering family and a proof that each pullback of
the extension group is diagonalizable. Its group and base hypotheses are
exactly those of the extension clause in the unchanged
`MultiplicativeTypeFpqcExtensionStatement`: arbitrary base, three affine flat
locally finitely presented groups, a monomorphic kernel representative, the
actual fppf quotient, relative multiplicative-type endpoints, and connected
or commutative middle residue fibres pointwise. The construction additionally
takes these three exact published statement types as explicit proof premises:

- `MultiplicativeTypeFibralCriterionStatement`;
- `MultiplicativeTypeCompleteLocalDeformationStatement`;
- `MultiplicativeTypeFieldExtensionStatement`.

They are not proved here and no proof of them is imported. The
local character-classification premise appearing in intermediate theorems
is discharged by the published `CompleteLocalDeformation.restrictMap_bijective`
from `LocalDiagonalizableHom`.

`idealResidue_fieldMultiplicativeType` compares the scheme residue fibre with
the canonical ideal-residue-field pullback using the actual residue-field
isomorphism and compatible scalar maps. `modelResidue_fieldMultiplicativeType`
uses a coefficient recovery isomorphism to identify the original residue
fibre with a field extension of the model residue fibre, then applies
field-extension reflection. Thus field-level multiplicative type transfers
to model points in the image of the original base; no condition on every
point of the coefficient spectrum is silently assumed.

`ringExtension_of_fieldResidues` models the exact split-endpoint quotient over
a finitely generated subalgebra of a same-universe copy of the integers.
Its noetherian model has diagonalizable actual kernel and quotient and
recovers the source by an actual group isomorphism. At every original prime,
the preceding residue comparison gives a multiplicative-type model fibre.
The noetherian point-neighbourhood theorem yields an affine fppf diagonalizing
neighbourhood there. Pull it back to the original base. The pullback range
formula retains the original prime in its image, and the recovery isomorphism
and actual pullback comparisons diagonalize the original group on this
neighbourhood. Taking one such neighbourhood per prime forms the fppf cover.

`affineSplit_of_fibral_deformation_field` uses the supplied field theorem to
obtain the needed middle residue properties from the exact extension and
its pointwise alternative. An affine scheme is handled through its spectrum
isomorphism. The common affine endpoint-splitting cover and fppf locality
then give the arbitrary-base extension clause.

`fpqcExtension_of_fibral_deformation_field` returns the full original target
with the three statement premises and local character premise explicit.
`fpqcExtension_of_threeStatements` supplies the published character
classification, leaving exactly the three statement premises. The definition
`extensionDiagonalizingCover` chooses the actual fppf cover from the resulting
extension clause; its `PLift` component carries the diagonalizability proofs.

The proof route is internal: exact finite coefficient models, finite Galois
residue splitting realized at an etale point, ordinary localization and
completion, and spreading an actual fppf diagonalizing piece. It uses no
strict-henselization existence premise. This is a conditional construction
and a reduction of `MultiplicativeTypeFpqcExtensionStatement` to the three
exact statements above. It is not an unconditional proof of that statement.
