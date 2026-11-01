# Right-corner actions and actual full-dual fixed-part comparison maps

This construction supplies the right corner actions and full-dual
comparison maps for Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, I.4.1, printed pp.22–23 /
PDF pp.28–29, especially the fixed-part identification in the lemma and
its proof on printed p.23 / PDF p.29. The governing registered
source is `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original nonunital-action conventions are on printed pp.5–7 /
PDF pp.11–13; the canonical complex scalar construction is I.2.1,
printed p.14 / PDF p.20, formula (I.2.1.1); the fixed-part splitting is
I.3.1, printed p.19 / PDF p.25, formula (I.3.1.1).
The registered supplementary `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp.1–2, has nearby corrections to tensor injectivity, later forgetful
comparison and admissible reflexivity. They do not alter these maps. No
project source-specific errata file was found in the inspected Library.
The 2026 edition governs.

The source identifies the ordinary dual of eM with the e-fixed part of
the full dual and with the e-fixed part of the nondegenerate dual. This
pair supplies the right corner actions and identity-on-functionals maps
needed to state those comparisons precisely. The named modules, corner
opposite equivalence, scalar adapters and whole-map identifications are
derived internal construction details of that argument.

`cornerOp` and `cornerUnop` use the original corner support equations.
`cornerOppositeEquiv` identifies `(Corner e)` opposite with
`Corner (oppositeIdempotent e)` as actual rings; reversed multiplication
and the additive operations agree on underlying elements. Both value
formulas expose the original `op` and `unop` functions.

`FullRightFixedPart` is the actual published fixed-part subtype of
`NonUnitalModuleDual.FullDual hA hM`, for the specified `fullAction`.
`fullRightFixedPart_eq_subtype` exposes its entire fixation condition.
`fullRightFixedModule` inherits the full dual's pointwise complex
scalars. Its whole-functional scalar formula and commutation with the
unchanged corner action are explicit. The latter proof uses subtype
extensionality and pointwise commutation in the full dual.

`fixedPartDualCornerModule` equips the actual ordinary complex dual of
the original fixed part with its right corner action. It precomposes
with `NonUnitalModuleCorner.cornerLinearAction hA hM e (cornerUnop e a)`.
Its module laws use the existing complex-linear action, reversed
products, and the corner unit. The whole-functional and application
formulas expose that action; complex scalar commutation holds
pointwise. It uses the exact named complex module recovered on eM.

`toFullFixed` forgets the inner nondegenerate-membership proof and keeps
the entire included functional. `fromFullFixed` uses the same opposite
idempotent as a witness of nondegeneracy via the published `ofFixedFull`.
Both are complex linear with the two precise inherited modules explicit.
Their whole-function and entire included-functional formulas are
provided. `toFullFixedCorner` and `fromFullFixedCorner` are corner-linear
forms of exactly those maps. Equality of their entire underlying
additive maps identifies the two scalar interfaces. Their linearity
proofs use subtype extensionality and inherited pointwise operations.
No inverse identities or equivalence for these maps are proved here.

`restrictionCorner` and `extensionCorner` equip the two published
complex-linear restriction and extension maps with corner-linear forms.
Their entire additive maps equal those of the published maps, and their
whole-functional formulas are precisely composition with the actual
linear inclusion and projection. Restriction compatibility is
definitional. Extension compatibility uses both support equations of
the original corner element and associativity of the original action;
explicit ambient complex modules make the functional extensionality
unambiguous. No inverse or naturality theorem for these two maps is
proved here.

Complete unapplied interface examples check that the algebra and carrier
universes are independent for the corner opposite equivalence, actual
full fixed part and its complex module, ordinary dual corner module,
both complex and corner-linear comparison directions, and corner-linear
restriction and extension. There is no original
complex Module hypothesis on M: its module is recovered from the
specified original action. There are no dimension, nontriviality,
global-unit or anti-involution assumptions. The zero idempotent and zero
algebra/module remain allowed.

These are the comparison maps and their intrinsic linearity proofs.
Full-fixed inverse identities, equivalences, compatibility of those
equivalences with the right corner and full-dual inclusion, and
whole-map naturality remain separate statement and proof obligations.
The existing basic fixed-part inverse/equivalence/naturality chain,
duality exactness, bidual injection, and later I.4.2/I.4.3 and
admissibility results are outside this construction.
