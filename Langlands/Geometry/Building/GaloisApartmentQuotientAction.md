# Actual coefficient action on the same root-valuation quotient

Let `k` and `K` be fields in an arbitrary common universe, with a supplied
`k`-algebra structure on `K`. Supply a commutative group scheme `T`, a group
scheme `G` over `k`, and a map `i : T.toGrp ⟶ G`. Write `T_K`, `G_K` and `i_K`
for their actual base changes. Assume the underlying scheme map of `i_K` is a
monomorphism. The first two results concern arbitrary root-function families
and need no affine or valuation hypothesis.

`galoisCharacter_weylAction` moves inverse character coefficient transport
across the existing Weyl action of the actual conjugated normalizer point. It
applies the full-character covariance from `NormalizerGaloisAction` to the
inverse-transformed character, then cancels the coefficient representations.
`RootFunctionFamily.galoisAction_smul` consequently intertwines the existing
normalizer action on families with the actual coefficient action. Its
pointwise proof uses that character identity for the inverse normalizer point.
Multiplication and inversion preservation by the existing rational coefficient
automorphism identify the remaining conjugated point arguments. All character
and point transports are the existing ones.

For the apartment and quotient constructions, also assume that the structure
morphism of `G` is affine. The required affine instance upstairs is its
pullback. Supply `omega : Kˣ → ℝ`, actual `D : KPApartmentData i_K omega`, and
`hD : D.GaloisStable`. Thus a full normalizer-stable class of valuations and its
stability under actual coefficient transport are supplied. Existence of such
canonical data and their coefficient stability are not proved here. No
splitness, reductivity, smoothness, finiteness or Galois-extension assumption
is used in these algebraic deductions.

`galoisAction_normalizer_smul` restricts the family equivariance to the same
`D.Apartment` by apartment extensionality. Its coefficient-transformed
normalizer point is exactly `normalizerGaloisAction sigma n`, whose carrier is
the existing `rationalConjugate sigma n`. This proves the normalizer
compatibility required for passage to the quotient; it is not a new input.

`rationalConjugate_mem_sharpFixer` proves preservation of the existing sharp
fixer at each apartment point. That subgroup is the supremum of the actual
root fixers. A singleton root fixer is the existing zero-depth filtration.
The actual root permutation `galoisRootAction` and the all-depth filtration
equivalence from `ApartmentGaloisAction` therefore send each generator into
the sharp fixer at the transformed point. The subgroup supremum property
extends this to every member, without a separate sharp-fixer premise.

`galoisQuotientActionData` now fills all four fields of the existing generic
`ApartmentQuotient.SemilinearActionData`. It uses the restricted actual
apartment action, actual normalizer preservation, the normalizer equivariance
just proved and sharp-fixer preservation. Its ambient automorphism
homomorphism is the existing generic `rationalConjugateAction` from
`UnramifiedBuildingSemilinearAction`; that definition is over arbitrary field
extensions, so this import imposes no local-field hypothesis on this unit.

`galoisQuotientAction` applies the generic quotient construction to these data.
The carrier is exactly the existing `D.ReducedBuilding`, the quotient of actual
rational points times the existing apartment by the original normalizer and
sharp-fixer relation. On a representative `(g, x)` it sends both coordinates by
the existing coefficient maps. The generic construction proves that this map
respects the relation, has the inverse coefficient map as inverse, and obeys
the identity and composition laws. The resulting homomorphism is to
permutations of this same quotient.

`galoisQuotientAction_apartmentMap` identifies the action on the existing
apartment map. `galoisQuotientAction_smul` proves semilinearity for the original
rational-point action on the quotient. Finally,
`galoisQuotientAction_smul_eq_iff` reflects and preserves full point fixation
under simultaneous transport of the original rational point and quotient
point. These assertions use the generic construction's proved formulas; no
replacement rational-point action or unrelated quotient is introduced.

This is an internal derivation from the imported actual coefficient actions,
full valuation-class structure, root filtrations, sharp fixers and generic
quotient transport. It adds no external literature assertion. It removes
normalizer and sharp-fixer compatibility as separate inputs once the given
class is coefficient-stable. Canonical class existence and stability, a
complete NPC metric, isometry and orbit continuity, a special point, the
original supplied-model stabilizer identity and unique fixation, and descent
to the base-field comparison remain separate obligations. The unconditional
`BuildingComparisonStatement` remains open.
