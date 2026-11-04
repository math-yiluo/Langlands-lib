# Actual lattice comparison from restriction evaluation

Author: Worker 1292. The imported SplitComponentLatticeBridge is by Worker 1503.

This module proves finite index of the actual split valuation image and
bijectivity of the actual uniformizer section onto that image, using splitness
of `S` and the host's existing bijectivity hypothesis for
`restrictionEvaluation s`. It is a derived integral comparison. It assumes
neither connected reductivity of `Z` nor the split-component property of `s`.

## Setting and provenance

The field `F : Type u` has the existing nonarchimedean local-field instances,
with no characteristic or residue-characteristic restriction. The commutative
group scheme `S`, group scheme `Z`, and morphism `s : S.toGrp ⟶ Z` are actual
objects over `Spec F`. The parameter `h` is a bijectivity proof for the published
real restriction-evaluation map. Splitness of `S` is a further explicit
hypothesis of the finite-index and section theorems.

All new content is internal and derived from the published actual maps and
integral linear algebra. The imported `RenardIntegralRestriction` gives descent
of functionals and a finite-index criterion. The imported
`RenardDominantValuation` gives positive uniformizer normalization and
invariance under equality of integer character valuations. The imported
`SplitComponentLatticeBridge`, by Worker 1503, supplies uniformizer evaluation
and realization of a split-torus point's valuation by a uniformizer point.
Its additional conditional split-component theorems are not used here.

## The restricted integral pairing

The actual image A of restriction is a sublattice of the character lattice B
of S. Pairing cocharacters C with A defines a map P to its integral dual.
Injectivity of the real comparison makes P injective: after embedding C into
its real scalar extension, every restricted character has equal evaluation,
so the real comparison identifies the vectors. The integral perfect pairing
of a split torus proves that scalar extension was injective. Split coordinates
give C and B equal rank, so the integral helper proves P has finite cokernel.

In Lean, `integralCharacterRestriction` is `characterRestriction s` viewed as
an integer linear map. `restrictedIntegralPairing` restricts the flipped
perfect lattice pairing to its range. Its evaluation lemma computes
`P(c)(r(χ)) = latticePairing S (characterRestriction s χ) c`.
`cocharacter_tmul_injective` uses
`CocharacterUniformizer.latticePairing_isPerfPair` to show that equality of
`1 ⊗ c` and `1 ⊗ d` implies equality of `c` and `d`: applying each character
evaluation gives equal integer pairings after injective casting to the reals.
`restrictedIntegralPairing_injective` then applies `h.injective` to these
pure tensors.

For `restrictedIntegralPairing_finiteIndex`, a splitting of `S` identifies both
character and cocharacter lattices with `I → ℤ` for the same finite `I`.
The resulting equivalence `C ≃ₗ[ℤ] B` and finite free instances for `B`
give exactly the hypotheses of
`IntegralRestriction.finiteIndex_range_of_injective`, applied to `A = r.range`.
This also covers rank zero.

## Descent of the actual valuation

The character normalization of centralizerValuation forces every actual integer
valuation to vanish on the restriction kernel. The integral descent helper
therefore defines its functional on A, with the stated evaluation formula.

More precisely,
`rationalCharacterValuation_eq_zero_of_restriction_eq_zero` applies
`centralizerValuation_spec s h z χ` to a character with `r(χ) = 0`. Its real
evaluation is zero, so injectivity of the integer cast gives zero integer
valuation. `descendedActualValuation s h y` applies
`IntegralRestriction.descend` to the integer functional underlying the actual
value `y`. The range membership of `y` supplies a rational point for the
kernel-vanishing argument. Its evaluation at `r(χ)` is `y(χ)`.

`actualValuationOnRestriction` packages this descent as a group homomorphism
from `rationalCharacterValuationImage Z` to the multiplicative synonym of
`Dual ℤ A`. The identity and product laws follow by evaluation on every
`r(χ)`, since these exhaust `A`. The same evaluation formula proves
`actualValuationOnRestriction_injective`: equal descended functionals give
equal values on every rational character and hence equal actual valuations.

The uniformizer identity
`actualValuationOnRestriction_uniformizer` identifies the image of
`H_Z(s(c(ϖ)))` with `P(c)`. On `r(χ)` this is exactly Worker 1503's
`rationalCharacterValuation_map_uniformizerSection`.

## Finite index and the section

`splitValuationImage_eq_comap` identifies the actual split valuation image
with the inverse image of `P.range` under `actualValuationOnRestriction`.
For the forward inclusion, a split-torus point has the same ambient valuation
as a uniformizer point, by
`exists_rationalCharacterValuation_map_eq`. The uniformizer identity puts its
descended value in `P.range`. Conversely, a descended value in `P.range`
agrees with that of the corresponding uniformizer point; injectivity of
`actualValuationOnRestriction` identifies their actual valuations.

`finiteIndex_splitValuationImage_of_comparison` now pulls finite index of
`P.range` back along this homomorphism. This uses the usual finite-index
instance for the inverse image of a finite-index subgroup.

`bijOn_C0_splitValuationImage_of_comparison` proves all three parts of the
valuation bijection. Every uniformizer point maps into the split image.
For injectivity, equality of integer valuations gives equality of real
centralizer valuations, whose positive normalizations are `1 ⊗ c` and
`1 ⊗ d`; the split-torus embedding gives `c = d`, hence equality of the
actual points in `C0`. Surjectivity uses
`exists_rationalCharacterValuation_map_eq` again.

These conclusions use the host's already quantified comparison proof `h`.
They do not establish existence or bijectivity of a real comparison for an
arbitrary morphism. The module supplies the two remaining lattice inputs
for the conditional dominant assembly, but contains no proof of the closed
`RenardDominantComparisonStatement` itself.

The local instances have explicit module-specific names to avoid generated-name
collisions when these developments are imported together. Their types, bodies
and local scope are unchanged.
