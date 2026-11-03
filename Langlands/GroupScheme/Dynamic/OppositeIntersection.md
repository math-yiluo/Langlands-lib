# Opposite dynamic intersections for affine group schemes

This internal unit constructs `Dynamic.oppositeCocharacter χ` by composing `χ`
with inversion of the Gm parameter. It proves
`Dynamic.opposite_unipotent_inf_parabolic χ`:

`Dynamic.unipotent (Dynamic.oppositeCocharacter χ) ⊓ Dynamic.parabolic χ = ⊥`.

The base is `Spec R` for any commutative ring `R`. The group scheme has affine
underlying scheme. The equality is of the actual subgroup functors, so it holds
on every test scheme, including nonreduced and nonaffine tests. No smoothness,
connectedness, reductivity, characteristic or field hypothesis is required.

On an affine test `Spec A`, choose an orbit extension `ep` for the original
cocharacter and an identity-valued extension `en` for its opposite. The published
polynomial and Laurent test-scheme charts convert their restrictions to ring
maps into `A[t]` and `A[t,t⁻¹]`. The constructed `AffineLine.laurentInvert` inverts
the Laurent parameter. Its composite with the universal Laurent point is the
same as inverting the Gm parameter. Consequently the Laurent expansion of
each coordinate of `en` is the inverse-variable expansion of the corresponding
coordinate of `ep`.

Both coordinate expressions are polynomials. At every positive exponent, the
coefficient of the inverse-variable expansion vanishes. Thus each coordinate of
`en` is constant, as proved in
`AffineLine.polynomial_eq_C_eval_zero_of_invert`. Its value at zero is the
identity by the unipotent premise, so the entire extension is the identity.
Restrict to Gm and evaluate its orbit at the unit parameter to conclude that
the original point is the identity.

For an arbitrary test scheme, restrict the two subgroup memberships to its
canonical affine open cover. The affine result identifies each restriction
with the identity, and the cover's morphism-extensionality theorem identifies
the original point with the identity. This yields the claimed all-test
intersection equality.

The provenance is internal coordinate algebra for the published dynamic
subgroups and affine test charts. No opposite open-cell or multiplication
injectivity theorem is assumed. These stronger geometric statements are not
claimed by this module; consumers may derive multiplication injectivity from
the proved subgroup intersection by group algebra.
