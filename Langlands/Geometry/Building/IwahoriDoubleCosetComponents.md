# Component representatives for actual Iwahori double cosets

This internal adapter applies the component Bruhat construction to the existing
`ParahoricBuildingData G`. It uses the actual normalizer, centralizer-zero
subgroup, full parahorics, Iwahori–Weyl quotient and component map. It does not
prove either global double-coset statement.

The field and group data have the same arbitrary universe parameter as the
published building definitions. Assume that `P.normalizerZero` is normal. For
every subset `Ω` of the apartment and every actual normalizer element `n`,
conjugation sends `P.parahoric Ω` onto `P.parahoric (n • Ω)`.
Indeed, the parahoric is the join of the image of the centralizer-zero subgroup
and the sharp fixer. Normality of `P.normalizerZero` keeps the first subgroup
invariant under conjugation by `n`; `mem_normalizerZero_iff` identifies its
image in the rational-point group. The published `sharpFixer_le_comap`
gives covariance of the second subgroup. This proves one containment, and
applying it to `n⁻¹` proves equality. Consequently every element of
`P.normalizerStabilizer Ω` normalizes the full `P.parahoric Ω`.
This argument works for arbitrary subsets; it needs no chamber hypothesis.

Assume also that `P.zeroSubgroup` is normal, and that the restriction of
`P.toComponents` to `P.chamberStabilizer C` is surjective. For every component
`γ`, `exists_normalizing_component_rep` chooses a chamber-stabilizer element
over `γ`, unpacks its image membership to an actual normalizer element fixing
`C`, and uses `toComponents_mk` to identify its component. The preceding
covariance theorem proves that this representative normalizes the full
`P.parahoric C`. For every rational point `g`, the companion
`exists_normalizing_zeroSubgroup_rep` chooses such a representative `n` of
the component of `g`. The quotient criterion for membership in
`P.zeroSubgroup` gives `g * n⁻¹ ∈ P.zeroSubgroup`. This is also the
representative hypothesis used by the parabolic component helper.

`iwahoriDoubleCosetEquivOfKernelTits` specializes
`Langlands.Group.TitsSystem.componentDoubleCosetEquiv` to the actual quotient
maps. It additionally assumes that the full `P.parahoric C` lies in the kernel
of `G(F) → G(F)/G(F)^0`, and that the actual normalizer and Iwahori restrictions
form a Tits system in that kernel, with Weyl group the kernel of
`P.toComponents`. These are explicit intermediate proof inputs. The quotient
map from the full normalizer is surjective, and `toComponents_mk` supplies
compatibility of the two quotient maps. The normalizing representatives above
therefore give an actual equivalence

`P.IwahoriWeylGroup ≃ P_C \ G(F) / P_C`.

Its application theorem gives the prescribed value on every actual normalizer
representative. The final lemma packages that equivalence and formula as the
existing fixed-data proposition `P.IwahoriDoubleCosetBijection C`. The
equivalence retains all components of both ambient groups.

The provenance is derived: the covariance argument follows directly from the
published parahoric definition, normalizer-zero membership criterion and sharp
fixer covariance. Its intended geometric context is Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Definition 7.4.1, Theorem 7.5.3,
Theorem 7.8.1(2) and §7.8.2 (PDF pages 286, 291–292 and 303–304), together
with the authors’ corrections of 1 November 2024, PDF page 35. The imported
component Bruhat construction implements the corrected injection argument:
compare components, remove a common representative normalizing the Iwahori,
and apply Bruhat uniqueness in the component kernel.

Neither normality, component surjectivity, actual Iwahori containment nor the
actual Tits-system realization is proved here. They must all be derived from
the unchanged apartment hypotheses before this adapter can close
`IwahoriDoubleCosetStatement`. The actual facet comparisons required by
`ParahoricDoubleCosetStatement` remain separate obligations. No hypotheses
of either published global target are changed.
