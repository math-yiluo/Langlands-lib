# Largest central subtori under arbitrary field extension

Authors: Worker 1578 and Worker 1467.

`reductiveLargestCentralSubtorusBaseChange` proves exactly
`ReductiveLargestCentralSubtorusBaseChangeStatement.{u}`. For every field
extension `K/k` in universe `u`, the base change of any largest central
subtorus of a connected reductive group is again its largest central
subtorus. The statement includes greatestness against all closed central
`K`-tori, whether or not they descend to `k`. There are no additional
premises on the extension.

The implemented proof uses only the smoothness, affineness and connectedness
parts of connected reductivity. The published normal-subgroup quotient
theorem supplies a smooth affine fppf quotient `q : G → Q` whose full kernel
is the given largest central torus `Z`. The full scheme-theoretic center
`C → Q` exists as a closed subgroup because `Q` is affine. Its source is
commutative, affine and locally of finite type; it need not be smooth.

The helper `IsLargestCentralSubtorus.quotient_center_torus_hom_eq_zero`
shows that every `k`-torus homomorphism into `C` is zero. Its schematic
image is a closed torus in `C`. Viewed in `Q`, that torus is central. Its
inverse image in `G` is a central extension of tori, hence a torus; it is
normal, so splitting and connectedness make it central. Greatestness of
`Z` places this inverse image in the kernel of `q`, forcing the original
torus in `Q` to vanish.

The helper `CocharacterDatum.torus_hom_eq_zero_of_no_torus` carries this
vanishing to every extension `K/k`. It combines geometric cocharacter
vanishing with the published specialization theorem over algebraically
closed fields, comparison of the two iterated field pullbacks, splitting
of a source torus, and faithful field pullback. Its target hypotheses are
precisely affineness, local finite type and commutativity, so they apply
to the full center `C`, including any nilpotents.

Finally, `IsLargestCentralSubtorus.baseChange_of_quotient_center` proves
the desired greatestness. A central torus in `G_K` has central image in
`Q_K`, since `q_K` is flat and surjective. This image factors through the
full center `C_K` and therefore vanishes. The exact fppf kernel identity
places its subgroup-functor range in the range of `Z_K` on every test
scheme. Existing base-change results supply the other three parts:
torus structure, closedness and centrality.

This is a derived proof of the published target, whose original-source
provenance is recorded in
`Rational/LargestCentralSubtorusBaseChangeStatement.md` (Milne,
*Algebraic Groups*, Corollary 17.62). The route uses the actual proved
Library quotient, central extension, torus-image, center and cocharacter
theorems rather than a multiplicative-type structure premise. The three
paired helper modules document their internal arguments and imported
prerequisites.
