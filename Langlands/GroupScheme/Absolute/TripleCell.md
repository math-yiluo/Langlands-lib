# The three-factor open cell of a smooth affine group

This is a derived construction from the published
`Absolute.OppositeCellProof`, the dynamic affine representability construction,
and the scheme product decomposition in `Dynamic.ParabolicProduct`.
The multiplication morphism is defined directly in the category of schemes
over the base; `lift_tripleCellMultiplication` records its value on every
test scheme.

For any smooth affine group scheme `G` over any field `k` and cocharacter `χ`,
`isOpenImmersion_tripleCellMultiplication` proves that the actual multiplication
morphism

`U(-χ) ×_k (Z(χ) ×_k U(χ)) → G`

is an open immersion. Here `-χ` denotes precomposition with inversion on `Gm`.
The three sources can be any group schemes representing the intrinsic dynamic
functors, with their represented inclusions in `G`. The theorem has no
perfectness, characteristic, connectedness, reductivity, or splitting
restriction.

The implementation obtains an actual representative of `P(χ)` from the
existing affine representability construction. It uses `parabolicProductIso`
to replace `Z(χ) × U(χ)` by `P(χ)`. The resulting isomorphism on the source,
followed by the published opposite-cell open immersion
`U(-χ) × P(χ) → G`, is precisely the displayed multiplication. Open immersions
are preserved by this composition.

For use with a specified maximal torus `T`, one must separately prove that its
inclusion represents `centralizer χ`. Substituting that representation in this
theorem gives `U(-χ) × T × U(χ) → G`. This construction does not establish
that centralizer identification or the split common-torus isomorphism theorem.
