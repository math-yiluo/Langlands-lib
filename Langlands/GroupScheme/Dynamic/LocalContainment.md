# Persistence of dynamic containment near a residue fibre

This internal module derives a neighbourhood construction from dynamic
representability and smoothness and the smooth-monomorphism local
isomorphism theorem. It supplies one step of the relative parabolic
Lie-containment argument, rather than the complete target.

Let `H` be smooth and affine over an arbitrary scheme `S`, with geometrically
connected fibres, and let `χ : Gm → H` be a cocharacter. If its dynamic
parabolic is the whole group on the actual residue fibre at `s`,
`exists_parabolic_eq_top_near` proves that the same holds on an open
neighbourhood of `s`.

The proof represents `P_H(χ)` by a closed monomorphism `κ : K → H`.
Dynamic smoothness makes `K` smooth. Compatibility with base change and the
assumed equality give full functorial range to `κ_s`, so evaluating its range
on the identity of the target gives a section. Monicity makes this fibre map
an isomorphism. `SmoothMonoLocalIso.isIsoNear_of_residueFiber` then gives an
open neighbourhood on which the underlying scheme map of `κ` is an
isomorphism. The forgetful functor reflects this isomorphism to the over
category. Every test point of `H` on that open lifts through the inverse of
`κ`, proving the full dynamic-parabolic equality.

For any group homomorphism `i : H → G`,
`exists_range_le_parabolic_near_of_top` maps that equality into
`P_G(χ ≫ i)` by dynamic functoriality. The ambient group has no additional
geometric assumptions in this implication.

`exists_range_le_parabolic_near_of_residueFiber` replaces the full-parabolic
fibre premise by containment of the actual range of `i_s` in
`P_G((χ ≫ i)_s)`, assuming `i_s` is a closed subgroup inclusion.
Closed-subgroup compatibility identifies `P_H(χ_s)` with the inverse image
of that ambient parabolic. The assumed containment makes this inverse image
the whole group, and the first result applies. Global closedness of `i` is
not a hypothesis.

`parabolicContainmentNeighbourhood` selects an actual open with the proved
point-membership and all-test containment properties. All schemes use one
arbitrary universe, and the base need not be affine, Noetherian, reduced or
connected. The source group's smoothness, affineness and geometrically
connected fibres, the supplied source cocharacter, and fibre closedness in
the last result are essential stated inputs.
