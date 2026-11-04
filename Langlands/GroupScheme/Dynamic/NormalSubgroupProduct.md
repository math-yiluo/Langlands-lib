# Smooth surjectivity of normal-subgroup multiplication

All declarations are internal constructions and deductions from the existing
Library interfaces. They are defined at arbitrary universe `u`.

For a commutative base ring `R`, `dualNumberTestReduction_surjective` proves that
`Spec A → Spec A[ε]` is surjective on underlying spaces for every commutative
`R`-algebra `A`. The reduction homomorphism is surjective and its kernel is
square-zero. `exists_dualNumberLift_of_openImmersion` then lifts a dual-number
point through an open immersion whenever its reduction has a specified lift.
It preserves that specified reduced lift. The proof first places the entire
point's topological image in the open subscheme and then uses the open-immersion
lift and its monomorphism property.

Let an actual automorphic action of `P` on `H` and compatible homomorphisms
`d : H → G` and `i : P → G` be given over `Spec R`. Suppose group homomorphisms
`s : U → H` and `t : V → P` make ordered multiplication of their ambient images
an open immersion `U × V → G`. `exists_lieLift_of_openCell` proves that every
actual dual-number identity-kernel element of `G(A)` lifts to the existing
semidirect product `H ⋊ P`, for every `R`-algebra `A`. Here the kernel uses
`A[ε]` points reducing to the identity in `G(A)`. The open chart lifts the
identity-reducing point with reduced coordinates `(1,1)`. Composing its two
coordinates with `s` and `t` gives a point of the semidirect product. The
semidirect point equivalence shows that it reduces to the identity, and the
published formula for `semidirectHomLift` gives its original image.

`AutomorphicAction.lieLiftOfOpenCell` chooses such an actual kernel element.
`lieLiftOfOpenCell_target` proves its exact image equation. No canonical or
natural choice is asserted. Over a field, `smoothSurjective_of_openCell` applies
these lifts to the published linear map on the actual Lie kernels. If `H`, `P`
and `G` are smooth affine and `G` is connected, the published differential
criterion proves that the same semidirect multiplication is smooth and
surjective on schemes.

Finally, `Dynamic.normal_subgroup_product_smooth_surjective` assumes a smooth
connected affine group `G` over any field, a closed normal smooth affine subgroup
`d : H → G`, and a monomorphic homomorphism `i : P → G` from a smooth affine
group. A cocharacter `χ` must have its full all-relative-test range in `range d`,
and its dynamic parabolic functor `P_G(χ)` must lie in `range i`. Then actual
ordered multiplication `H × P → G` is smooth and surjective. Normality supplies
the existing normalized conjugation action. The inverse cocharacter still has
range in `range d`. The existing normal-subgroup contraction construction
factors the represented `U_G(-χ)` through `d`; represented-subgroup lifting
factors the represented `P_G(χ)` through `i`. The published opposite-cell
open-immersion theorem supplies the chart for the preceding differential
argument. The underlying semidirect homomorphism is the stated ordered
multiplication map.

These results impose no perfectness, infinitude, reductivity or characteristic
condition on the field. They establish a multiplication input for the host
rational-lifting proof; they do not prove that proof's full all-field target or
assert rational surjectivity of this multiplication map.
