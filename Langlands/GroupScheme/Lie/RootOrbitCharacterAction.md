# The torus action on root-orbit field coordinates

This internal unit computes how rational points of an original maximal torus
act on the published field coordinates `rootOrbitFieldWeightSpaceEquiv` of an
original relative weight space. The values are actual root values. It also
shows that these coordinates are linear over the base field. It uses the
published actual base change of points and Lie algebras, the canonical Galois
transport of characters, and the actual root-orbit reconstruction.

## Points and Galois transport

Let `k -> K` be a field extension and `T` a commutative group scheme over
`k`. `affineBaseChangeEquiv_comp_baseChange` states that the published
equivalence `Lie.affineBaseChangeEquiv` between `K`-points of a scheme base
change and original points over `K` is natural in group-scheme homomorphisms.
`rationalBaseChangePoint k K T h` is the `K`-point of the actual base change
`T_K` that corresponds to the image of a `k`-point `h` under `k -> K`.

`characterValue_galoisRepresentation_rationalBaseChangePoint` states that for
`σ` in `Aut(K/k)` and a character `χ` of `T_K`, the canonical Galois transport
`σχ` takes the value `σ(χ(h_K))` at `h_K`. The proof applies the published
`Lie.characterValue_galoisRepresentation` at the twisted test point
`Lie.galoisTestPoint`. It then pushes that point back to `K` along the
`K`-algebra map `σ⁻¹` out of the twisted test algebra. Over the original base
this recovers `h_K`, because maps of `k`-algebras out of `k` are unique.
`CoordinateWeights.characterValue_affineMap` then gives the equation.

## Root values and the adjoint action

Now let `L/k` be a field extension, `j : T -> G` an actual homomorphism into
an affine group scheme, and `β` an actual root of the split base change.
`kernelBaseChange_adjoint_rationalBaseChangePoint` states that the adjoint
action of `h ≫ j` commutes with the passage to the actual base-changed Lie
algebra, where it becomes the adjoint action of `h_L ≫ j_L`.
`adjoint_rationalBaseChangePoint_of_mem_weightSpace` states that on an actual
weight space of `T_L` for `χ`, the adjoint action of `h_L ≫ j_L` is
multiplication by `χ(h_L)`.

`rootOrbitCharacterValue k L j β h` is the value `β(h_L)` as an element of the
published stabilizer field `rootOrbitField k L j β`. It lies there because
every `σ` fixing `β` fixes `β(h_L)`, by the Galois transport formula above.
When `L/k` is finite Galois, `rootOrbitEmbeddingEquiv_characterValue` states
that the embedding of this field attached to an orbit root `ρ` sends the value
to `ρ(h_L)`.

## The action on field coordinates

Assume further that `G` is locally of finite type and connected reductive,
`j` is a maximal torus, `T_L` and the acting torus `S` are split, `a` is a
nonzero character of `S`, and the Galois orbit of `β` equals the whole fiber
`rootRestrictionFiber k L j f a`. These are the hypotheses of
`rootOrbitFieldWeightSpaceEquiv`. `rootOrbitFieldFixedSpanEquiv_val` states
that the ambient vector of a field element `x` is the sum, over orbit roots
`ρ`, of the root-line vectors at `ρ`'s embedding of `x`.

`adjoint_rootOrbitFieldWeightSpaceEquiv` is the main result. For every
`k`-point `h` of `T`, the adjoint action of `h ≫ j` sends the original vector
with coordinate `x` to the vector with coordinate `β(h_L) · x`. The proof is
injectivity of the published `Lie.baseChangeFixedLieEquiv`. After base change,
each orbit summand lies in the actual weight space of `ρ`. There `h_L` acts by
`ρ(h_L)`, which is the embedding at `ρ` of `β(h_L)`. Since that embedding is
multiplicative and the root-line equivalence is `L`-linear, the sum is the
vector with coordinate `β(h_L) · x`.
`conjugation_differential_rootOrbitFieldWeightSpaceEquiv` states the same
result for a rational point `z`. There the action is the differential of
actual conjugation along `j` at `GaloisPointComparison.rationalCoeffEquiv`,
which equals the adjoint action by the published
`AutomorphicAction.differential_conjugation`.

`rootOrbitFieldWeightSpaceEquiv_smul` states that the coordinates commute with
scalars from `k`. The proof again uses base-change injectivity: extension of
coefficients is semilinear over `k -> L`, every field embedding is `k`-linear,
and every root-line equivalence is `L`-linear.
`rootOrbitFieldWeightSpaceLinearEquiv` packages the coordinates as a
`k`-linear equivalence.

The value is the root `β` of the split torus over `L`, evaluated at a
base-changed rational point. This unit does not descend `β` to a rational
character of the base change of `T` to the stabilizer field. It also does not
treat multipliable roots. All results are uniform in the universe and the
characteristic.
