# The finite étale sum of endomorphism images on torsion

This internal construction applies the actual torsion restriction in
`Langlands.AbelianScheme.TorsionFunctor` and the actual finite étale image
sum in `Langlands.GroupScheme.FiniteEtaleSum`. It introduces no external
geometric existence assertion.

Let `A` be an abelian scheme over an arbitrary scheme `S`, let `n` be a
signed integer, and let `f` be a family of actual endomorphisms of `A`
indexed by a finite type `I`. Assume explicitly that the structure
morphism of the actual torsion scheme `A[n]` is finite and étale. This
assumption is retained; the file does not deduce it from an arithmetic
or characteristic hypothesis.

In `AbelianScheme.FiniteEtaleSubgroup.TorsionImageSum`, `maps A n f i`
is the bundled restriction of `f i` to `A[n]`. `subgroup A n f`
is a `FiniteEtaleSubgroup A`: its group scheme is the actual image of
the sum map from the finite product of copies of `A[n]` to `A[n]`.
Its inclusion into `A` is the image inclusion followed by the torsion
inclusion. The first map is a closed immersion by the finite étale
image construction. The second is a closed immersion because `A` is
separated. Their composite is therefore a closed immersion, and the
image construction supplies the finite étale structure over `S`.

`component A n f i` factors the restricted image of each endomorphism
through this subgroup. `component_inclusion` identifies its composite
into `A` with the torsion inclusion followed by `f i`. The proof
composes the finite sum's component formula with the torsion inclusion
and uses the defining naturality formula for torsion restriction.

For any commutative group scheme `H` and actual homomorphism `g : A → H`,
`inclusion_comp_eq_zero_iff` says that `g` vanishes on the subgroup
exactly when each composite `A[n] → A → A → H`, using `f i` in the
middle, vanishes. This follows from the finite sum's vanishing criterion
applied to the torsion inclusion followed by `g`, and again the torsion
restriction formula. The target need not be finite, étale or abelian.

`inclusion_zsmul` says that the subgroup inclusion followed by
multiplication by `n` on `A` vanishes. The subgroup inclusion factors
through `A[n]`, where this is the defining kernel equation.
All vanishing equations use the actual pointwise additive law on
homomorphisms of commutative group schemes.

The index type may be empty, the integer may be zero or negative,
and the base may have nilpotents. The explicit finite étale torsion
hypothesis still applies in all these cases. This unit constructs the
subgroup only. Quotient existence, an integral model of a rational
action, and CM representability remain subsequent obligations.
