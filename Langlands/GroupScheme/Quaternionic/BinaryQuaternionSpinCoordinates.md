# Root-of-unity coordinates of the diagonal binary spin homomorphism

This internal construction identifies the original diagonalizable μ₂ points
with units whose square is one and gives the diagonal spin homomorphism's
formula in these coordinates on every relative test scheme.

In `BinaryKernel`, `characterRootsEquiv` is a multiplicative equivalence between
unit-valued characters of `TwoLattice = ULift (ZMod 2)` and
`rootsOfUnity 2 R`, for any commutative ring `R`. The lattice and coefficient
ring can lie in different universes. The forward map evaluates a character at
the distinguished generator. The inverse uses `characterOfUnit` from the
preceding diagonal-kernel construction. Its inverse laws follow from the
evaluation identity and injectivity of character evaluation. The theorems
`characterRootsEquiv_val` and `characterUnit_characterRootsEquiv_symm`
record the underlying units in each direction.

For a field `K` and a finite-dimensional central division `K`-algebra `D`,
`rootsPointsEquiv T` composes the existing diagonalizable character point model
with this equivalence. It identifies actual μ₂ points over every `T` over
`Spec K` with `rootsOfUnity 2 (BinaryScheme.coefficients T)`, using the section
algebra's structural `K`-algebra structure. This includes the full μ₂ points
on nonreduced tests.

For `Module.finrank K D = 4`, `rootScalarNormOne` sends such a root to the
associated scalar reduced-norm-one unit by the existing character construction.
Its value formula is exactly
`normCoverScalarUnits K D R u.val`. The theorem `diagonal_root_coordinates`
identifies the two coordinates of the original diagonal morphism at a root:
the actual matrix `diag(u,u⁻¹)` in `SL₂` and this scalar norm-one unit.
The projection identities `diagonal_root_fst` and `diagonal_root_snd`
identify these as the actual upper diagonal cocharacter point and the
actual norm-one point, respectively. These comparisons use the represented
point equivalences, so they are equalities of relative scheme points.

The remaining results assume `K` infinite, `D` of dimension four, a first-kind
involution `σ` whose symmetric subspace has dimension three, a supplied
hyperbolic pair in `q`, a supplied spin cover `π : S ⟶ σ.isometryGroup q`,
and the explicit premise
`CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement`.
The theorem `diagonalSpin_root_points` expresses the diagonal spin point at `u`
as the product of the scalar lift at the inverse Gm point model of `u.val`
and the norm-one lift at the inverse norm-one point model of the scalar
norm-one unit. This is precisely the all-test formula
`z(u) = μ(u) ψ(u·1)` for the existing lifts. The proof applies the combined
homomorphism's product formula and the two projection identities.

Finally `existsUnique_root_of_kernel` assumes that `diagonalSpin` is a
monomorphism on underlying relative schemes and that the subgroup functor
`range (kernelι π)` is contained in `range productHom`. It concludes that
each spin-kernel point on every original relative test scheme has exactly one
root-of-unity parameter for `diagonalSpin`. Existence follows from the
previous exact image-intersection theorem; uniqueness cancels the assumed
monomorphism and uses the root point equivalence. The coefficient ring in this
theorem is the relative test's section algebra.

The provenance is internal: this combines the published character evaluation
and inverse construction, the actual diagonalizable and binary point models,
and the combined lift's multiplication and image formulas. No external source
correspondence is claimed. Characteristic is unrestricted. The final theorem's
diagonal monomorphy and kernel coverage assumptions remain separate obligations.
