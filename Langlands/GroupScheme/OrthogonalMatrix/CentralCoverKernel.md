# A specified generator of an even orthogonal cover kernel

This internal supporting unit works over any field `k` in universe `u`. Let
`p : S → O(2l)⁰` be a central isogeny with algebraically simply connected
source, where the finite index type `l` has at least three elements.

For a compatible split maximal torus `i : T → S` with restriction
`t : T → 𝔾_m^l`, suppose a cocharacter `c` maps to `2eᵢ₀` in the standard
orthogonal coordinates. `centralCoverEvenImage` constructs the four
`SpinKernelTorus.EvenImage` hypotheses. Injectivity is the published
finite-isogeny cocharacter injectivity. The actual range calculation
`range_cocharacterCoord_eq_pairLattice` gives even sums and preimages of
all coordinate differences. The last field is the supplied coordinate
identity for `c`.

`centralCoverCocharacter_comp_injective` states that composing a point
of `𝔾_m` with `c` and `i` is injective on every relative test scheme.
The half-sum character from `SpinKernelTorus` recovers the original point,
and the closed immersion `i` permits cancellation.

`existsUnique_kernel_comp_eq` states that every point `x` of `S` killed by
`p` has exactly one parameter `u` with `u² = 1` and `i(c(u)) = x`.
The published `IndexTwoKernel.kernelPointsMap_bijective` moves `x` into
the torus kernel. The half-sum-character argument
`EvenImage.exists_comp_eq` supplies its square-root parameter, and the
preceding injectivity proves uniqueness.

Finally, `existsUnique_kernel_lift_comp_eq` requires only an ambient lift
`a : 𝔾_m → S` whose projection has coordinate `2eᵢ₀`. The published
`centralIsogenySplitMaximalTorusLift` constructs a compatible split maximal
torus. `IsCentralIsogeny.maximalTorusFactor` factors `a` through it with
the prescribed torus composite, so the preceding result applies.

`liftedCocharacter_comp_eq_one` proves the converse: each square root
parameter maps into the kernel. In coordinates the projected cocharacter
is twice the coordinate cocharacter at `i₀`, so it kills a point whose
square is one. `kernelPointsEquiv` is the resulting equivalence from
square roots of unity to the points killed by `p`, and
`kernelPointsEquiv_apply_val` records its specified forward map `u ↦ a(u)`.

These are statements about all relative test schemes, including nonreduced
ones, and use no characteristic restriction. Their provenance is the
explicit composition of the named Library lattice, torus and centralizer
results. They neither construct the quaternionic adapted coordinates nor
identify the binary Levi diagonal; those comparisons remain necessary for
the host task's `SpinKernelGeneratorStatement`.
