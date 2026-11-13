# Central isogenies whose torus restriction has cocharacter index two

This module works over an arbitrary field `k` in an arbitrary universe. It
treats a central isogeny `p : G ⟶ G'` (`IsCentralIsogeny`) with `G` connected
reductive and a commuting square

    i ≫ p = groupHom t ≫ i'

where `T` and `T'` are split tori, `i : T ⟶ G` is a maximal torus
(`IsMaximalTorus`), `i' : T' ⟶ G'` is only a closed subgroup, and `t : T ⟶ T'`
is a homomorphism of commutative group schemes. Assume the image of the actual
cocharacter pushforward `RealTorusSpace.cocharacterMapInt t` has index two in
the cocharacter lattice of `T'`, written as `Nat.card` of the quotient equal to
`2`. The main definition `IsCentralIsogeny.indexTwoKernelIso` is then an
isomorphism of group schemes from the diagonalizable group scheme
`Diagonalizable.groupScheme k (ULift (ZMod 2))`, that is `D(ℤ/2)`, to the full
scheme-theoretic kernel `kernel p`. Classically `D(ℤ/2)` is `μ₂`, the spectrum
of `k[x]/(x² - 1)`; this module does not state that identification.

The kernel is the actual pullback kernel on every test scheme over `Spec k`.
No reducedness or smoothness of the kernel is used or asserted, and
characteristic two is allowed. There `D(ℤ/2)` is nonreduced, and the
isomorphism still holds for the scheme-theoretic kernel. The torus `T'` need
not be maximal in `G'`.

## Lattice algebra

The first section is pure algebra over `ℤ`. It uses two perfect pairings
`P : X × Y → ℤ` and `P' : X' × Y' → ℤ`, an injective `b : Y → Y'` with
quotient of order two, and an `a : X' → X` adjoint to `b`, so that
`P' χ (b ν) = P (a χ) ν`.

- `halfForm` halves an integral linear form whose values are all even.
- `two_smul_mem_range`, `exists_not_mem_range` and `mem_range_or_sub_mem_range`
  record that in a quotient of order two, twice every element lies in the
  subgroup, and every element is either in the subgroup or differs from a fixed
  nonzero class `n₀` by an element of the subgroup.
- `doubleLift` is the linear map `n ↦ b⁻¹(2n)`. It is well defined by the
  previous point and injectivity of `b`.
- `eq_zero_of_two_smul_eq_zero`: the right lattice of a perfect pairing has no
  `2`-torsion.
- `exists_parity` builds a surjective homomorphism `Φ : X → ℤ/2` with kernel
  exactly the image of `a`. Choose `n₀ ∉ b(Y)` and put `m₀ = b⁻¹(2n₀)`; then
  `Φ χ` is the parity of `P χ m₀`.
  - Surjectivity: if every `P χ m₀` were even, perfectness would give
    `m₀ = 2m₁`. Then `b m₁ - n₀` would be `2`-torsion in `Y'`, so zero,
    contradicting `n₀ ∉ b(Y)`.
  - Kernel contains the image: `P (a ψ) m₀ = P' ψ (2n₀)` is even.
  - Kernel is contained in the image: if `P χ m₀` is even, then
    `n ↦ P χ (b⁻¹(2n))` has only even values. This holds on `b(Y)` directly
    and on `n₀ + b(Y)` through `m₀`. Half of this form is represented by some
    `ψ ∈ X'` by perfectness of `P'`. Evaluating on `b ν` gives `P (a ψ) ν = P χ ν`
    for all `ν`, so `a ψ = χ` by perfectness of `P`.

## The torus kernel

`latticePairing_cocharacterMapInt` checks that the actual pullback of
characters `characterLattice.comapHom (groupHom t)` is adjoint to
`cocharacterMapInt t` for the actual pairings `latticePairing`. These pairings
are perfect for split tori by the published
`CocharacterUniformizer.latticePairing_isPerfPair`.
`nonempty_homKernelLattice_addEquiv` applies `exists_parity` to obtain an
additive equivalence from `Diagonalizable.homKernelLattice (groupHom t)`, the
quotient of the characters of `T` by the image of pullback, to `ℤ/2`.
`homKernelLatticeEquiv` chooses one such equivalence. The choice is harmless
in fact, because an additive equivalence onto `ℤ/2` is unique; this module
does not prove that uniqueness. `torusKernelIso` composes the induced
isomorphism of diagonalizable group schemes `Diagonalizable.congrIso` with the
published `Diagonalizable.homKernelDiagonalizableIso`. That isomorphism
identifies the full kernel of a homomorphism of split tori with the
diagonalizable group of this quotient. The result is
`D(ℤ/2) ≅ kernel (groupHom t)`.

## Comparison of kernels

For a test scheme `U` over `Spec k`, `kernelPointsMap` sends a `U`-point of the
kernel of `groupHom t` to its composite with `i`. `comp_comp_eq_one` uses the
square to show that this composite is killed by `p`.
`kernelPointsMap_bijective` proves that this is a bijection onto the
`U`-points of the kernel of `p`.

- Injectivity: `i` is a closed immersion, hence a monomorphism.
- Surjectivity: a `U`-point `z` of the kernel of `p` is central, because the
  kernel of a central isogeny is central for all test points
  (`IsCentralIsogeny.mem_center_of_comp_eq_one`). Hence `z` lies in the
  centralizer of the torus (`center_le_torusCentralizer`). The published
  theorem `maximalTorusCentralizer` says this centralizer is the range of `i`
  for a maximal torus of a connected reductive group over a field. Writing
  `z = y ≫ i`, the square gives `y ≫ groupHom t ≫ i' = 1`. Since `i'` is a
  closed immersion, hence a monomorphism, `y` lies in the kernel of
  `groupHom t`.

`kernelPointsComparison` is the resulting multiplicative equivalence of
`U`-points, transported through the published `kernelPointsEquiv` for both
kernels. `kernelPointsComparison_comp_kernelι` and
`kernelPointsComparison_naturality` show that it is compatible with the
kernel inclusions and natural in `U`. `kernelComparisonIso` is the
group-scheme isomorphism `kernel (groupHom t) ≅ kernel p` obtained by
`isoOfPoints`. `kernelComparisonIso_hom_kernelι` says that its composite with
the inclusion of the kernel of `p` is the torus-kernel inclusion followed by
`i`.

## Main result

`IsCentralIsogeny.indexTwoKernelIso` is the composite of `torusKernelIso` and
`kernelComparisonIso`. Injectivity of `cocharacterMapInt t` is not an extra
hypothesis. It comes from the published
`IsCentralIsogeny.cocharacterMapInt_injective_of_square`, which uses only that
`i` and `i'` are closed subgroups. `IsCentralIsogeny.indexTwoKernelIso_hom_kernelι`
records that the isomorphism lands in the torus: followed by the inclusion of
`kernel p`, it equals `torusKernelIso` followed by the torus-kernel inclusion
and `i`.

## Provenance

The construction is internal. It specializes a standard fact to cocharacter
index two. For a homomorphism of split tori, the kernel is the diagonalizable
group of the cokernel of character pullback. Over a field, the kernel of a
central isogeny of connected reductive groups lies in every maximal torus.
The Library inputs are the published full-kernel model
`homKernelDiagonalizableIso`, perfectness of the character–cocharacter
pairing of a split torus, injectivity of the cocharacter pushforward over a
central isogeny, and the published `maximalTorusCentralizer`. The lattice step
is a direct computation with the two perfect pairings. This module does not
construct the isogeny, the tori or the square, and it does not compute any
root datum.
