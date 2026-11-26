# The classes of a normal subgroup under one type form one orbit

This internal module proves the orbit part of Clifford's theorem for a compact
nonarchimedean group `G` and a normal subgroup `N`. Every type (continuous
irreducible representation of `G`) lies over some open-kernel irreducible class
of `N`. When moreover every commutator lies in `N` (`CommutatorsIn N`) and, for
every open subgroup `U` containing `N`, the powers of one element meet every
right coset of `U` (`CyclicOpenQuotients N`), the classes of `N` lying under one
type form a single `G`-orbit, the rank of the type is the orbit size times the
rank of a class, and triviality of the type on a normal subgroup inside `N` is
read off from one class. Without these conditions the rank formula can fail.
Compare J.-P. Serre, *Linear Representations of Finite Groups* (1977),
registered as `serre-1977-linear-representations`, §8.1, Proposition 24
(printed p. 61), where the isotypic components of the restriction to a normal
subgroup are permuted transitively.

## Results

- `exists_over`: every type `B` lies over some open-kernel irreducible object
  of `N`. The restriction of `B` to `N` has a maximal proper
  subrepresentation (the lattice of subrepresentations of a
  finite-dimensional space is well founded), and the quotient by it is
  irreducible (`Langlands.Classification.isIrreducible_iff_isCoatom_ker`). Its
  kernel contains the kernel of `B` on `N`, which is open since `B` is
  continuous (`isContinuous_iff_isOpen_ker`), and the quotient map is a nonzero
  intertwiner.
- `over_smul`: a type lying over `A` lies over the conjugate representative
  `conjugateOpenKernelIrreducible N g A` of `g • [A]`, by precomposing the
  intertwiner with `B g⁻¹`.
- `over_pullback`: pulling back a type and a class along a continuous
  automorphism preserving `N` preserves the relation.

The remaining results assume `CommutatorsIn N` and `CyclicOpenQuotients N`.
They use the extension `θ` of `A` to its stabilizer `H` from
`exists_extension_stabilizer` and the description `exists_phiObj_eq` of every
type over `A` as a coinduction `coind_H^G (twist χ θ)` (module
`Langlands.Representation.Clifford.Fiber`).

- `finrank_of_over`: if `B` lies over `A`, then
  `dim B = [G : H] · dim A`, since `B` is equivalent to a coinduction from `H`
  of a representation of dimension `dim A` (`finrank_coindObj`).
- `exists_smul_eq_of_over`: if `B` lies over `A` and over `A'`, then
  `[A'] = g • [A]` for some `g`. Otherwise no conjugate of `A` is equivalent to
  `A'`, and `intertwining_eq_zero` (module
  `Langlands.Representation.Clifford.Coinduction`) kills every
  `N`-intertwiner from the coinduction to `A'`, contradicting `Over N B A'`.
- `trivial_iff_of_over`: for a normal subgroup `M ≤ N` and `B` over `A`, `B`
  is trivial on `M` exactly when `A` is trivial on `M`. One direction uses the
  surjectivity of a nonzero intertwiner onto the irreducible `A`. For the
  other, `twist χ θ` is trivial on the conjugates `y m y⁻¹ ∈ M`, so the
  coinduction is trivial on `M`.
