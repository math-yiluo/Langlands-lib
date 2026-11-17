# Group-algebra facts behind torsion determination

Module `Langlands.GroupScheme.Torus.TorsionDetermination.Algebra`, namespace
`Langlands.GroupScheme.TorsionDetermination`.

This is a helper module for the proof of
`Langlands.GroupScheme.MultiplicativeTypeTorsionDeterminationStatement` (SGA 3, Exposé IX,
4.8–4.9). It collects the purely algebraic facts about group algebras used in the
diagonalizable case (module `...TorsionDetermination.Diagonalizable`). These are internal
lemmas, not statements quoted from the literature. They make precise the two density
facts behind SGA 3's argument: torsion characters separate the functions on `D(Λ)`, and over a
field the torsion points are dense in a split torus.

## Declarations

- `Diagonalizable.exists_freeFiniteEquiv Λ`: a finitely generated abelian group `Λ` (in universe `u`) is
  isomorphic to `(I → ℤ) × A` with `I` a `Fintype` and `A` a finite abelian group, both in
  universe `u`. Proof: Mathlib's `AddCommGroup.equiv_free_prod_directSum_zmod`, with the index
  types and the torsion part lifted to universe `u` by `ULift`.
- `TorsionDensity.multiples Λ n`: the subgroup `nΛ`, defined as the range of `x ↦ n • x`.
- `exists_not_mem_nsmulSubgroup`: a nonzero `d` in a finitely generated `Λ` lies outside `nΛ`
  for some `n > 0`. Proof: write `Λ ≅ ℤ^I × A`. If the free part of `d` vanishes, take
  `n = |A|`, which kills `A`. Otherwise take `n = |d_i| + 1` for a nonzero coordinate `d_i`.
  Then `n` does not divide `d_i`.
- `exists_injOn_mk_nsmulSubgroup s`: for a finite set `s ⊆ Λ`, the quotient map
  `Λ → Λ/nΛ` is injective on `s` for some `n > 0`. Take for `n` the product of the integers
  obtained above for all differences of pairs in `s`.
- `coeff_mapDomain_of_injOn`, `mapDomain_ne_zero_of_injOn`: if `f` is injective on the support
  of `x ∈ R[M]`, then `mapDomain f x` has coefficient `x_a` at `f a`. In particular
  `mapDomain f x ≠ 0` whenever `x ≠ 0`.
- `exists_mapDomain_mk_ne_zero` (**torsion quotients detect group-algebra elements**): for any
  semiring `R` and finitely generated `Λ`, a nonzero `x ∈ R[Λ]` has nonzero image in
  `R[Λ/nΛ]` for some `n > 0`.
- `castPi I n`: the reduction homomorphism `ℤ^I → (ℤ/n)^I`.
- `isReduced_zmod`: for a field `K`, a finite `I` and `n ≠ 0` with `(n : K) ≠ 0`, the group
  algebra `K[(ℤ/n)^I]` is reduced. The order `n^|I|` of the group is invertible in `K`, so
  Maschke's theorem (Mathlib's semisimplicity instance for `AddMonoidAlgebra`) makes the ring
  semisimple. A commutative semisimple ring is reduced.
- `exists_not_isNilpotent_mapDomain_castPi` (**separable torsion quotients detect Laurent
  polynomials**): over a field `K` and for finite `I`, a nonzero `x ∈ K[ℤ^I]` has
  non-nilpotent image in `K[(ℤ/n)^I]` for some `n > 0` with `(n : K) ≠ 0`. Proof: let `B`
  bound the absolute values of all coordinates of exponents in the support of `x`. Choose a
  prime `p > 2B + char K + 1`. Then `castPi I p` is injective on the support of `x`, so the
  image is nonzero. It is not nilpotent because `K[(ℤ/p)^I]` is reduced.

The free/finite decomposition and multiples subgroup are reused from `DiagonalizablePowerDecomposition` and `TorsionDensityLattice`.
