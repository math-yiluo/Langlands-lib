# Induction of a character with separated conjugates on a normal subgroup

This module proves the representation-theoretic part of the irreducibility
criterion for monomial representations, over an arbitrary field `K`, and
collects the equivalences of finite-dimensional representations used to
compare a restriction of an induced representation with another induction.

## Diagonal coordinates

`irreducible_of_diagonal_coordinates` and `scalar_of_diagonal_coordinates`
treat a representation `ρ` of a group `G` on `V` with a linear isomorphism
`e : V ≃ K^ι`, `ι` finite and nonempty. The hypotheses are:

- a family of group elements `b x` acts diagonally in these coordinates, with
  eigenvalue `a x i` at `i`;
- the eigenvalue functions separate coordinates: for `i ≠ j` some `x` has
  `a x i ≠ a x j`;
- the group moves every coordinate to every other: for all `i, j` some `g`
  satisfies `e (ρ g v) j = e v i`.

Then `ρ` is irreducible, and every linear endomorphism commuting with `ρ` is
a scalar. For irreducibility, separation lets one isolate each coordinate of
a vector in an invariant subspace by repeatedly applying
`(b x - a x j)/(a x i - a x j)`. The private lemma
`single_mem_of_diagonal_separation` does this. Transitivity then gives every
basis vector. For the scalar statement, a commuting endomorphism is diagonal
by separation, and transitivity makes its diagonal entries equal.

## Induced lines

`induce_twist_irreducible_scalar_of_separation`: let `S` be a finite-index
subgroup of `G`, `N ≤ S` a normal subgroup of `G`, and `φ : S → Kˣ` a
character. Suppose that for `x, y ∈ G` in different right cosets `S x ≠ S y`
some `n ∈ N` has `φ(x n x⁻¹) ≠ φ(y n y⁻¹)`. Then the induction from `S` of the
line on which `S` acts by `φ`,
`induce S (twist φ (of 1))`, is irreducible and has scalar endomorphisms.
In the coset coordinates `Induction.coordinates`, `n ∈ N` acts at the coset
of `x` by `φ(x n x⁻¹)`, and `G` permutes the cosets transitively, so the
previous section applies. This is a form of Mackey's irreducibility
criterion for a monomial representation whose conjugate characters on a
normal subgroup are pairwise distinct. It is proved here directly, without
finiteness of `G`.

## Equivalences

- `hasScalarEndomorphisms_of_equiv` and `isIrreducible_of_equiv`: scalar
  endomorphisms and irreducibility are invariant under equivalence of
  representations. The second is a form of
  `CentralEigenspaceSplitting.isIrreducible_iff_of_equiv`.
- `restrictInduceEquivOfOneCoset`: Mackey's formula with one double coset.
  Let `H ≤ G` and `S ≤ Γ` have finite index, `ι : Γ → G`, and `x ∈ G`. Let
  `κ : S → H` be conjugation by `x` after `ι`. Assume that `x ι(ℓ) x⁻¹ ∈ H`
  implies `ℓ ∈ S`, and that `G = H x ι(Γ)`. Then the restriction along `ι` of
  `induce H A` is equivalent to `induce S (restrict κ A)`. The equivalence is
  `mackeyEquiv` of `Langlands.VirtualRepresentation.ExactMackey` for a single
  double coset, with intertwining from `mackeyMap_intertwines`. The
  `x = 1` case appears in the proof of
  `GeneralPosition.induce_irreducible_of_one_coset`.
- `restrictTwistLineEquiv` and `twistLineEquivOfEq`: restricting the line of
  `φ` along `κ` gives the line of `φ ∘ κ`, and equal characters give
  equivalent lines. Both are the identity of `K`.
