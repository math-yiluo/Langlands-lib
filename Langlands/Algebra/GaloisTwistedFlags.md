# Rational idempotents adapted to a twisted-stable flag

This internal module continues `Algebra/GaloisTwistedSubspaces` and
`Algebra/GaloisTwistedCompression`. Its setting is the same: `K/k` is a Galois
extension, possibly infinite (`IsGalois k K`), the matrices `P σ ∈ M_n(K)` are
invertible, and `A ⊆ M_n(K)` is a `k`-subalgebra of twisted-fixed matrices
(`A ≤ twistedFixed P`) whose `K`-span is `M_n(K)`.

Tits (*Représentations linéaires irréductibles d'un groupe réductif sur un
corps quelconque*, J. reine angew. Math. 247 (1971), Proposition 3.4, pp. 204–205)
uses two Galois-stable subspaces `Y ⊆ X` and passes to the subquotient
`X/Y`; he descends the flag to `k` through the submodule correspondence of
§1.4 (pp. 197–198). This development instead realizes the subquotient inside
the `k`-form `A` by an idempotent `f ∈ A` adapted to the flag `Y ⊆ X`, which
this module constructs; that choice of a complement is this development's
own. The compression `x ↦ F x E` with `E F = f` is then handled by
`Algebra/GaloisTwistedCompression`.

## Declarations

- `IsTwistedStable P V`: a `K`-subspace `V ⊆ Kⁿ` is twisted-stable if
  `u ∈ V` implies `σ⁻¹(P σ · u) ∈ V` for every `σ ∈ Gal(K/k)`. Here
  `σ⁻¹(w)` applies `σ⁻¹` to each coordinate. This is the hypothesis used by
  `exists_idempotent_ker_eq` in `Algebra/GaloisTwistedSubspaces`, now given a
  name.
- `symm_map_mulVec`: for a rectangular matrix `F`,
  `σ⁻¹(σ(F) · v) = F · σ⁻¹(v)`.
- `exists_adapted_idempotent`: let `n` be nonempty and let `Y ≤ X` be
  twisted-stable subspaces of `Kⁿ`. Then there is `f ∈ A` such that
  - `f * f = f`;
  - `f v ∈ X` for every `v`;
  - `f y = 0` for every `y ∈ Y`;
  - `f x - x ∈ Y` for every `x ∈ X`.

## Proof of `exists_adapted_idempotent`

1. `exists_idempotent_ker_eq` gives an idempotent `e₁ ∈ A` with kernel `X`.
   Then `g = 1 - e₁ ∈ A` is an idempotent with image in `X` that fixes `X`
   pointwise.
2. The published `exists_subspace_split_coordinates` gives coordinates
   for `X`: a matrix `B : n × d` whose columns lie in `X`, and `C : d × n`
   with `C B = 1` and `B C x = x` for `x ∈ X`. The published
   `range_coordinateInclusion_eq` shows that `B w ∈ X` for every `w`. Since
   `g` fixes the columns of `B`, `g B = B`. Put `F = C g`. Then `F B = 1`
   and `B F = g ∈ A`.
3. If `d = 0`, then `X = 0` and `f = 0` works.
4. Otherwise the corner `S = compressed A F B = {F a B | a ∈ A}` of
   `Algebra/GaloisTwistedCompression` is a twisted-fixed `k`-form of `M_d(K)`
   for the matrices `σ(F) P σ B`. Its `K`-span is `M_d(K)`, and these twisting
   matrices are invertible (`compressed_le_twistedFixed`,
   `isUnit_compressed_twist`, `span_compressed`).
5. `Y' = {w | B w ∈ Y}` is twisted-stable for `σ(F) P σ B`. Indeed, by
   `symm_map_mulVec`, `B σ⁻¹(σ(F) P σ B w) = g σ⁻¹(P σ B w)`. This vector is
   `σ⁻¹(P σ B w)`, which lies in `Y ⊆ X` because `B w ∈ Y`.
6. Applying `exists_idempotent_ker_eq` to `S` and `Y'` gives an idempotent
   `e' = F a B` (`a ∈ A`) with kernel `Y'`. Put `f = B e' F`.
   - `f = g a g`, so `f ∈ A`.
   - `f` is idempotent because `F B = 1` and `e'` is idempotent.
   - Its image lies in the image of `B`, which is in `X`.
   - For `y ∈ Y`, `B (F y) = g y = y ∈ Y`. So `F y ∈ Y'` and `e' (F y) = 0`.
   - For `x ∈ X`, write `x = B u` with `u = F x`. Then
     `f x - x = B (e' u - u)`, and `e' u - u ∈ Y'` because `e'` is
     idempotent with kernel `Y'`.

No continuity or cocycle condition on `σ ↦ P σ` is used.
