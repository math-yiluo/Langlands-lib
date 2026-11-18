# Brauer class of a compressed twisted-fixed algebra

This internal module continues `Algebra/GaloisTwistedCompression`. That
module associates to a `k`-subalgebra `B ⊆ M_N(K)` and rectangular matrices
`F : r × N`, `E : N × r` with `F E = 1` and `E F ∈ B` the compression
`compressed B F E = {F x E | x ∈ B} ⊆ M_r(K)`. Here it is shown that, when
`B` is a twisted-fixed central simple `k`-form, the compression has the same
Brauer class as `B`. This is the corner step in this development's proof of
the additivity of the Tits class (Tits, *Représentations linéaires
irréductibles d'un groupe réductif sur un corps quelconque*, J. reine angew.
Math. 247 (1971), Corollary 3.5, p. 205, via Proposition 3.4, pp. 204–205).

In that application (`Reductive/TitsAdditivity`), `B` is the image of the
Kronecker map on the tensor product of the Tits algebras of the two factors
`ρ₁` and `ρ₂`. It contains the Tits algebra of the tensor representation
`ρ₁ ⊗ ρ₂`, and the inclusion can be strict. For example, for the standard
representation `V` of split `SL₂` over `ℚ` (with `K = k`), the Tits algebra
of `V ⊗ V` preserves `Sym² V` and the alternating line `Λ² V`, on which it
acts by scalars, so it has a proper nonzero ideal; the tensor product of the
factor Tits algebras is `M₄(ℚ)`. The Tits algebra of the subquotient `X/Y`
is a compression of `B` (`MatrixRepresentation/TitsAlgebraCompression`).

The compression by an adapted idempotent, and hence the choice of a
complement of `Y` in `X`, is this development's own matrix argument. Tits
instead descends the invariant flag to `k` and passes to the quotient through
the submodule correspondence of §1.4 (pp. 197–198).

The Brauer-theoretic input is the corner theorem `isBrauerEquivalent_cornerCSA`
of the published module `Langlands/Algebra/CentralSimpleCorner` (Task 7605). It states that a corner `e A e` of a central simple
algebra `A` at a nonzero idempotent `e` is central simple and Brauer
equivalent to `A`.

## Declarations

- `isIdempotentElem_compression`: `E F` is an idempotent of `B`, since
  `(E F)(E F) = E (F E) F = E F`.
- `mul_mem_of_mem_compressed`: if `z ∈ compressed B F E`, then `E z F ∈ B`.
  Indeed, for `z = F x E` we get `E z F = (E F) x (E F)`.
- `compressedEquivCorner`: a `k`-algebra isomorphism from
  `compressed B F E` to the corner `(E F) B (E F)`. The corner is Mathlib's
  `IsIdempotentElem.Corner`, with the `k`-algebra structure of
  `CentralSimpleCorner`.
  - The forward map sends `z` to `E z F`; the inverse sends a corner element
    `c` to `F c E`.
  - `F (E z F) E = z` and `E (F c E) F = (E F) c (E F) = c`.
  - Multiplicativity: `E (z w) F = (E z F)(E w F)`, because `F E = 1`.
  - Scalars: `E (c · 1) F = c · (E F)`, and this is `cornerInclusion_algebraMap`.
- `compression_ne_zero`: if `r` is nonempty, then `E F ≠ 0`, because
  otherwise `1 = (F E)(F E) = F (E F) E = 0` in `M_r(K)`.
- `isBrauerEquivalent_toCSA_compressed`: let `K/k` be Galois and let `N` and
  `r` be nonempty. Let `B ≤ twistedFixed P` have `K`-span `M_N(K)`, where the
  `P σ` are invertible. Then the central simple algebra `toCSA` of the
  compression, for the twisting matrices `σ(F) P σ E`, is Brauer equivalent
  to `toCSA P B`.
  - `compressedEquivCorner`, applied entrywise to `1 × 1` matrices, shows that
    the compression is Brauer equivalent to `cornerCSA (toCSA P B)` at `E F`.
  - `isBrauerEquivalent_cornerCSA` then gives the equivalence with
    `toCSA P B`.
