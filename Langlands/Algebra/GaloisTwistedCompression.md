# Compressions of twisted-fixed matrix algebras

This internal module treats corners of the descended matrix algebras of
`Algebra/GaloisTwistedMatrix` in matrix form. It is the algebraic part of the
simple-weight comparison of Tits (*Représentations linéaires irréductibles
d'un groupe réductif sur un corps quelconque*, J. reine angew. Math. 247
(1971), Proposition 3.4, pp. 204–205). There the Tits algebra of a
subquotient `X/Y` of a representation with descent data is compared with the
descended algebra of the ambient representation. Realizing `X/Y` as a
compression `x ↦ F x E` is this development's own matrix formulation; Tits
descends the flag `Y ⊆ X` itself (§1.4, pp. 197–198).

Let `B ⊆ M_N(K)` be a `k`-subalgebra. Let `F : K^N → K^r` and `E : K^r → K^N`
be rectangular matrices with `F E = 1` and `E F ∈ B`. So `f = E F` is an
idempotent of `B`, and `E`, `F` identify its image with `K^r`.

## Declarations

- `compressed B F E hFE hf` is the set `{F x E | x ∈ B}`. It is a `k`-subalgebra of
  `M_r(K)`: `(F x E)(F y E) = F (x f y) E`, `F 1 E = 1`, and scalars map to
  scalars. It is the corner `f B f` transported to `M_r(K)` (inverse
  `z ↦ E z F`). `mem_compressed` records membership of `F x E`.
- `compressed_le_twistedFixed`: if `B ≤ twistedFixed P`, the compression is
  twisted-fixed for the compressed twisting matrices `σ(F) · P σ · E`. Both
  sides of the twisted-fixed identity reduce to `σ(F) P σ x E`, using
  `P σ f = σ(f) P σ` and `P σ x = σ(x) P σ`.
- `isUnit_compressed_twist`: the compressed twisting matrices are invertible
  when every `P σ` is, with explicit right inverse `F (P σ)⁻¹ σ(E)`.
- `span_compressed`: if `B` spans `M_N(K)` over `K`, its compression spans
  `M_r(K)`, since `z = F (E z F) E`.

With these, `toCSA` of module `GaloisTwistedMatrix` applies to the
compression, for `K/k` Galois and `r` nonempty. No continuity or cocycle
hypothesis is used.
