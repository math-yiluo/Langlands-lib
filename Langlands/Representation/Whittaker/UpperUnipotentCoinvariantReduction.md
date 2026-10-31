# Reductions for character-localized upper-unipotent coinvariants

Author: Worker 784. This module is an internal prerequisite of the exact proof task
`62de5903-b616-4b5c-88eb-a066b77c5467`, which proves
`Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`. It proves two
reductions for the published quotient `Jacquet.Localization.Coinvariants ρ U η` of
[`Jacquet/Localization`](../Jacquet/Localization.md). That quotient divides `V` by the span of
`ρ(u)v - (η u : R) • v` for `u ∈ U`, the positive-character convention of
Bernstein–Zelevinsky (1976), §2.30–§2.35 (printed pages 24–25). Source:
`bernstein-zelevinsky-1976-representations-gln`, SHA-256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.

The group-theoretic input comes from
[`UpperUnipotentCharacterFactorization`](UpperUnipotentCharacterFactorization.md).

## The two-block shape

- `ProductLeviChamber.twoBlock N a ha haN : BlockShape N`, for `0 < a < N`,
  is the existing ordered block shape with sizes `![a, N - a]`, now shared through
  [`TwoBlockShape`](../../Group/GL/TwoBlockShape.md). Its existing
  `twoBlock_index_val` says that coordinate `r` of the first block is `r`, and
  coordinate `r` of the second block is `a + r`. This module reuses both declarations
  directly. `cutShape_length` records the two blocks; `cutFirst` and `cutSecond`
  name the two block indices.
- `cutShape_parabolic_ne_top`: the parabolic is proper over every field. The lower
  transvection `1 + E_(a,0)` has a nonzero entry strictly below the block diagonal, so it
  does not lie in the parabolic.
- `isBlockUnipotent_of_mem_cutShape`: every element of the published unipotent radical
  subgroup `(twoBlock N a _ _).unipotentSubgroup F` satisfies the published predicate
  `IsBlockUnipotent a`, that is, it equals `[[I_a, Y], [0, I]]`.

## Degenerate vanishing

`subsingleton_coinvariants_of_adjacentUnit` covers every field `F` with a topology, every
`n`, and every complex representation `ρ` of `GL_(n+1)(F)` on `V : Type uV` with
`GeneralLinear.IsSupercuspidal ρ`. Take any homomorphism
`η : upperUnipotent (n + 1) F →* ℂˣ` and any `k : Fin n` with
`η (adjacentUnit k x) = 1` for all `x`. Then

```text
Subsingleton (Jacquet.Localization.Coinvariants ρ (upperUnipotent (n + 1) F) η)
```

No smoothness, irreducibility, local constancy or nontriviality hypothesis is used.

Proof. Put `B = twoBlock (n + 1) (k + 1)`. Each element `u` of the radical
`B.conjugateUnipotent 1` is block unipotent, so it is upper unipotent, and
`character_eq_one_of_isBlockUnipotent` gives `η u = 1`. Hence the quotient map onto the
`η`-coinvariants is invariant under `B.conjugateUnipotent 1` and factors through
`Jacquet.Coinvariants ρ (B.conjugateUnipotent 1)`. That quotient is a subsingleton by the
Jacquet clause of the published `IsSupercuspidal` (second component), applied to the
proper parabolic `B` and the conjugating element `1`. The admissibility component is not
used. This is the argument of BZ76 §5.15(a), step (2) ⇒ (3) (printed page 49), here for
representations of `G`. A degenerate character is trivial on a nontrivial standard
radical `U_β`, and `E_(U_β) = 0` forces `E_(U,θ) = 0`.

## Conjugation

The section covers a commutative ring `R`, a group `G`, a representation `ρ` on an
`R`-module `V`, a subgroup `U`, characters `θ η : U →* Rˣ` and an element `g : G`, under
two hypotheses:

- `hg : ∀ u : U, g⁻¹ * u * g ∈ U`;
- `hη : ∀ u, η ⟨g⁻¹ * u * g, hg u⟩ = θ u`.

Under these hypotheses:

- `conjugationMap ρ U θ η g hg hη` is the linear map `V_(U,θ) → V_(U,η)` induced by
  `v ↦ [ρ(g⁻¹) v]`. It is well defined because
  `ρ(g⁻¹) ρ(u) v = ρ(g⁻¹ u g) ρ(g⁻¹) v`.
- `conjugationMap_surjective`: the map is surjective, with preimage `[ρ(g) v]`.
- `finite_coinvariants_of_conj`: if `V_(U,θ)` is a finite `R`-module, so is `V_(U,η)`.

For diagonal matrices over a field:

- `diagonalUnit_inv`: `(diagonalUnit d)⁻¹ = diagonalUnit d⁻¹`.
- `finite_coinvariants_of_diagonalConj`: take a complex representation `ρ` of `GL_m(F)`,
  characters `θ η` of `U_m`, and `d : Fin m → Fˣ` with `η u = θ (diagonalConj d u)` for
  all `u`. If `V_(U_m,θ)` is finite dimensional, so is `V_(U_m,η)`. This is the transport
  step for the BZ76 §5.6 conjugacy of nondegenerate characters (printed page 45).
