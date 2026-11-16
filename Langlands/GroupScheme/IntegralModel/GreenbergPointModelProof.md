# Greenberg point models at every positive congruence level

`Langlands.GroupScheme.IntegralModel.greenbergPointModel` proves the Library
statement `GreenbergPointModelStatement.{u}` at arbitrary universe `u`.
For every discrete valuation ring `R : Type u` with algebraically closed
residue field `k`, every positive level `n` and every smooth affine group
scheme `X` over `Spec R`, it gives a smooth affine group `G` over `k` and a
group isomorphism `X(R/𝔪ⁿ) ≃* G(k)`.

The model `G` and its point isomorphism are fixed before any source.
For every smooth affine group `Z` over `R` and homomorphism `h : Z ⟶ X`,
the theorem supplies a smooth affine group `GZ` over `k`, a group
isomorphism `Z(R/𝔪ⁿ) ≃* GZ(k)` and a group-scheme homomorphism `GZ ⟶ G`
that commutes with `h` on congruence-level points. If `Z` is geometrically
connected over `R`, then `GZ` is geometrically connected over `k`.

The implemented proof applies
`greenbergPointModel_of_characteristicCases` from
`GreenbergPointModelCases.lean` to two Library theorems:

- `equalCharacteristicGreenbergPointModel` from
  `EqualCharacteristicGreenbergProof.lean` proves the case
  `ringChar R = ringChar k` using a coefficient field in `R/𝔪ⁿ` and
  affine Weil restriction.
- `mixedCharacteristicGreenbergPointModel` from
  `MixedCharacteristicGreenbergPointModelProof.lean` proves the case
  `ringChar R ≠ ringChar k` using Witt-vector coefficient ring schemes
  and the affine Greenberg construction.

The reduction decides this characteristic equality and applies the
corresponding complete case theorem. Both cases have the exact
`HasGreenbergPointModel` conclusion, so the reduction preserves the fixed
target, all source homomorphisms and the geometric-connectedness implication.
Their paired Markdown explains the underlying constructions.

The source context is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`,
Theorem A.4.19, its preceding paragraph and Definition A.4.20, printed
pp.628–629 / PDF pp.659–660. This theorem proves the point-model consequence
specified in `GreenbergPointModel.md`. The registered
`kaletha-prasad-2024-corrections`, PDF p.49, requires a perfect residue
field; the algebraically closed residue field in the statement satisfies
that requirement. The final assembly is an internal logical deduction
from the two characteristic-case proofs.
