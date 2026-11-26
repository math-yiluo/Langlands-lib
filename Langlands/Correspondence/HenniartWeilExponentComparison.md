# The Artin and Swan exponents of Weil representations against Henniart's numerical relations

The numerical route of Henniart's correspondence uses the relation
`Henniart.Numerical.HasArtinConductor K σ a` (`HenniartNumericalStatement`: some representative of
`σ` has a finite inertia presentation with Artin expression `a`) and the natural number
`Henniart.Numerical.weilSwanExponent K σ` (`HenniartWeilSwanBreak`: a natural Artin conductor
chosen by `Classical.choose` from `weilArtinConductorExistence`, minus the rank). This module
identifies both with the exponents of `Weil.Local.artinExponent` and `Weil.Local.swanExponent`
(`LocalFactor/Ramification/WeilExponent`) of a representative.

## Statements

Name space `Langlands.Henniart.Numerical`; `K : PadicField.{uK} p`,
`σ : IrreducibleWeilClass.{uK, uW} K k.succPNat` (a continuous irreducible class of rank `k + 1`),
`A : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K)` with
`hA : FiniteRepresentation.classOf A = weilClassForget K σ` (a representative).

```lean
theorem hasArtinConductor_iff_artinExponent_eq (hA) (a : ℕ) :
    HasArtinConductor K σ a ↔ artinExponent K A = a
theorem hasArtinConductor_artinExponent (hA) : HasArtinConductor K σ (artinExponent K A)
theorem weilSwanExponent_eq_artinExponent_sub (hA) :
    weilSwanExponent K σ = artinExponent K A - (k + 1)
theorem weilSwanExponent_eq_swanExponent (hA) : weilSwanExponent K σ = swanExponent K A
theorem hasWeilSwan_iff_swanExponent_eq (hA) (s : ℕ) :
    HasWeilSwan K σ s ↔ swanExponent K A = s
```

(each with the implicit binders `{p : ℕ} [Fact p.Prime] (K) {k : ℕ} {σ} {A}`).

So the relation `HasArtinConductor K σ` holds for exactly one natural number, the Artin exponent
of any representative, and the chosen `weilSwanExponent K σ` is the Swan exponent of any
representative.

## Proofs

- `hasArtinConductor_iff_artinExponent_eq`. By `hasArtinConductor_iff_exists_padicPresentation`
  (`HenniartPadicArtinTransport`) the relation is witnessed by p-adic finite inertia
  presentations. If `B`, such a presentation `P` and `a` witness the relation, `A` and `B` are equivalent (same class), so `artinExponent K A = artinExponent K B`
  (`artinExponent_eq_of_equiv`), which is `P.artinConductor hP = a` (`artinExponent_eq`).
  Conversely, `A` is continuous (`weilRepresentative_continuous_irreducible`), so it has a
  presentation computing its exponent (`exists_presentation_of_isContinuous`), which witnesses the
  relation.
- `weilSwanExponent_eq_artinExponent_sub`: the chosen conductor satisfies the relation
  (`Classical.choose_spec`), hence is the Artin exponent.
- `weilSwanExponent_eq_swanExponent`: for an irreducible continuous `A` of rank `k + 1` with a
  presentation `P`, the Library's `irreducible_artin_sub_rank_eq_rank_mul_lastBreak` gives
  `a − (k + 1) = (k + 1) · t` and `irreducible_presentation_swan_eq_rank_mul_lastBreak` gives
  `sw = (k + 1) · t` (as real numbers, `t` the last upper break of `A`); so
  `artinExponent − (k + 1) = swanExponent`.
- `hasWeilSwan_iff_swanExponent_eq`: `HasWeilSwan K σ s` is `∃ a, HasArtinConductor K σ a ∧
  a − (k + 1) = s`; by the first theorem `a` is the Artin exponent.

## Literature

Deligne, *Les constantes des équations fonctionnelles des fonctions L*, LNM 349 (1973), §4.5,
printed pp. 537–538, (4.5.4): `a(V) = sw(V) + dim V − dim V^I`; for an irreducible `V` on which
inertia acts non-trivially `V^I = 0`, so `sw(V) = a(V) − dim V`, which is the normalization of
`weilSwanExponent`. Henniart's numerical correspondence, for which these relations were introduced,
is cited in `HenniartNumericalStatement.md`.
