# Highly ramified L-vanishing against a character of `GL_1`, every local field

Module `Langlands.AllField.Representation.RankinSelberg.WhittakerTypeHighlyRamifiedRankOneStatement`.
It states one proposition and proves nothing:
`Langlands.AllField.RankinSelberg.WhittakerTypeHighlyRamifiedRankOneLVanishingStatement.{uF,uV,uW}`.

## The statement

The proposition quantifies over:

- a field `F` with instances `[TopologicalSpace F] [ValuativeRel F]
  [IsNonarchimedeanLocalField F]`, so `F` is any nonarchimedean local field, of any
  characteristic;
- a unitary additive character `ψ` and a self-dual Haar measure
  `ν : AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ`.
  Here `⟨⟩ : LocalFieldData F` is the local-field data assembled from the instances,
  definitionally `LocalFieldData.ofInstances F`;
- a rank `t : ℕ`;
- a representation `π` of `GL_(0+1)(F)` on a complex vector space `V` (universe `uV`)
  and a representation `σ` of `GL_(t+1)(F)` on `W` (universe `uW`). Both are of
  Whittaker type for the standard character: `IsOfWhittakerType 0 (standardCharacter ψ 0) π`
  and `IsOfWhittakerType t (standardCharacter ψ t) σ`. Reducible representations are
  allowed.

Its conclusion: there is a bound `A : ℕ` such that every continuous quasicharacter
`χ : Quasicharacter F` with multiplicative conductor at least `A`
(`A ≤ (⟨⟩ : LocalFieldData F).multiplicativeConductor χ`) satisfies

```text
IsPadicSymmetricLPolynomial F ψ ν.val (twist (χ ∘ det) π) σ 1,
```

that is, `L(s, (π ⊗ (χ ∘ det)) × σ) = 1`. `IsPadicSymmetricLPolynomial` is the
all-field symmetric L-polynomial relation of
`Langlands.AllField.Representation.RankinSelberg.PadicPairFactors`. It takes the
larger rank first, requires that a compatible quotient measure exists, and requires
the relation for every compatible quotient measure. The bound `A` is chosen before
`χ`, so it is uniform over all such `χ`, including their unramified parts.

## Source

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg Convolutions*,
Amer. J. Math. 105 (1983), registered as `jpss-1983-rankin-selberg`
(`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`),
Proposition (2.13), printed page 404 (PDF page 39, counting the cover as page 1):
for representations `π` of `G_r` and `σ` of `G_t` of Whittaker type (Section 2),
`L(s, (π ⊗ μ) × σ) = 1`, "provided the conductor of `μ` is sufficiently large".
Here `π ⊗ μ` is the twist by `μ ∘ det`. Section 0.3 (printed page 375) allows any
nonarchimedean local field.

This proposition is the case `r = 1` of (2.13) in the source's numbering of ranks
(here `π` is a representation of `GL_(0+1)`), with `χ` in place of `μ`. The bound
`A` on the conductor is the formal reading of "sufficiently large". Section 2.1
defines Whittaker type, and Section 2.12 (printed page 403) gives the convention for
pairs with the smaller rank first, which the symmetric relation encodes.

## Provenance and relation to the full proposition

The full proposition (2.13), for all ranks, is formalized over every local field as
`Langlands.AllField.RankinSelberg.WhittakerTypeHighlyRamifiedLVanishingStatement`
(module `Langlands.AllField.Representation.RankinSelberg.WhittakerTypeHighlyRamifiedStatement`,
the all-field port of the Library's p-adic
`Langlands.RankinSelberg.WhittakerTypeHighlyRamifiedLVanishingStatement`). The body
of `WhittakerTypeHighlyRamifiedRankOneLVanishingStatement` is the body of that
proposition with the rank variable `r` replaced by `0` and its binder removed. Hence
the full proposition implies this one by taking `r = 0`.

The rank-one case is stated separately for the following reason. The Library proves
the p-adic proposition (`Langlands.RankinSelberg.whittakerTypeHighlyRamifiedLVanishing`)
along the finite-function route of the source's proof. In the root coordinates used
there, the determinant twist contributes the character power `χ^i` to the `i`-th
coordinate, for `i = 1, …, k` with `k` the smaller rank, and the argument needs each
such power to be nontrivial on a principal-unit group of a fixed level. If `F` has
characteristic `p` and `p` divides `i`, the `i`-th powers of a principal-unit group
contain no principal-unit group, and there are characters of arbitrarily large
conductor with `χ^i` trivial on that group (so the all-field analogue of the
Library's p-adic `Langlands.HarmonicAnalysis.PrincipalUnitPowerCofinalityStatement`
is false). A large conductor of `χ` thus does not control `χ^i`. That route
therefore does not give the full proposition in positive characteristic. When the
smaller member of the pair has rank one, only `χ^1` occurs, and the route works in
every characteristic (see
[WhittakerTypeHighlyRamifiedRankOneProof](WhittakerTypeHighlyRamifiedRankOneProof.md)).
This is a statement about the proof route only; this module asserts nothing about the
full proposition in positive characteristic.

The L-factor descent of JPSS Section 7, as implemented in
[TwoBlockLConditionalAssembly](TwoBlockLConditionalAssembly.md), uses (2.13) only
with first member `rankOneCharacter 1`, a representation of `GL_1`. Its
high-ramification hypothesis therefore takes this rank-one proposition.
