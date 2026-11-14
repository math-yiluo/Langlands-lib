# Reduction of the real Langlands quotient statement

Worker 373 wrote this module for Task 6201 (`285d5eab-679b-4923-b5a6-c24fb384cd06`). The
task's target is the Library's `Langlands.Archimedean.RealLanglandsQuotientStatement` (module
`Langlands.Representation.Archimedean.RealGenericParameterReduction`). It says that every
irreducible admissible `(𝔤𝔩_n(ℝ), O(n))`-module `(ρ, π)` on a complex vector space `V`
receives a nonzero `(𝔤, K)`-intertwiner `B` (`IsRealStandardIntertwiner n ρ π ds B`) from the
`O(n)`-finite functions of the Library's standard module `realStandardModule n ds`, for some
list `ds` of real blocks with `realRank ds = n` in Langlands order (`IsRealLanglandsOrdered ds`).

This module splits the target into two statements and proves that together they imply it:

1. Casselman's subrepresentation theorem in quotient form: every such module is a quotient of
   the `O(n)`-finite principal series of some `n` characters of `ℝ^×`, in some order;
2. the Langlands classification starting from such a principal-series quotient.

No new predicate is introduced. The principal series of `n` characters is the Library's
standard module of the list of those characters, each read as a real block of rank one, and
the intertwiners are the Library's `IsRealStandardIntertwiner`. All declarations are in the
namespace `Langlands.Archimedean`. The Library's `RealBlock`, `realRank` and
`RealCharacterData` are in `Langlands.LocalFactor.Archimedean`.

## Principal series as standard modules

A `c : RealCharacterData` is the character `x ↦ sgn(x)^ε |x|^t` of `ℝ^×`, with
`ε = c.parity ∈ {0, 1}` and `t = c.exponent ∈ ℂ` (`c.character_eq`). Every continuous
character of `ℝ^×` has this form. For `cs : List RealCharacterData`, the list
`cs.map RealBlock.character` consists of blocks of rank one only. It has no induction block, so
`realInducedBlockAt` is `none` everywhere and `realStandardModule n (cs.map RealBlock.character)`
imposes no Fourier condition. It is the Library's smooth principal series
`principalSeries ℝ n (realPositionCharacter (cs.map RealBlock.character))`: the `C^∞` functions
`f` on `GL_n(ℝ)` with

`f(diag(a) u g) = ∏ᵢ cᵢ(aᵢ) |aᵢ|^((n-1)/2 - i) f(g)`

for `u` upper unipotent, where `cᵢ` is the `i`-th entry of `cs` for `i < cs.length`. The factor
`∏ᵢ |aᵢ|^((n-1)/2 - i)` is the square root of the modulus character of the upper triangular
Borel subgroup, so this is the normalized principal series, with `GL_n(ℝ)` acting by right
translation.

### `realRank_map_character (cs : List RealCharacterData)`

`realRank (cs.map RealBlock.character) = cs.length`. Every block `.character c` has rank one,
so the total rank is the number of entries. Proof by induction on `cs`, using
`realRank_cons` and `RealBlock.rank`. It shows that the principal series of
`RealPrincipalSeriesQuotientStatement` is the standard module of a list of real blocks of total
rank `n`.

## Statements

### `RealPrincipalSeriesQuotientStatement.{uV}`

For every `n : ℕ`, every complex vector space `V : Type uV` and every `ρ`, `π` with
`IsRealGKModule n ρ π`, `IsIrreducibleGKModule ρ π` and `IsAdmissibleGKModule ρ`, there are
`cs : List RealCharacterData` and `B` such that:

- `cs.length = n`;
- `B : kFiniteFunctions (realStandardModule n (cs.map RealBlock.character)) (unitaryCompact ℝ n) →ₗ[ℂ] V`
  with `B ≠ 0`;
- `IsRealStandardIntertwiner n ρ π (cs.map RealBlock.character) B`.

No order condition is imposed on `cs`. As in the target, `B` is onto because `V` is
irreducible, so `V` is a quotient of the `O(n)`-finite principal series.

Provenance (derived). The source is Casselman's subrepresentation theorem as stated by Wallach
1979 (`wallach-1979-representations-reductive-lie-groups`), Theorem 4.18, printed pp. 77–78
(PDF pp. 80–81 of the Corvallis Part I volume). It says that an irreducible admissible
`(𝔤, K)`-module `W` is isomorphic to a `(𝔤, K)`-submodule of `V(P₀, σ)` for an irreducible
representation `σ` of the minimal Levi subgroup `M₀`. Here `V(P₀, σ)` is the Harish-Chandra
module of Wallach's induced representation (4.8, p. 77): functions with
`f(kp) = δ_{P₀}(p)^{-1/2} σ(p)^{-1} f(k)` on which `G` acts by left translation. Wallach's
`G` includes `GL_n(ℝ)` (3.9, p. 75); for `GL_n(ℝ)` with the upper triangular minimal parabolic
subgroup, `M₀` is the diagonal torus, which is abelian, so `σ` is a character `diag(a) ↦ ∏ᵢ
σᵢ(aᵢ)` with characters `σᵢ` of `ℝ^×`.

The quotient form used here is derived from Theorem 4.18 as follows; this derivation is not in
the cited text.

- Under `F(g) = f(g⁻¹)`, Wallach's space becomes the space of `F` with
  `F(pg) = δ_{P₀}(p)^{1/2} σ(p) F(g)`, on which `G` acts by right translation. That is the
  Library's normalized principal series of the characters `σᵢ` described above.
- Apply Theorem 4.18 to the `K`-finite contragredient `W = Ṽ` of `V`, which is again
  irreducible and admissible, with `(Ṽ)~ ≅ V` by admissibility. This gives `Ṽ ↪ I(σ)`, so
  `I(σ)~ ↠ V` after taking `K`-finite contragredients.
- The pairing `⟨F₁, F₂⟩ = ∫_K F₁(k) F₂(k) dk` between `I(σ)` and `I(σ⁻¹)` is invariant,
  because `F₁F₂` transforms under `P₀` by `δ_{P₀}`, and it identifies `I(σ)~` with the
  `K`-finite part of `I(σ⁻¹)`. So `V` is a quotient of the `K`-finite principal series of the
  characters `cᵢ = σᵢ⁻¹`.

A proof must also identify the Library's algebraic `(𝔤, K)`-modules (`GKModule`) and
`realStandardModule` with the classical notions, as for the target (see
`RealGenericParameterReduction.md`).

### `RealLanglandsFromPrincipalSeriesStatement.{uV}`

For every `n : ℕ`, every complex vector space `V : Type uV`, every `ρ`, `π`, every
`cs : List RealCharacterData` and every
`B : kFiniteFunctions (realStandardModule n (cs.map RealBlock.character)) (unitaryCompact ℝ n) →ₗ[ℂ] V`,
assume:

- `IsRealGKModule n ρ π`, `IsIrreducibleGKModule ρ π` and `IsAdmissibleGKModule ρ`;
- `cs.length = n`;
- `B ≠ 0` and `IsRealStandardIntertwiner n ρ π (cs.map RealBlock.character) B`.

Then there are `ds : List RealBlock` and `B'` such that:

- `realRank ds = n` and `IsRealLanglandsOrdered ds`;
- `B' : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ] V` with
  `B' ≠ 0`;
- `IsRealStandardIntertwiner n ρ π ds B'`.

Provenance (source). The conclusion is exactly that of the target
`RealLanglandsQuotientStatement`, which is the existence half of the Langlands classification
of `GL_n(ℝ)` (Knapp 1994, `knapp-1994-archimedean-llc`, Theorem 1(a)–(b), p. 400, with the order
condition as corrected in `RealGenericParameterReduction.md`). For general groups in the
Harish-Chandra class it is Knapp–Vogan 1995 (`knapp-vogan-1995-cohomological-induction`),
Theorem 11.198(d), printed p. 741 (PDF p. 763): every irreducible admissible `(𝔤, K)`-module is
the unique irreducible quotient of a standard continuous-series representation, defined on
printed p. 739. The statement adds the hypothesis of the first statement: a nonzero intertwiner
from a principal series. This matches the classical route in Wallach 1979: Casselman's theorem
(4.18), then Lemma 5.13 and Lemma 5.15 (printed pp. 78–79) to move the embedding to a parabolic
subgroup whose exponents lie in a chamber, then Langlands' Theorem 6.7 and the classification
in 6.9 (printed pp. 79–80).

The hypothesis does not make the statement a reordering of `cs`. On `GL₂(ℝ)`, the discrete
series `D` with lowest `O(2)`-type of weight 2 and trivial central character on positive
scalars is a quotient of `Ind(|·|^{-1/2}, |·|^{1/2})`, whose list is not Langlands ordered. In
the reordered principal series `Ind(|·|^{1/2}, |·|^{-1/2})` it is a subrepresentation, with the
trivial representation as the unique irreducible quotient. So the conclusion needs the induction
block of weight `1` and exponent `0`, whose position characters are `|·|^{1/2}` and
`|·|^{-1/2}`. Its standard module is cut out of `Ind(|·|^{1/2}, |·|^{-1/2})` by the vanishing of
the Fourier coefficient of weight `0` along the rotations, and its `O(2)`-finite part is the
Harish-Chandra module of `D`.

### `RealLanglandsQuotientReductionStatement.{uV}`

`RealPrincipalSeriesQuotientStatement.{uV} → RealLanglandsFromPrincipalSeriesStatement.{uV} →
RealLanglandsQuotientStatement.{uV}`.

Provenance: internal; the reduction is proved in the module.

## Proofs

- `realRank_map_character`: induction on `cs`; the step rewrites with `List.map_cons`,
  `realRank_cons`, the induction hypothesis and `List.length_cons`, unfolds `RealBlock.rank` of
  a character block to `1`, and closes with `omega`.
- `realLanglandsQuotientReduction` proves the reduction statement. Given an irreducible
  admissible `(ρ, π)`, `RealPrincipalSeriesQuotientStatement` gives `cs` with
  `cs.length = n` and a nonzero intertwiner `B` from the principal series.
  `RealLanglandsFromPrincipalSeriesStatement`, applied to these data, returns the `ds`, rank
  equation, order condition and nonzero intertwiner that the target asks for.
