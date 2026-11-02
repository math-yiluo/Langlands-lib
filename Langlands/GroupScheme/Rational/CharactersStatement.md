# Split components and rational characters of connected reductive groups

Author: Worker 1122.

This module states five propositions about split components and rational
characters. It proves none of them. Each is a `Prop`-valued definition in the
namespace `Langlands.GroupScheme`. Each quantifies over every field
`k : Type u`, with base `S = Spec (CommRingCat.of k)`. The first four also
quantify over every `G : GroupScheme S` with the published
`IsConnectedReductive G`.

The objects come from
[`Langlands.GroupScheme.Rational.Characters`](Characters.md):
`rationalCharacters` (`X^*(G)_k`), `characterRestrict`, `IsSplitComponent`,
and the `GL_n` constructions `GeneralLinear.determinantCharacter`,
`GeneralLinear.scalarTorus` and `GeneralLinear.blockDeterminantCharacter`.
The published `IsMaximalSplitTorus` and `IsSplitSubtorus` are in
`Langlands.GroupScheme.Rational.SplitTorus`, `IsClosedSubgroup` and
`IsConnectedReductive` in `Langlands.GroupScheme.Reductive.Basic`,
`Dynamic.centralizer` in `Langlands.GroupScheme.Dynamic.Basic`,
`SubgroupFunctor.IsRepresentedBy` in `Langlands.GroupScheme.SubgroupFunctor`,
and `cocharacterLattice` in `Langlands.GroupScheme.Torus.Lattice`.

## Sources

- Renard, *Représentations des groupes réductifs p-adiques* (French version of
  9 July 2026), source ID `renard-2026-representations-groupes-reductifs-padiques`,
  SHA-256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
  Printed page = PDF page − 6.
  - V.2.1 (printed p.104, PDF p.110): « Si G est réductif, une composante
    déployée de G est alors un tore déployé maximal dans le centre de G. Comme
    deux tels tores doivent être conjugués par 𝑅(𝐺) qui est central, on en
    déduit l'unicité de la composante déployée pour un groupe réductif. »
  - V.2.2 (printed p.105, PDF p.111): « Le groupe 𝑅(G) ∩ 𝒟G étant fini,
    𝑋^∗(G) est un sous-réseau de rang maximal de 𝑋^∗(𝑅(G)). Le groupe des
    caractères rationnels 𝑋^∗(𝐺) de 𝐺 est un sous-réseau, pouvant être trivial,
    du réseau 𝑋^∗(G). »
  - V.2.6, Lemme and its proof (printed pp.107–108, PDF pp.113–114): « Nous
    affirmons que c'est une injection » for the restriction of `X^*(G)` to
    `X^*(A_G)`, and « le réseau 𝑋^∗(𝐺) = 𝑋^∗(𝐺′) est d'indice fini dans
    𝑋^∗(𝐴′_𝐺) et donc d'indice fini dans 𝑋^∗(𝐴_𝐺) ».
  - V.3.1 (printed p.110, PDF p.116): « Les sous-groupes de Levi 𝑀 de 𝐺 sont
    les centralisateurs de tores déployés 𝐴 dans 𝐺 tels que 𝐴 est la composante
    déployée de 𝑀. »
  - V.3.6 (printed p.111, PDF p.117): « On a 𝐴_𝐺 ⊂ 𝐴_𝑀 ⊂ 𝑀 ⊂ 𝐺, ce qui induit
    des morphismes donnés par la restriction des caractères », followed by the
    diagram `𝑋^∗(𝐺) → 𝑋^∗(𝑀) → 𝑋^∗(𝐴_𝑀) → 𝑋^∗(𝐴_𝐺)`.
- Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
  Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), source ID
  `waldspurger-2003-plancherel`, SHA-256
  `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
  Printed page = PDF page + 234.
  - I.1 (printed pp.238–239, PDF pp.4–5): « on note A_M le plus grand tore
    déployé dans le centre de M » and « Rat(G) ⊗_Z Q (≃ Rat(A_G) ⊗_Z Q ⊂ a*_G) ».

## The statements

### `SplitComponentStatement`

For every connected reductive `G`:

- there are `A : CommGroupScheme S` and `i : A.toGrp ⟶ G` with
  `IsSplitComponent i`;
- for any split components `i : A.toGrp ⟶ G` and `i' : A'.toGrp ⟶ G` there
  is an isomorphism `e : A.toGrp ≅ A'.toGrp` with `e.hom ≫ i' = i`.

The second clause is Renard's uniqueness (V.2.1) in the form "the same
subgroup of `G`": `i` and `i'` have the same image, through `e`.

### `RationalCharacterLatticeStatement`

For every connected reductive `G`, `rationalCharacters G` is a free and
finitely generated `ℤ`-module: `Module.Free ℤ (rationalCharacters G)` and
`Module.Finite ℤ (rationalCharacters G)`. The `ℤ`-module structure is the one
of the additive group. This is Renard V.2.2, where `X^*(G)_k` is a sublattice
of the lattice `X^*(G)`. The statement does not mention `X^*(G)` over `k̄` or
the radical; it states only the conclusion for `X^*(G)_k`.

### `CharacterRestrictionStatement`

For every connected reductive `G` and every split component
`i : A.toGrp ⟶ G`, restriction
`characterRestrict i : rationalCharacters G →+ rationalCharacters A.toGrp` is
injective (`Function.Injective`), and its range has finite index
(`(characterRestrict i).range.FiniteIndex`). This is the form proved in Renard
V.2.6. Waldspurger I.1 states the isomorphism
`Rat(G) ⊗ ℚ ≃ Rat(A_G) ⊗ ℚ`. For lattices of finite rank, that isomorphism is
equivalent to injectivity with finite index. This equivalence is a derived
reformulation and is not used here.

### `LeviSplitComponentStatement`

For every connected reductive `G`, every maximal split torus
`i : T.toGrp ⟶ G` (`IsMaximalSplitTorus i`), every cocharacter
`μ : cocharacterLattice T` (a homomorphism `Gm S ⟶ T`), and every
`j : M ⟶ G` with `IsClosedSubgroup j` that represents
`Dynamic.centralizer (CommGroupScheme.groupHom μ ≫ i)` in the sense of
`SubgroupFunctor.IsRepresentedBy`:

- `IsConnectedReductive M`;
- for every split component `iG : A_G.toGrp ⟶ G` of `G` there are a split
  component `iM : A_M.toGrp ⟶ M` of `M` and homomorphisms
  `f : A_G.toGrp ⟶ A_M.toGrp` and `g : A_M.toGrp ⟶ T.toGrp` with
  `f ≫ iM ≫ j = iG` and `g ≫ i = iM ≫ j`. So `A_G ⊆ A_M ⊆ M ⊆ G`, and
  `A_M ⊆ T`;
- with these maps, the restrictions compose as in Renard V.3.6:
  `(characterRestrict f).comp ((characterRestrict iM).comp (characterRestrict j))
  = characterRestrict iG`. This is the chain
  `X^*(G)_k → X^*(M)_k → X^*(A_M) → X^*(A_G)` of V.3.6, composed. It follows
  from `f ≫ iM ≫ j = iG` and the published `characterRestrict_comp`. It is
  included so that the statement records the chain of restriction maps.

`M` is the centralizer of the image of `μ` in `G`. The statement quantifies
over every closed subgroup representing this centralizer, so it does not
depend on a particular construction of the centralizer scheme. Renard V.3.1
describes the Levi subgroups as centralizers of split tori. Here the split
torus is the image of a cocharacter of a maximal split torus; the zero
cocharacter gives `M = G`. This dynamic description is a derived formulation.
The statement does not assert that every Levi subgroup in Renard's sense
arises this way.

### `GeneralLinearCharactersStatement`

For every field `k`, write `GL_n` for
`GeneralLinear.groupScheme (Fin n) (CommRingCat.of k)`. For every `n : ℕ`:

- every `χ : rationalCharacters GL_n` is `m • determinantCharacter` for some
  `m : ℤ`;
- if `n = 0`, every rational character of `GL_n` is `0`;
- if `1 ≤ n`, `m • determinantCharacter = 0` only for `m = 0`; with the first
  clause, `X^*(GL_n)_k` is free of rank one on the determinant;
- if `1 ≤ n`, `IsSplitComponent (scalarTorus (Fin n) (CommRingCat.of k))`;
- `characterRestrict scalarTorus determinantCharacter` is
  `n • Additive.ofMul (𝟙 (Gm S).toGrp)`, `n` times the identity character
  of `𝔾_m`. On points this says `det(t · 1) = t^n`.

For every `N : ℕ` and every block shape `B : Langlands.GeneralLinear.BlockShape N`,
there is a basis `b : Module.Basis (Fin B.length) ℤ` of the rational
characters of `GeneralLinear.blockLeviScheme (Fin N) (CommRingCat.of k)
(GeneralLinear.blockShapeWeight B)` with
`b i = blockDeterminantCharacter (CommRingCat.of k) B i` for every block `i`.

For `n = 0`, `GL_0` is the trivial group: its split component is the trivial
torus, and no homomorphism from `𝔾_m` to it is a closed immersion. So the
split-component clause is stated only for `1 ≤ n`. For `n = 0` the
restriction clause is `0 = 0`, because the determinant of the empty matrix is
`1`.

## Provenance

Renard and Waldspurger work over a non-archimedean local field `F`. These
statements quantify over every field `k`. This generality is derived: the
cited statements concern algebraic groups over `F` and characters defined over
`F`, not the topology of `F`, and they are stated here for every field. Nothing
here proves them. The `GL_n` statement is internal. It is the standard
computation of the characters and the split component of `GL_n` and of its
block Levi subgroups, which are products of general linear groups. The sources
use it without stating it as a proposition.
