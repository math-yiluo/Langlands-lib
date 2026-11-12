# Weyl groups of standard Levi subgroups (Renard V.4.3.3 and V.4.8): statements

Module `Langlands.GroupScheme.Rational.StandardLeviWeylStatements`.
Namespace `Langlands.GroupScheme`. Universe parameter `u`.
The module contains two **statements**, the `Prop`-valued definitions
`StandardLeviNormalizerQuotientStatement` and `StandardMaximalLeviWeylStatement`. It proves
nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. The Chapter V item ledger found both assertions
unstated. The Library states only the finiteness of `N_G(M)(F)/M(F)`
(`LeviNormalizerFiniteQuotientStatement`) and a bound of at most two parabolics through a
maximal Levi (`MaximalLeviParabolicCountStatement`).

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read V.4.3–V.4.4 (printed p.119 / PDF p.125) and V.4.8 (printed p.122 /
PDF p.128) in the rendered PDF.

V.4.3. For a standard Levi subgroup `M` with split component `A`,
`W_M = N_M(A_∅)/Z_M(A_∅)` (V.4.3.1) embeds in `W_G`, `w · M = gMg⁻¹` for a lift `g` of `w`,
and `W(L, M) = {w ∈ W_G | w · L = M}` (V.4.3.2). Renard notes
`W(M, M) = (N_G(M) ∩ N_G(A_∅))/M_∅`, so that there is a well-defined map

> `W(M, M) → W(A) = N_G(A)/Z_G(A) = N_G(M)/M`

with kernel `W_M`, and concludes: « l'on vérifie immédiatement qu'elle est surjective car
les tores déployés maximaux sont conjugués dans `M`. Ainsi l'on obtient
(V.4.3.3) `W(M, M)/W_M ≃ W(A)`. »

V.4.4. `W(M, *) = ⋃_L W(M, L)` over the standard Levi subgroups `L`, and
`l(M) = |W(M, *)/W_M|`.

V.4.8. « On dit qu'un sous-groupe de Levi est maximal s'il est facteur de Levi d'un
sous-groupe parabolique maximal propre de `G`. Les sous-groupes de Levi maximaux standards
de `G` correspondent par la proposition V.4.2 aux parties de `Δ_∅` de la forme
`Θ = Δ_∅ ∖ {α}` […]. Il n'est pas difficile de voir en utilisant les considérations de la
section V.4.6 qu'un sous-groupe de Levi `M` est maximal si et seulement si `l(M) = 2` […].
Supposons `M` standard donné par la partie `Δ_∅ ∖ {α}`. Soit `w` un représentant de
l'élément non trivial de `W(M, *)/W_M` dans `G`. Alors si `P = MN` est le sous-groupe
parabolique standard contenant `M`, et si `P′` est le sous-groupe parabolique standard
contenant `M′ = w · M`, on a `w · P = P̄′`. »

The overline on `P̄′` is visible in the rendered page but lost in text extraction. Without
it the assertion fails: for `G = GL_2`, `M` the diagonal torus and `w = s`, `s · B` is the
lower triangular Borel subgroup.

## Setting and objects

`k` is a nonarchimedean local field, `G` a connected reductive group scheme over `k`,
`i : T.toGrp ⟶ G` a maximal split torus and `ν` a generic cocharacter. These are the setting
and objects of the published V.4.6 statement `StandardWeylMinimalRepresentativesStatement`:

| Renard | Lean |
| --- | --- |
| `W_G = N(k)/Z(k)` | `relativeWeylGroup i` |
| `M = L_I`, `P_I = L_I U_I` | `levi i ν I`, `parabolic i ν I` (rational points, `RationalPointFamily`) |
| `W_M` for `M = L_I` | `standardRelativeWeylGroup i ν (rootSet i ν I)`, the image of `L_I(k) ∩ N(k)` |
| `w · H` | `H.map (MulAut.conj n)` for a representative `n : normalizerPoints i` of `w` |
| `N_G(M)` | the `g ∈ G(k)` with `(levi i ν I).map (MulAut.conj g) = levi i ν I` |
| `Δ_∅ ∖ {α}` | an index set `I` with `b ∈ I ↔ b ≠ a` for all simple roots `b` |
| opposite `P̄_J` of `P_J` | `(Dynamic.parabolic (groupHom (-ζ) ≫ i)).carrier`, for a standard cocharacter `ζ` of `J` |

Here a standard cocharacter `ζ` of `J` (published `IsStandardCocharacter i ν (rootSet i ν J) ζ`)
vanishes on the roots of `J` and is positive on the other simple roots. The proved
`StandardCocharacterStatement` gives `P_J = P(ζ)` and `L_J = Z(ζ)` for every such `ζ` and
asserts that one exists. `P(-ζ)` is then the parabolic opposite to `P_J` with Levi factor
`L_J`.

## `StandardLeviNormalizerQuotientStatement` (V.4.3.3)

For every index set `I`:

1. a point `n ∈ N(k)` has class in `W_I` exactly when `n ∈ L_I(k)`;
2. every `g ∈ G(k)` with `g L_I(k) g⁻¹ = L_I(k)` has the form `g = n m` with `m ∈ L_I(k)`
   and `n ∈ N(k)` satisfying `n L_I(k) n⁻¹ = L_I(k)`.

The map of the source sends the class of `n` (a representative of an element of
`W(M, M)`) to the coset `n M(k)`. It is well defined because two representatives differ by
an element of `Z(k) ⊆ L_I(k)`. Clause 1 says that its kernel is `W_M`, and clause 2 that it
is surjective. Together they give the bijection `W(M, M)/W_M ≃ N_{G(k)}(M(k))/M(k)` of
(V.4.3.3).

## `StandardMaximalLeviWeylStatement` (V.4.8)

Inside the statement, `WLstar I` is `W(L_I, *)`: the classes having a representative `n`
with `n L_I(k) n⁻¹ = L_J(k)` for some `J`. `ell I` is `l(L_I)`: the number of left cosets
`w W_I` of elements of `WLstar I`. `IsMaximal I` says that `P_I(k) ≠ G(k)` and that every
standard `P_J(k)` strictly containing `P_I(k)` is `G(k)`. For every `I`:

1. `IsMaximal I` holds exactly when `I = Δ_∅ ∖ {a}` for some simple root `a`;
2. `IsMaximal I` holds exactly when `ell I = 2`;
3. if `IsMaximal I`, `n ∈ N(k)` has class outside `W_I`, and `n L_I(k) n⁻¹ = L_J(k)`, then
   `n P_I(k) n⁻¹ = P(-ζ)(k)` for every standard cocharacter `ζ` of `J`.

## Formalization choices

- **Rational points.** Conjugation and normalizers are taken on `G(k)`, as in the
  published V.4.6 and VI.5.4 statements. `N_G(M)` is read as the normalizer of `M(k)` in
  `G(k)`. Over the infinite field `k`, the points of the connected reductive `M` are Zariski
  dense in `M`, so this is the group `N_G(M)(k)` of the source.
- **Maximality.** Every parabolic subgroup containing `P_I` contains `P_∅`, so it is
  standard. Hence a standard Levi is the Levi factor of a maximal proper parabolic exactly
  when `P_I` is maximal among the proper standard parabolics. If some parabolic with Levi
  factor `M` is maximal, every parabolic with Levi factor `M` is maximal, since
  `dim 𝔞^G_M = 1`. Clauses 1 and 2 are stated for standard Levis only. Renard extends
  `l(M)` to nonstandard `M` by conjugation (V.4.4), and maximality is invariant under
  conjugation, so the nonstandard case adds nothing.
- **"The nontrivial element of `W(M, *)/W_M`."** For maximal `M` this quotient has two
  elements (clause 2). A representative of the nontrivial one is an `n` with
  `n L_I n⁻¹ = L_J` whose class is not in `W_I`, which is how clause 3 is stated.
- **The opposite parabolic.** Renard's `P̄′` is the opposite of `P_J` with respect to
  `M′ = L_J` (V.3.1). The statement writes it as `P(-ζ)` for every standard cocharacter `ζ` of
  `J`. One such `ζ` exists (`StandardCocharacterStatement`), so clause 3 is not vacuous.
- **Field.** The setting matches the published V.4.6 statement: a nonarchimedean local field.

## Why the statements are true

V.4.3.3. Clause 1: if `mk n = mk n'` with `n' ∈ L_I(k)`, then `n'⁻¹ n ∈ Z(k) = M_∅(k)`, which
lies in `L_I(k)`. Clause 2 is Renard's argument. `g A_∅ g⁻¹` is a maximal split torus of
`gL_Ig⁻¹ = L_I`. Maximal split tori of `L_I` are conjugate in `L_I(k)`, so some
`m ∈ L_I(k)` has `m g A_∅ g⁻¹ m⁻¹ = A_∅`. Then `n = mg` lies in `N(k)` and normalizes
`L_I(k)`, and `n⁻¹ g = g⁻¹ m⁻¹ g ∈ L_I(k)`.

V.4.8. Clause 1 follows from the classification of standard parabolics by subsets of
`Δ_∅`, which preserves inclusion (V.4.2; published `StandardParabolicClassificationStatement`
and `TitsStandardParabolicStatement`), with `P_{Δ_∅} = G`. For clause 2, `w W_M ↦ w⁻¹ · P_J`,
where `w · M = L_J`, is a bijection from `W(M, *)/W_M` onto the set `P(M)` of parabolics
with Levi factor `M`. Injectivity holds because conjugate standard parabolics are equal and
`P_J ∩ N_G(L_J) = L_J`. Surjectivity holds because every semistandard parabolic is
`W`-conjugate to a standard one. So `l(M) = |P(M)|`. This number is the number of chambers
cut out in `𝔞^G_M` by the restricted roots, which span its dual. It is 2 when
`dim 𝔞^G_M = 1`, that is when `M` is maximal, and at least 4 otherwise, except for `M = G`,
where it is 1. Clause 3: `n · P_I` has Levi factor `L_J`. By clause 2, `P(L_J)` is
`{P_J, P̄_J}`. If `n · P_I = P_J`, then `P_I = P_J` since conjugate standard parabolics are
equal. Then `n` normalizes `P_I` and `L_I`, so `n ∈ L_I(k)` and the class of `n` lies in
`W_I`, a contradiction. Hence `n · P_I = P̄_J = P(-ζ)`.

## Remaining obligations

Both proofs are separate obligations. They need conjugacy of maximal split tori in a
standard Levi, the published standard-parabolic classification and standard cocharacters,
self-normalization of parabolics (published `StandardParabolicPointsStatement`), and
opposite-parabolic uniqueness (`OppositeDynamicParabolicUniquenessStatement`).

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.GroupScheme.Rational.RelativeWeylCoxeterStatement` | `relativeWeylGroup`, `standardRelativeWeylGroup`, `normalizerPoints`, `IsStandardCocharacter`, `Dynamic.parabolic` (through its imports) |
| `Langlands.Representation.Aubert.General.RationalPointFamily` | `SimpleRoot`, `rootSet`, `parabolic`, `levi` |
