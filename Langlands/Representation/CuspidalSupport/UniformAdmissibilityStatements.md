# Uniform admissibility and uniform support (Renard VI.2.3–VI.2.4): statements

Module `Langlands.Representation.CuspidalSupport.UniformAdmissibilityStatements`.
Namespace `Langlands.CuspidalSupport`. Universe parameters `u, v`.
The module contains four **statements**, all `Prop`-valued definitions; it proves
nothing:

- `RationalPointsUniformAdmissibilityStatement` (VI.2.3, Theorem);
- `RationalNormKernelUniformAdmissibilityStatement` (VI.2.3, Remark);
- `SupercuspidalUniformCoefficientSupportStatement` (VI.2.4, Proposition);
- `UniformAdmissibilityStatements`, their conjunction.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read VI.2.2–VI.2.4, printed pp.140–142 / PDF pp.146–148:

> **Théorème.** Soit `K` un sous-groupe compact ouvert de `G`. Il existe une
> constante positive `c = c(G, K)` telle que pour toute représentation lisse
> irréductible `(π, V)` de `G`, `dim V^K ≤ c`. (VI.2.3, printed p.140)
>
> *Remarque.* Un résultat analogue est vrai pour les représentations lisses
> irréductibles du groupe `⁰G`. (VI.2.3, printed p.141)
>
> **Proposition.** Etant donné un sous-groupe ouvert compact `K` de `G`, il existe
> une partie ouverte compacte modulo le centre `Ω` dans `G` telle que pour toute
> représentation supercuspidale irréductible `(ρ, W)` de `G`, pour tout `v ∈ W^K`,
> le support de `g ↦ ρ(a_{g,K}) · v` soit inclus dans `Ω`. (VI.2.4, printed p.141)

The Library uses these results as inputs, but before this unit no declaration
stated them. `UniformFixedLevelBounds` and `FixedLevelSandwich` are internal
supporting constructions for the dimension argument. The published
`RationalNormKernelUniformSupportStatement` is a derived norm-kernel form used in
VI.3.4.

## The statements

**VI.2.3, Theorem.** For every nonarchimedean local field `F` and connected
reductive `G`, with the canonical topology `rationalPointTopology F G.X` on
`G(F)`, and every compact open subgroup `K` of `G(F)`, there is `c : ℕ` such that
`Module.rank ℂ (fixedVectors A.representation K) ≤ c` for every irreducible
`A : SmoothRep ℂ G(F)`. The bound is on the `ℂ`-rank (a cardinal) of the actual
subspace of `K`-fixed vectors, so it also asserts that this subspace is
finite-dimensional.

**VI.2.3, Remark.** The same for the common norm kernel
`⁰G = Plancherel.rationalCommonNormKernel G` with its subspace topology: for every
compact open subgroup `K` of `⁰G` there is `c : ℕ` bounding the rank of `σ^K` for
every irreducible smooth representation `σ` of `⁰G`. Since `⁰G` is open in `G(F)`
and contains every compact subgroup, these `K` are exactly the compact open
subgroups of `G(F)`.

**VI.2.4, Proposition.** In the represented-parabolic setting of the published
VI.10.4 statements (field `k` with `T2Space`, canonical topology
`RationalPointFamily.pointTopology`, `LocallyCompactSpace` and
`NonarchimedeanGroup` binders), for every compact open subgroup `K` there is an
open `Ω ⊆ G(F)` with `Ω ⊆ C · Z` for a compact `C`, where `Z` is the centre of
`G(F)`. For every irreducible `A` satisfying
`Aubert.General.RepresentedParabolic.IsSupercuspidal`, every `w ∈ A^K`, and every
linear form `ℓ` on `A` invariant under `K`, the support of `g ↦ ℓ(A(g) w)` lies in
`Ω`.

## Formalization choices

- **The function `g ↦ ρ(a_{g,K}) v`.** For `v ∈ W^K`,
  `ρ(a_{g,K}) v = ρ(e_K) ρ(g) ρ(e_K) v = ρ(e_K) ρ(g) v`. A `K`-invariant linear
  form satisfies `ℓ ∘ ρ(e_K) = ℓ`. Conversely, every linear form on `W^K`
  extends through the projector `ρ(e_K)` to a `K`-invariant form. So
  `ρ(e_K) ρ(g) v ≠ 0` iff `ℓ(ρ(g) v) ≠ 0` for some `K`-invariant `ℓ`. The support
  of Renard's function is therefore the union of the supports of these
  coefficients. The statement uses this form, as the published
  `CompactCoefficientClass.HasUniformFixedLevelCoefficientSupport` does. It
  avoids the Hecke algebra and its measure normalization.
- **Compact modulo the centre** is `Ω ⊆ C · Z(G(F))` for a compact `C`. Here
  `Z(G(F))` is `Subgroup.center` of the group of rational points, as in the
  published `RepresentedSupercuspidalCentralProjectivityStatement`. For
  connected reductive `G` it equals `Z(G)(F)`, since `G(F)` is Zariski dense
  (unirationality); that comparison is not used or proved here.
- **Supercuspidality** is the published represented predicate: every normalized
  Jacquet module along a proper actual rational parabolic vanishes (VI.2.1,
  definition).
- **Constants.** Renard's `c` is positive; `∃ c : ℕ` is equivalent (replace `c`
  by `c + 1`). The constant depends on `G`, `K` and the fixed carrier universe
  `v`.
- **Binders.** VI.2.3 uses the binders of the published
  `RationalPointsIrreducibleAdmissibleStatement` (VI.2.2), written with
  `GroupScheme.rationalPoints G`. VI.2.4 uses the binders of the published VI.10.4
  statements. No Chapter V structural input is a hypothesis: Renard's proofs use
  V.5.1, V.5.3 and C.I, and those are proof obligations.

## Why the statements are true

VI.2.3: by III.1.5 the claim is a uniform bound on the dimension of simple
`H(G, K)`-modules. Renard bounds it by Burnside's theorem, the decomposition
`H(G, K) = ∑_j H₀ A D_j H₀` (published V.5.3 statement) and Lemma C.I on
commutative subalgebras, getting `c = (h² q)^{2^{d-1}}`. The `⁰G` case follows
from the `G` case through compact induction and Frobenius reciprocity: an
irreducible `σ` of `⁰G` embeds in the restriction of an irreducible quotient of
`ind_{⁰G}^G σ`. VI.2.4: uniform admissibility gives `N` with `dim W^K ≤ N`; the
Cartan decomposition (V.5.1) and the decomposition of V.5.3 then confine the
support to finitely many `K₀ E_j z K₀` modulo `Z(G)` (printed pp.141–142).

## Source issue

Renard's proof of VI.2.3 uses the identification `C_∅^+/C_{A_G} ≅ ℕ^d` of V.3.24,
which is false in general (published V.5.3 statement, "Source issue"). The
argument still works with a finitely generated cone monoid in place of `ℕ^d`.
The statements here do not depend on that identification.

## Remaining obligations

The proofs are separate obligations.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Plancherel.RationalCharacterValuation` | `Plancherel.rationalCommonNormKernel` |
| `Langlands.Representation.Exponents.LeviSupercuspidalInductionSupport` | `Aubert.General.RepresentedParabolic.IsSupercuspidal`, the represented point topology |
| `Langlands.GroupScheme.Reductive.Basic` | `IsConnectedReductive` |
