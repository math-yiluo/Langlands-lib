# The centre of `M(G)_Ω` is the algebra of functions on `Ω`: statements

Module `Langlands.Representation.CuspidalSupport.BernsteinCenterFunctionsStatements`.
Namespace `Langlands.CuspidalSupport`. Universe parameters `uF, uV`.
The module contains four **statements**, all `Prop`-valued definitions; it
proves nothing:

- `BernsteinBlockCenterFunctionsStatement`: the Theorem of VI.10.4, first
  sentence, with Remark 1;
- `BernsteinCenterFunctionsStatement`: the Theorem of VI.10.4, second
  sentence, with Remark 1;
- `BernsteinCentralIdempotentFunctionStatement`: Remark 2 after the Theorem;
- `BernsteinCenterFunctionsStatements`: their conjunction.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read VI.10.4, printed pp.209–212 / PDF pp.215–218. The Theorem
and the Remarks are on printed p.212 / PDF p.218:

> **Théorème.** Soit `Ω` une composante connexe de la variété `Ω(G)`. Alors le
> centre de la catégorie `M(G)_Ω` est isomorphe à l'algèbre des fonctions
> polynomiales sur la variété `Ω`. De même, le centre `ℨ(G)` de la catégorie
> `M(G)`, produit des `ℨ_Ω`, s'identifie à l'algèbre des fonctions
> polynomiales sur `Ω(G)`.
>
> *Démonstration.* […] la variété `Ω` est le quotient de la variété `D` sous
> l'action du groupe `W(D)` (voir VI.7.1). Or l'algèbre des fonctions
> polynomiales sur `D` est isomorphe à `ℨ_D`, et donc `O(Ω) ≃ ℨ_D^{W(D)}`. Or
> `ℨ_D^{W(D)} ≃ ℨ_Ω`. […]
>
> **Remarques.** 1. […] la valeur en un point `(M, (ρ, W))_G` de `Ω(G)` de la
> fonction `z ∈ ℨ(G)` est le scalaire par lequel `z` agit sur `i_P^G(ρ, W)`,
> où `P` est un sous-groupe parabolique de `G` de facteur de Levi `M`.
> — 2. Les idempotents centraux `e_Ω` de VI.7.4 sont les fonctions
> caractéristiques des composantes connexes `Ω` de `Ω(G)`.

The Corollary and Remark 3 are the published
`BernsteinBlockCenterStatements` (Worker 6), whose Markdown records the
Theorem as not stated. The earlier steps of VI.10.4 are the published
`InducedProgeneratorEndFreeStatement` and
`InducedProgeneratorCenterInclusionStatement` (Worker 6); their Markdown also
lists the Theorem as not stated.

The provenance is source: the statements are the Theorem and Remarks 1–2, in
the formal reading described below.

## Framework and published objects

All objects are published; this file constructs nothing. The setting is the
standard-family framework of Worker 1153 (modules `BernsteinData`,
`BernsteinBlock`, `BernsteinSupportComparison`), with the same binders as
`BernsteinBlockCenterStatements`.

- `F`, `G`, `T`, `i`, `ν`, `family : BernsteinStandardFamily i ν`: a
  nonarchimedean local field, a group scheme with locally compact
  nonarchimedean `G(F)`, and the structural hypotheses on the standard
  subgroups.
- A cuspidal datum `a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family` is a
  standard Levi `M_a = bernsteinLeviScheme i ν a.roots` with an irreducible
  cuspidal representation `ρ_a = a.representation` (carrier in
  `Type (max uF uV)`). Every cuspidal datum is associated to such an `a`.
- `M(G)_Ω` is the published `BernsteinSaturatedBlock i ν family
  (bernsteinInertialClass i ν family a)`: the full subcategory of smooth
  representations (carriers in `Type (max uF uV)`) all of whose irreducible
  subquotients occur in the induction of a datum inertially equivalent to `a`
  (`bernsteinSaturatedBlockProperty`). `M(G)` is
  `SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)`.
- The centre of a category is Mathlib's `CatCenter C = End (𝟭 C)`, as in the
  published VI.4.5 and VI.10.4 statements; `z.app V` is the component at `V`
  and `SmoothRep.hom` its underlying intertwiner.
- `X(M_a)` is `unramifiedCharacters (fun χ => (rationalNormCharacters M_a
  χ).toMul)`, `ρ ⊗ ω` is `rationalUnramifiedTwist`, and `ℂ[X(M_a)]` is the
  published `unramifiedRegularFunctions`, the coordinate algebra of the
  complex torus `X(M_a)`.
- `ind_a ω = i_{P_a}^G(ρ_a ⊗ ω)` is the published `normalizedInductionFunctor`
  of the standard parabolic `P_a` of `a.roots`, applied to `ρ_a ⊗ ω`
  transported by `bernsteinLiteralLeviRep`; for `ω = 1` this is
  `bernsteinInduction a`.
- Association of `(M_a, ρ_a ⊗ ω)` and `(M_b, ρ_b ⊗ ω')` is an actual
  `RationalLeviConjugacy` `c` of the Levi subgroups with
  `ρ_a ⊗ ω ≅ rationalIsoPullback c.iso (ρ_b ⊗ ω')`, the relation of the
  published `AreBernsteinCuspidalDataAssociated`.

## Functions on `Ω` and on `Ω(G)`

The component `Ω` of `a` is the image of `X(M_a) → Ω(G)`,
`ω ↦ (M_a, ρ_a ⊗ ω)_G`; two characters have the same image exactly when the
twisted data are associated. Its polynomial functions are the elements of
`ℂ[X(M_a)]` constant on the association classes. This is the encoding of the
statement unit for the VI.7.1 Theorem (`BernsteinComponentVarietyStatement`,
candidate `64e71122-0633-4798-a645-a27268500947`), which states that these
functions form the finitely generated coordinate algebra of `X(M_a)/W` and
that they do not depend on the representative `a`. This module does not
import that unit; it repeats the definition inline.

A function on `Ω(G)` that is polynomial on every component is a family `f`
indexed by all data `a`, with `f a` a complex function on the characters
`M_a(F) →* ℂˣ` read on `X(M_a)` (through `ω ↦ f a ω.val.toMonoidHom`), such
that each `ω ↦ f a ω` lies in `ℂ[X(M_a)]` and `f a ω = f b ω'` whenever
`(M_a, ρ_a ⊗ ω)` and `(M_b, ρ_b ⊗ ω')` are associated. Values off `X(M_a)` are
irrelevant. Using all characters of `M_a(F)` as domain avoids a dependent
family of topological types in the binder.

## The statements

**`BernsteinBlockCenterFunctionsStatement`.** For every datum `a`, with
`X = X(M_a)`, `ind ω = ind_a ω`, `Assoc` the association of twists of `a`, and
`invariant` the elements of `ℂ[X]` constant on its classes:

1. every `ind ω` lies in `M(G)_Ω`;
2. there are a subalgebra `O` of `X → ℂ` with underlying set `invariant` and a
   ring isomorphism `e : CatCenter(M(G)_Ω) ≃+* O` such that every `z` acts on
   every `ind ω` by the scalar `e z ω`.

So `ℨ_Ω ≅ O(Ω)`, and the value of `e z` at `(M, ρ ⊗ ω)_G` is the scalar by
which `z` acts on `i_P^G(ρ ⊗ ω)` (Remark 1). The scalar condition determines
`e`.

**`BernsteinCenterFunctionsStatement`.** Writing "`z` acts by `f`" for: `z`
acts on every `ind_a ω` by the scalar `f a ω`:

1. every `z ∈ CatCenter(M(G))` acts by some function `f` on `Ω(G)`
   polynomial on every component (as above);
2. two elements of the centre that agree on every `ind_a ω` are equal;
3. every function `f` on `Ω(G)` polynomial on every component is the action
   of some `z`.

The map `z ↦ f` is a ring homomorphism (components of sums and composites),
well defined by 1, injective by 2 and surjective by 3: it is the
identification of `ℨ(G)` with the polynomial functions on `Ω(G)`, with
Remark 1 as its defining property. "Polynomial functions on `Ω(G)`" is read
as the functions polynomial on every connected component, which for the
disjoint union `Ω(G) = ⨆ Ω` is the product `∏ O(Ω)` of the source.

**`BernsteinCentralIdempotentFunctionStatement`.** For every inertial class
`s` and every `z ∈ CatCenter(M(G))`: `z` is the identity on every object of
`M(G)_s` and zero on every object of every other block (the defining property
of `e_s` in the published VI.7.4 statement `BernsteinCentralIdempotentStatement`)
exactly when `z` acts on every `ind_a ω` by `1` if `a` lies in `s` and by `0`
otherwise. That is, `e_Ω` corresponds to the characteristic function of `Ω`.

## Why the statements are true

- `ind_a ω` is the induction of the datum `(M_a, ρ_a ⊗ ω)` (twists preserve
  irreducibility and cuspidality), which is inertially equivalent to `a`.
- Renard's proof: `ℨ_Ω ≅ ℨ_D^{W(D)}` (VI.10.4, using the published
  `InducedProgeneratorEndFreeStatement` and
  `InducedProgeneratorCenterInclusionStatement`), `ℨ_D` is the algebra of
  polynomial functions on `D = Irr(M)_D ≅ X(M)/X(M)(ρ)` (VI.4.4–VI.4.5), and
  `W(D)`-invariance on `D` is association of twists. Each `z ∈ ℨ_Ω ⊂ ℨ_D`
  acts on `i_P^G(Π_D / I Π_D) ≅ m · i_P^G(σ_I)` by `Ψ_I(z)`, hence on every
  `i_P^G(σ)`, `σ ∈ D`, by a scalar, even when it is reducible.
- The second sentence follows from the first and the Bernstein decomposition
  (VI.7.2): `ℨ(G) = ∏ ℨ_Ω`; scalars of associated data agree because their
  inductions have the same irreducible subquotients (VI.5.4); and every twist
  of an inertially equivalent datum is associated to a twist of `a`.
- Remark 2: `e_s` acts by the characteristic function, and by item 2 of the
  second statement an element of the centre is determined by its scalars.

## Formal choices and scope

- **Standard data and blocks.** As in the framework; blocks are defined with
  the induction-occurrence support relation, whose comparison with Renard's
  `M(G)_Ω` is recorded in `BernsteinBlock`.
- **Variety of `Ω`.** The coordinate algebra `O(Ω)` is written inline as the
  association-invariant elements of `ℂ[X(M_a)]`; its identification with the
  regular functions of the variety `X(M_a)/W` is the VI.7.1 statement unit
  named above, not repeated here.
- **The centre of `M(G)`.** Stated by the three properties of `z ↦ f` rather
  than by constructing the ring of functions on `Ω(G)`.
- **Carriers.** All representations have carriers in `Type (max uF uV)`, the
  universe of the normalized inductions.
- **Not stated.** The intermediate results `ℨ_Ω ⊂ ℨ_D^{W(D)}`,
  `ℨ_Ω = ℨ_D^{W(D)}`, the centralizer lemma for bimodules with a filtration,
  and the equivalence of (VI.10.4.1) with `i_P^G` through (VI.10.4.2).

## Remaining obligations

The proofs are separate obligations. They need the VI.10.4 lemmas (published
statements), the VI.4.4–VI.4.5 description of `ℨ_D`, the Bernstein
decomposition (VI.7.2) and VI.7.4 idempotents, and the association invariance
of supports (VI.5.4).

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.CuspidalSupport.BernsteinSupportComparison` | the framework (`BernsteinStandardFamily`, `BernsteinCuspidalDatum`, `bernsteinLeviScheme`, `bernsteinLiteralLeviRep`, `bernsteinInertialClass`, `BernsteinInertialClass`, `bernsteinSaturatedBlockProperty`, `BernsteinSaturatedBlock`), `normalizedInductionFunctor`, `RationalLeviConjugacy`, `rationalIsoPullback`, `rationalUnramifiedTwist`, `unramifiedCharacters`, `rationalNormCharacters` |
| `Langlands.Representation.Plancherel.UnramifiedOperatorFamilies` | `unramifiedRegularFunctions` |
| `Mathlib.CategoryTheory.Center.Basic` | `CatCenter` |
