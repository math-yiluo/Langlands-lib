# `(G, B)`-modules of finite type (Renard VI.10.7, Variant; statements)

Module `Langlands.Representation.Families.RenardFamilyFiniteTypeStatements`, namespace
`Langlands.Renard.AlgebraicFamily`. The module contains three `Prop`-valued definitions. None
of them is proved here, and the module defines nothing else.

- `FamilyFiniteTypeCenterAdmissibleStatement` (universe parameters `u v uB`): the VI.10.7
  Theorem for `(G, B)`-modules. A `(G, B)`-module of finite type is `B ⊗_ℂ ℨ(G)`-admissible.
- `FamilyFiniteTypeComponentCharacterizationStatement` (universe parameters `uF uV uB`): the
  VI.10.7 Lemma and Proposition for `(G, B)`-modules. A `(G, B)`-module is of finite type iff
  it is `B ⊗_ℂ ℨ(G)`-admissible and has nonzero components in only finitely many Bernstein
  blocks.
- `FamilyLeviInductionFiniteTypeStatement` (universe parameters `u' uB' uE'`): the last
  sentence of the Variant. Normalized parabolic induction `i_P^G` preserves `B`-modules of
  finite type.

Worker 4 wrote this unit under the whole-book task `f5d1f399-a1f8-4ab5-a981-90b92abd4857`.
It covers gap 5 of the Chapter VI item ledger (`notes/renard/item-ledger-vi.md`, row
"VI.10.7 Variant (`(G, B)`-modules)"). The ledger records that gap as needing "the action of
`ℨ(G)` on `(G, B)`-modules and the Bernstein components of families". No new construction is
needed for either: see "The action of `ℨ(G)`" and "Components" below.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. PDF page numbers are
one-based and equal printed page numbers plus six. The author read VI.10.7, printed
pp.215–217 / PDF pp.221–223, and VI.8.1, printed pp.187–188 / PDF pp.193–194.

The Variant (printed p.217 / PDF p.223) reads:

> **Variant.** On peut reformuler et démontrer le théorème et la proposition ci-dessus pour
> les `(G, B)`-modules : Un `(G, B)`-module `(τ, E)` est de type fini si et seulement s'il est
> `B ⊗_ℂ ℨ(G)`-admissible et n'a de composantes non nulles que dans un nombre fini de
> `M(G)_𝔰`. On en déduit que les foncteurs d'induction `i_P^G` préservent les `B`-modules de
> type fini.

The results it adapts are on printed pp.215–216 / PDF pp.221–222:

> **Lemme.** Soit `(τ, E)` une représentation de type fini dans `M(G)`. Alors `E_𝔰` est nul
> sauf pour un nombre fini de `𝔰 ∈ B(G)`.
>
> **Théorème.** Soit `(τ, E)` une représentation lisse de type fini de `G`. Alors `(τ, E)` est
> `ℨ(G)`-admissible, c'est-à-dire que pour tout sous-groupe ouvert compact `K` de `G`, `E^K`
> est un `ℨ(G)`-module de type fini.
>
> **Proposition.** Pour qu'une représentation `(τ, E)` de `G` soit de type fini, il faut et il
> suffit qu'elle soit `ℨ(G)`-admissible et n'ait de composantes non nulles que dans un nombre
> fini de `M(G)_𝔰`.

Here `E_𝔰` is "la composante de `E` dans la catégorie `M(G)_𝔰`" (opening of VI.10.7, PDF
p.221). The standing hypothesis of VI.8 and the definition of `(G, B)`-modules (VI.8.1,
printed p.187 / PDF p.193) read:

> Soit `B` une `ℂ`-algèbre commutative noethérienne de type fini réduite (i.e. sans éléments
> nilpotents). [...] **Définition.** Un `(G, B)`-module est un `ℂ`-espace vectoriel `V` muni
> d'une représentation lisse `(π, V)` de `G` et d'une structure de `B`-module plat, où les deux
> actions commutent.

## Encoding of a `(G, B)`-module

In the first two statements a `(G(F), B)`-module is the following data:

- `B : Type uB` with `[CommRing B] [Algebra ℂ B] [IsNoetherianRing B]
  [Algebra.FiniteType ℂ B] [IsReduced B]`. These are Renard's standing hypotheses, written as
  in the published family statements (for example `InductionBaseChangeStatement` and
  `JacquetFiniteTypeStatement`).
- A carrier `V` with `[AddCommGroup V] [Module B V] [Module ℂ V] [IsScalarTower ℂ B V]` and
  `Module.Flat B V`: a complex vector space with a flat `B`-module structure extending its
  complex structure. The scalar-tower condition is how "`ℂ`-espace vectoriel [...] muni d'une
  structure de `B`-module" is read for a `ℂ`-algebra `B`. It is also exactly what lets
  `B ⊗_ℂ ℨ(G)` act, since `(c b) ⊗ z = b ⊗ (c z)` in `B ⊗_ℂ ℨ(G)`. The same binders
  `[Module ℂ V] [IsScalarTower ℂ B V]` appear in the published
  `fixedJacquetMap_surjective_of_complexRepresentation` (module
  `RenardFamilyJacquetAdmissibilityReduction`).
- `ρ : Representation B (rationalPoints G) V` with `hρ : IsSmooth ρ`. Each `ρ g` is
  `B`-linear, which is the commutation of the two actions ("où les deux actions commutent").
- The underlying smooth complex representation `(π, V)` is
  `τ := SmoothRep.of (complexRepresentation ρ) ((isSmooth_complexRepresentation ρ).2 hρ)`,
  introduced by `let` in the statement. `complexRepresentation ρ` is the published restriction
  of each operator `ρ g` to complex scalars on the same carrier (namespace
  `Langlands.Jacquet.CoefficientRestriction`, module `Jacquet/CoefficientScalarRestriction`),
  so `τ g x = ρ g x` for all `g` and `x` (`complexRepresentation_apply`, by `rfl`). Its
  smoothness is `isSmooth_complexRepresentation`, an `Iff.rfl`.

Up to the separate complex structure, these data are an object of the published category
`FamilyModule B G` of `(G, B)`-modules (module `RenardFamilyCategory`): a smooth `B`-linear
representation on a flat `B`-module. The statements add `[Module ℂ V] [IsScalarTower ℂ B V]`
because the centre `ℨ(G)` and the Bernstein blocks belong to the category of smooth complex
representations, and `τ` must live there. Every object of `FamilyModule` gives such data with
the complex structure induced along `algebraMap ℂ B`. Conversely, `IsScalarTower ℂ B V` forces
the given complex structure to be that induced one.

The `K`-fixed vectors of the `(G, B)`-module are the `B`-submodule `fixedVectors ρ K`, as in
the published admissibility predicate `admissibleProperty` of `RenardFamilyCategory`. It has the
same elements as `fixedVectors τ.representation K`, since the operators agree.

Renard's `(τ, E)` is `(τ, V)` here. The explanations below keep his notation `E` and `E^K` for
the carrier and its `K`-fixed vectors.

**Finite type** is `Module.Finite (MonoidAlgebra B (rationalPoints G)) ρ.asModule`, finite
generation over `B[G(F)]`. This is the convention of the published VI.8.3 statement
`JacquetFiniteTypeStatement` ("le foncteur `r_P^G` préserve les `B`-modules de type fini").

### The action of `ℨ(G)`

`ℨ(G)` is the published `CatCenter (SmoothRep ℂ (rationalPoints G))`, the centre of the
category of smooth complex representations, as in the published VI.10.7 statements
`FiniteTypeCenterAdmissibleStatement` and `FiniteTypeComponentCharacterizationStatement`. An
element `z` acts on the `(G, B)`-module through `SmoothRep.hom (z.app τ)`.

This action commutes with `B`. Multiplication by `b ∈ B` is a `G(F)`-equivariant complex
linear map, because each `τ g = ρ g` is `B`-linear. It is therefore an endomorphism of `τ` in
`SmoothRep ℂ`, and the naturality of `z` gives `z ∘ b = b ∘ z`. So `B ⊗_ℂ ℨ(G)` acts on `E`
by `(b ⊗ z) · x = b · (z · x)`, and it preserves `E^K` for every compact open `K`. The
statements do not need this fact. It is what makes the source's notion meaningful.

### `B ⊗_ℂ ℨ(G)`-admissibility

By analogy with the definition in the Theorem, "`B ⊗_ℂ ℨ(G)`-admissible" means: for every
compact open subgroup `K`, `E^K` is a finitely generated `B ⊗_ℂ ℨ(G)`-module. The statements
write this as follows. There are `n : ℕ` and `s : Fin n → V` with every
`s j ∈ fixedVectors ρ K`, such that `fixedVectors ρ K` is contained in

`Submodule.span B {y | ∃ j z, y = SmoothRep.hom (z.app τ) (s j)}`.

This is equivalent to `E^K = ∑ⱼ (B ⊗_ℂ ℨ(G)) · sⱼ`. Every element of `B ⊗_ℂ ℨ(G)` is a finite
sum of pure tensors `b ⊗ z`, so `(B ⊗_ℂ ℨ(G)) · sⱼ` is the `B`-span of the vectors `z · sⱼ`.
The inclusion `∑ⱼ (B ⊗_ℂ ℨ(G)) · sⱼ ⊆ E^K` is automatic, because `z.app τ` and `B` preserve
`K`-fixed vectors. For `B = ℂ` the condition is the published one
(`x = ∑ j, SmoothRep.hom ((z j).app τ) (s j)`), since `ℨ(G)` is a complex vector space. The
`B`-span formulation avoids building the tensor-product algebra `B ⊗_ℂ ℨ(G)` and its module
structure.

### Components

"N'a de composantes non nulles que dans un nombre fini de `M(G)_𝔰`" is about the underlying
smooth complex representation `τ`. The second statement uses the same formulation as the
published `FiniteTypeComponentCharacterizationStatement`, in the standard-family framework
(`BernsteinStandardFamily`, `BernsteinInertialClass`, `IsBernsteinInertialSupport`). The
condition is that the set of inertial classes `s` such that some `π` is an actual subquotient
of `τ` (`SmoothRep.IsSubquotient π τ`) with `IsBernsteinInertialSupport i ν family s π` is
finite. The Markdown of that published statement explains why this agrees with
"`E_𝔰 ≠ 0` for finitely many `𝔰`" given the Bernstein decomposition. The explanation applies
verbatim, since the `B`-structure plays no role in it.

## `FamilyFiniteTypeCenterAdmissibleStatement`

The group-theoretic binders are those of the published `FiniteTypeCenterAdmissibleStatement`
(Renard VI.10.7, Theorem):

- a nonarchimedean local field `k : Type u` (any characteristic, `[T2Space k]`);
- a connected reductive `G` over `k` (`hG : IsConnectedReductive G`), with
  `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` installed on
  `rationalPoints G`, and `[LocallyCompactSpace (rationalPoints G)]` and
  `[NonarchimedeanGroup (rationalPoints G)]` assumed.

The statement quantifies over `B` and a `(G(F), B)`-module `(V, ρ)` as above, with
`V : Type v`, so that `τ : SmoothRep.{0, u, v} ℂ (rationalPoints G)`. It assumes
`Module.Finite (MonoidAlgebra B (rationalPoints G)) ρ.asModule`. Its conclusion is
`B ⊗_ℂ ℨ(G)`-admissibility for every compact open `K : OpenSubgroup (rationalPoints G)`
(`IsCompact (K : Set (rationalPoints G))`), with
`ℨ(G) = CatCenter (SmoothRep.{0, u, v} ℂ (rationalPoints G))`.

## `FamilyFiniteTypeComponentCharacterizationStatement`

The group-theoretic binders are those of the published
`FiniteTypeComponentCharacterizationStatement` (Renard VI.10.7, Lemma and Proposition):

- a nonarchimedean local field `F : Type uF`;
- `G` with `[IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]`, with `G(F)` locally compact
  and nonarchimedean in the canonical topology `pointTopology`;
- `T`, `i`, `ν` and `family : BernsteinStandardFamily i ν`.

The statement quantifies over `B` and a `(G(F), B)`-module `(V, ρ)` as above, with
`V : Type (max uF uV)`. So `τ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)` has the
carrier universe of the published blocks. The conclusion is an equivalence between
`Module.Finite (MonoidAlgebra B (rationalPoints G)) ρ.asModule` and the conjunction of:

1. `B ⊗_ℂ ℨ(G)`-admissibility for every compact open `K`, with
   `ℨ(G) = CatCenter (SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))`; and
2. finiteness of the set of inertial classes of irreducible subquotients of `τ`, exactly as
   in the published statement.

The forward implication contains the Variant of the Lemma (condition 2) and of the Theorem
(condition 1). The equivalence is the Variant of the Proposition, which is the sentence
quoted above.

The first statement is not a special case of the second. The second needs the standard-family
data, and the first is stated for every connected reductive `G`, exactly as the two published
complex statements are.

## `FamilyLeviInductionFiniteTypeStatement`

The binders are those of the published VI.8.2 statement `InductionBaseChangeStatement`:

- `k`, `G`, `hG` as in the first statement;
- every actual rational parabolic `p : P ⟶ G` (`hp : IsParabolicSubgroup p`) with rational
  Levi `l : M ⟶ P` (`hl : IsRationalLeviSubgroup l`) and matching geometric unipotent radical
  `r : U ⟶ P` (`hr`, `hmul : IsIso (subgroupMultiplication l r)`). The statement installs
  `hl.isConnectedReductive.isAffineHom` and the canonical topology `leviPointTopology l hl` on
  `rationalPoints M`;
- `B : Type uB'` as above, and an `(M(F), B)`-module `σ : Representation B (rationalPoints M) E`
  with `E : Type uE'`, `IsSmooth σ` and `Module.Flat B E`.

Here the `(M(F), B)`-module is a `B`-linear representation, as in the published family
statements. Its complex structure is the one induced along `algebraMap ℂ B`, and no centre or
block appears. If `σ` is finitely generated over `B[M(F)]`, the statement concludes that the
published normalized family induction `leviInducedRepresentation p l r hp hr hl hmul σ`
(`i_P^G(σ)`, module `RenardFamilyParabolicFunctors`) is finitely generated over `B[G(F)]`.
`P = G` is allowed.

"Les foncteurs d'induction `i_P^G` préservent les `B`-modules de type fini" is read as "send
`(M, B)`-modules of finite type to `(G, B)`-modules of finite type". This parallels the VI.8.3
sentence for `r_P^G` quoted above and the complex VI.7.5 Theorem (published
`LeviInductionFiniteTypeStatement`). That `i_P^G(σ)` is again a `(G, B)`-module, smooth and
flat, is not part of this sentence. Smoothness is the published
`isSmooth_inducedRepresentation`. Flatness is the published VI.8.2 statement
`InductionFlatStatement`.

## Hypotheses that are kept although the expected proofs do not use them

The reductions sketched below use neither flatness nor the Noetherian, finite-type or
reducedness hypotheses on `B`. The statements keep them because they are the hypotheses under
which Renard defines `(G, B)`-modules and states the Variant. A later unit could drop them.

## Proof routes (not part of the statements)

These remarks only guide later proof tasks.

- **First statement.** Pick `B[G(F)]`-generators `e₁, …, e_m`, and let `W ⊆ τ` be the complex
  subrepresentation that they generate over `ℂ[G(F)]`. Then `W` is of finite type, and its
  carrier is a subtype of that of `τ`, in the same universe. The carrier of `τ` is the
  `B`-span of `W`. The published complex Theorem `FiniteTypeCenterAdmissibleStatement`
  applied to `W` gives generators of `W^K` over `ℨ(G)`. For `x ∈ E^K`, write
  `x = ∑ bᵢ wᵢ` and apply the averaging projector onto the `K`-fixed vectors, which commutes
  with `B`. Naturality of `z` along the inclusion `W → τ` finishes the proof.
- **Second statement, forward direction.** Condition 1 is the first statement, in the
  standard-family setting through the forward direction of the published complex
  characterization applied to `W`. For condition 2: let `π ≅ X / Y` be an irreducible
  subquotient of `τ` and pick `x ∈ X \ Y`, say `x = ∑_{i ≤ r} bᵢ wᵢ`. The map `W^r → τ`,
  `(w'ᵢ) ↦ ∑ bᵢ w'ᵢ`, is `G(F)`-equivariant, and its image `I` contains `x`. By
  irreducibility `π ≅ (X ∩ I) / (Y ∩ I)`, so `π` is a subquotient of the quotient `I` of
  `W^r`. An irreducible subquotient of `W ⊕ W'` is a subquotient of `W` or of `W'`, by
  intersecting with the first summand. So the classes are among the finitely many classes of
  `W`.
- **Second statement, reverse direction.** Renard proves the complex Proposition with the
  VI.10.6 Proposition for a well-chosen `K`. The Library versions of that input are open
  and concern the standard family built by `standardBernsteinFamily`
  (`StandardBernsteinFixedVectorVisibilityStatement`, `bernsteinFixedVectorVisibility`).
  For an arbitrary `family`, as in the statement, the following route uses only the
  published complex characterization.
  1. *Uniform level.* Some compact open `K` has the property that every irreducible
     subquotient of `τ` has a nonzero `K`-fixed vector. Otherwise take a decreasing sequence
     `K₁ ⊇ K₂ ⊇ ⋯` of compact open subgroups that is a neighbourhood basis of `1`, and
     irreducible subquotients `πₙ` of `τ` with `πₙ^{Kₙ} = 0`. Let `X = ⊕ₙ πₙ`. Every
     irreducible subquotient of the semisimple `X` is isomorphic to some `πₙ`. So the
     inertial classes of `X` lie in the finite set of condition 2.
     `SmoothRep.IsSubquotient` allows an isomorphism in its first argument, so this needs
     only that `IsIrreducible` is invariant under isomorphism. Next, `X` is
     `ℨ(G)`-admissible. For `n ≥ m`, `πₙ^{K_m} ⊆ πₙ^{Kₙ} = 0`, so
     `X^{K_m} = ⊕_{n<m} πₙ^{K_m}`. Each `πₙ` is cyclic, hence `ℨ(G)`-admissible by the
     forward direction of the published complex characterization. A general `K'` contains
     some `K_m`, and the averaging projector onto `X^{K'}` commutes with `ℨ(G)`. By the
     published complex characterization, `X` is finitely generated. Its generators are
     fixed by some `K_m`, so `X` is generated by `X^{K_m}`. This lies in the
     subrepresentation `⊕_{n<m} πₙ`, which therefore equals `X`, although `π_m ≠ 0`.
  2. *Generation.* For this `K`, take the vectors `sⱼ` of condition 1 and let `W'` be their
     `ℂ[G(F)]`-span. Each `z · sⱼ` lies in `W'`, because `z.app τ` commutes with the inclusion
     of `W'`. So `E^K` lies in the `B`-span `B · W'`, which is a subrepresentation. The
     quotient `Q = τ / (B · W')` has no nonzero `K`-fixed vectors, by exactness of
     `K`-invariants. If `Q ≠ 0`, it has an irreducible subquotient (a nonzero cyclic
     subrepresentation has an irreducible quotient). That subquotient is an irreducible
     subquotient of `τ` without nonzero `K`-fixed vectors, which contradicts step 1. Hence
     `Q = 0`, and the `sⱼ` generate `E` over `B[G(F)]`.

  The proof task must supply from the Library, or prove as lemmas, the existence of
  irreducible subquotients and the semisimplicity facts used in step 1.
- **Third statement.** If `σ` is generated over `B[M(F)]` by `e₁, …, e_m`, let `W` be their
  complex `ℂ[M(F)]`-span. Then `σ = B · W`, and the published complex VI.7.5 Theorem
  `LeviInductionFiniteTypeStatement` makes `i_P^G(W)` of finite type. Every `f ∈ i_P^G(σ)` is
  determined by its values at finitely many representatives of `P\G/K'`. Each value can be
  written as a `B`-combination of vectors of `W` with the required invariance, using averaging
  projectors, which commute with `B`. Hence `i_P^G(σ) = B · i_P^G(W)`. Renard's own route goes
  through the first two statements for `M` and `G`.

## Not stated here

- The objects `E_𝔰` themselves (the Bernstein decomposition of a `(G, B)`-module) are not
  defined. The components enter only through irreducible subquotients, as in the published
  complex statement.
- The tensor-product algebra `B ⊗_ℂ ℨ(G)` and its module structure on `E^K` are not built (see
  "`B ⊗_ℂ ℨ(G)`-admissibility").
