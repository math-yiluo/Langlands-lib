# Iwahori decompositions along an arbitrary parabolic: contracting powers and the Jacquet lemmas (statements)

Module `Langlands.Representation.Exponents.RepresentedIwahoriDecompositionStatements`.
Namespace `Langlands.Aubert.General.RepresentedParabolic`. Universe parameters: `u` (the base
field) and, for the two Jacquet lemmas, `v` (the representation space).

The module contains three `Prop`-valued definitions and nothing else:

- `RepresentedIwahoriContractionStatement` (universe `u`): powers of an element of `A^{++}`
  give the Library's Iwahori contraction conditions for every compact open subgroup with an
  Iwahori decomposition;
- `RepresentedJacquetLemmaStatement` (universes `u`, `v`): Renard VI.6.1, Théorème, for
  admissible representations;
- `RepresentedGeneralizedJacquetLemmaStatement` (universes `u`, `v`): Renard VI.9.1,
  Théorème, for smooth representations.

None of them is proved here. There are no new objects.

Worker 4 wrote this unit under the whole-book task `f5d1f399-a1f8-4ab5-a981-90b92abd4857`,
with the agreement of Worker 1222. It addresses the framework comparison **F2** of the
Chapter VI item ledger (`notes/renard/item-ledger-vi.md`). The ledger records that the
published VI.6.1 Theorem and VI.9.1 Theorem statements use dynamic parabolics and a compact
open `K` that is given together with an `M`-central contracting element. The source instead
allows every `K` with an Iwahori decomposition along an arbitrary parabolic. Before this unit,
no statement said that such a `K` has a contracting element, and no statement covered the
source's hypothesis.

## Common setting

The field and group data are those of the published
`RepresentedParabolic.GeneralizedJacquetContractingRangeStatement` (module
`Langlands.Representation.Exponents.GeneralizedJacquetRemarksStatements`) and
`SplitComponentOppositeContractionStatement`. The statement quantifies over
`k : Type u` with
`[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`,
and both characteristics are allowed. For every group scheme `G` over `Spec k` and every
`hG : IsConnectedReductive G`, it installs `hG.isAffineHom` and the topology
`RationalPointFamily.pointTopology` on `rationalPoints G`. It then quantifies over instances
`[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]`.

The parabolic data are the same, word for word:

- group schemes `P`, `Pbar`, `M`, `N`, `Nbar` over `Spec k`;
- maps `p : P ⟶ G`, `m : M ⟶ P`, `n : N ⟶ P` with `IsParabolicSubgroup p`,
  `IsRationalLeviSubgroup m`, `LeviSubgroup.IsGeometricUnipotentRadical n` and
  `IsIso (subgroupMultiplication m n)`, so that `P = MN`;
- maps `pbar : Pbar ⟶ G`, `mbar : M ⟶ Pbar`, `nbar : Nbar ⟶ Pbar` with the same four
  predicates, so that `P̄ = M N̄`;
- the equations `mbar ≫ pbar = m ≫ p` (the same Levi `M` in `G`) and
  `pointImage p ⊓ pointImage pbar = pointImage (m ≫ p)` (`P(F) ∩ P̄(F) = M(F)`). Together they
  make `P̄` the parabolic opposite to `P` with respect to `M`.

Write `N(F) = pointImage (n ≫ p)`, `M(F) = pointImage (m ≫ p)` and
`N̄(F) = pointImage (nbar ≫ pbar)`, all subgroups of `rationalPoints G`.

**The source's hypothesis on `K`.** `K : OpenSubgroup (rationalPoints G)` must satisfy
`IsCompact (K : Set (rationalPoints G))` and

```text
∀ x ∈ K, ∃ l ∈ K.toSubgroup ⊓ N̄(F), ∃ y ∈ K.toSubgroup ⊓ M(F), ∃ z ∈ K.toSubgroup ⊓ N(F),
  x = l * y * z,
```

that is, `K = K_N̄ K_M K_N` with `K_N̄ = K ∩ N̄`, `K_M = K ∩ M` and `K_N = K ∩ N`. This is the
"décomposition d'Iwahori de `K` selon `P`" of V.5.2 (ii), and it is the only assumption on `K`.
The clause has the same form as the `factor` field of `Jacquet.IsIwahoriContraction`.
Uniqueness of the factorization is not part of the hypothesis; it follows from the other data.
None of the further properties of the V.5.2 basis members is assumed: `K` need not be normal
in a maximal compact subgroup, and no element of `A` is assumed to contract `K_N` or to
normalize `K_M`.

## `RepresentedIwahoriContractionStatement`

In the common setting, take `K` as above, a commutative group scheme `A` over `Spec k`, a map
`a : A.toGrp ⟶ M` and `pres : ParabolicRootPresentation p m a`. The presentation includes
`IsSplitComponent a`, so `A` is the split component of `M`. Let

```text
Δ = (fun α => pres.data.f ≫ α) ''
      (simpleRelativeRoots pres.data.i pres.data.ν \ pres.data.J)
```

be the restrictions to `A` of the simple roots outside `J`, i.e. `Δ(P)`. This encoding is the
same as in `PresentationConeContractionStatement`, `SplitComponentOppositeContractionStatement`
and the Remark 3 target. Let `incG = rationalPoints.map (a ≫ m ≫ p)`. The conclusion is the
conjunction of:

1. **`A^{++}` is nonempty.** There is `t₀ : rationalPoints A.toGrp` with
   `CocharacterUniformizer.characterNorm k A α t₀ < 1` for all `α ∈ Δ`.
2. **Contracting powers.** For every such `t₀` there is `r₀ : ℕ` such that, for every `r ≥ r₀`,
   `Jacquet.IsIwahoriContraction K N(F) M(F) N̄(F) (incG (t₀ ^ r))` holds.

Spelled out for `g = incG (t₀ ^ r)`, the published structure `Jacquet.IsIwahoriContraction`
(module `Langlands.Representation.Jacquet.IwahoriContraction`) has seven fields, and all of
them are required:

- `mem_levi`: `g ∈ M(F)`;
- `factor`: the factorization `K = K_N̄ K_M K_N`;
- `upper`: `g K_N g⁻¹ ⊆ K_N`;
- `levi`: `g⁻¹ K_M g ⊆ K_M`;
- `lower`: `g⁻¹ K_N̄ g ⊆ K_N̄`;
- `exhaust`: for every `x ∈ N(F)` there is `s : ℕ` with `g^s x g^{-s} ∈ K` (pointwise
  exhaustion of `N(F)` by the `g^{-s} K_N g^s`);
- `contract`: for every open subgroup `L` of `G(F)` there is `s : ℕ` such that
  `g^{-s} l g^s ∈ L` for **every** `l ∈ K_N̄` (uniform contraction of the compact set `K_N̄`
  into `L`; one `s` serves all `l`).

So a compact open subgroup with an Iwahori decomposition along `P` has an `M(F)`-central
contracting element taken from `A(F)`. Only large powers are claimed. The statement does not
claim that `t₀` itself satisfies the conditions, because the source's hypothesis on `K` does
not include inclusions such as `t₀ K_N t₀⁻¹ ⊆ K_N`.

## `RepresentedJacquetLemmaStatement` (VI.6.1, Théorème)

In the common setting, for every `K` as above, every `V : Type v` with
`[AddCommGroup V] [Module ℂ V]` and every `ρ : Representation ℂ (rationalPoints G) V` with
`Langlands.IsAdmissible ρ`, the map

```text
Jacquet.fixedJacquetMap ρ N(F) M(F) (pointImage_le_normalizer p m n hn) K.toSubgroup
```

is surjective. Here `Langlands.IsAdmissible ρ` means that `ρ` is smooth and that
`fixedVectors ρ L` is finitely generated for every open subgroup `L`. The map is the Jacquet
quotient map `V → V_N = Coinvariants ρ N(F)` restricted to `V^K`, with values in the vectors
of the Jacquet module fixed by `K.comap M(F).subtype = K ∩ M(F)` for the induced `M(F)`-action
`Jacquet.action`. So the statement says that `j : V → V_N` maps `V^K` onto `(V_N)^{K_M}`.
The inclusion `j(V^K) ⊆ (V_N)^{K_M}` is built into the codomain of `fixedJacquetMap`.

The split component `A` named in the source's statement plays no role in the conclusion, so it
does not appear.

## `RepresentedGeneralizedJacquetLemmaStatement` (VI.9.1, Théorème)

This has the same data and conclusion as `RepresentedJacquetLemmaStatement`, with
`IsSmooth ρ` in place of `Langlands.IsAdmissible ρ`. Since `Langlands.IsAdmissible ρ` contains
`IsSmooth ρ`, this statement implies `RepresentedJacquetLemmaStatement` at once, for the same
universes. The source states both theorems, and the VI.6.1 statement has an elementary
proof (see Proof obligations), so the two are kept separate.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`
(SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).

- V.5.2, Théorème (ii), printed p.123 / PDF p.129. It defines the Iwahori decomposition for
  the basis members `K` of that theorem and for the standard parabolics `P = MN`:
  > Pour tout sous-groupe parabolique standard `P = MN`, on a une décomposition
  > `K = K_N̄ K_M K_N`, `K_N̄ = K ∩ N̄`, `K_N = K ∩ N`, `K_M = K ∩ M`
  > dite décomposition d'Iwahori de `K` selon `P`. De plus, `C_A` normalise `K_M`, `C_A^+`
  > contracte `K_N` et `C_A^- := (C_A^+)^{-1}` contracte `K_N̄`.

  Parts (iii)–(iv) on the same page give, for `m ∈ C_A^{++}`: `N = ⋃_n m^{-n} K_N m^n` and
  `N̄ = ⋃_n m^n K_N̄ m^{-n}`; `{m^i K_N m^{-i}}` is a neighbourhood basis of `1` in `N` and
  `{m^{-i} K_N̄ m^i}` is a neighbourhood basis of `1` in `N̄`; and, uniformly, for every open
  compact subgroup `Γ̄` of `N̄` there is `ε > 0` with `m^{-1} K_N̄ m ⊂ Γ̄` for all
  `m ∈ C_A^+(ε)` (and similarly `m K_N m^{-1} ⊂ Γ` in `N`).
- VI.6.1, Théorème, printed p.176 / PDF p.182:
  > Soit `P = MN` un sous-groupe parabolique de `G`, de composante déployée `A`, et soit
  > `(π, V)` une représentation lisse admissible de `G`. Soit `K` un sous-groupe ouvert compact
  > de `G` admettant une décomposition d'Iwahori selon `P`. Alors l'application de projection
  > `V → V_N` envoie surjectivement `V^K` sur `(V_N)^{K_M}`.

  The sentence before the theorem refers back to V.5.2 for the notion: "La notion de
  décomposition d'Iwahori d'un sous-groupe ouvert compact et les notations afférentes ont été
  introduites en V.5.2."
- VI.9.1, Théorème, printed p.195 / PDF p.201: the same statement for "une représentation
  lisse de `G`", introduced by "L'énoncé du théorème qui suit ne diffère du théorème VI.6.1
  que par le fait que l'on fait plus d'hypothèse d'admissibilité sur la représentation" (sic,
  for "ne fait plus").
- The proofs of both theorems begin with "On choisit alors `t ∈ C_A^{++}`". The proof of
  VI.6.1 uses that `{t^{-m} K_N̄ t^m | m ∈ ℕ}` is a neighbourhood basis of the identity in
  `N̄` ("Théorème V.5.2") and the relations `t^{-1} K_N̄ t ⊂ K_N̄`, `t^{-1} K_M t = K_M`. The
  proof of VI.9.1 uses the same neighbourhood basis of the identity in `N̄`, and in addition,
  for a different family, that the union of the `t^{-m} K_N t^m` (`m ∈ ℕ`) is `N`
  ("Théorème V.5.2"). (The overbars on `K_N̄` and `N̄` are lost in the PDF text layer; these
  readings were checked on the rendered pages.)

**Provenance.** The two Jacquet lemmas are **source** statements: the theorems of VI.6.1 and
VI.9.1 for an arbitrary parabolic. The hypothesis on `K` is the literal Iwahori decomposition.
`RepresentedIwahoriContractionStatement` is **derived**. It isolates the geometric step that
the source's proofs take from V.5.2.

**Formalization choices and source issues.**

- *Arbitrary parabolics.* V.5.2 defines the Iwahori decomposition only along standard
  parabolics, with `N̄` the radical of the standard opposite parabolic. VI.6.1 and VI.9.1 use it
  for an arbitrary `P = MN`. Here `N̄` is the unipotent radical of the parabolic `P̄` opposite to
  `P` with respect to the given Levi `M`. That parabolic is supplied by maps and characterized by
  `mbar ≫ pbar = m ≫ p` and `P(F) ∩ P̄(F) = M(F)`, as in the published Remark 3 target. For a
  standard `P` this is the source's `N̄`.
- *Contracting elements of the source's proofs.* The source's proofs apply to its `t ∈ C_A^{++}`
  the properties that V.5.2 (ii)–(iv) asserts for the V.5.2 basis members. Those properties are
  not part of the hypothesis "admettant une décomposition d'Iwahori selon `P`". For an
  arbitrary `K` with that decomposition, `RepresentedIwahoriContractionStatement` supplies
  what the proofs need, but for a sufficiently large power `t₀^r` rather than for `t₀` itself.
  This is enough for both proofs, which use only one contracting element.
- *Direction of conjugation.* The statement follows V.5.2 (iii)–(iv), the proofs of VI.6.1
  and VI.9.1, and the published `Jacquet.IsIwahoriContraction`, which all use one
  convention: for `|α(t)|_F < 1` (`α ∈ Δ(P)`), conjugation `x ↦ t x t⁻¹` contracts `N` and
  `x ↦ t⁻¹ x t` contracts `N̄`. The source's `t^{-1} K_N̄ t ⊂ K_N̄` is the `lower` field. Its
  neighbourhood basis `{t^{-m} K_N̄ t^m}` of `N̄` corresponds to the uniform `contract` field:
  open subgroups `L` form a neighbourhood basis of `1` in the nonarchimedean group `G(F)`, so
  `contract` says that some conjugate `t^{-s} K_N̄ t^s` lies in any given neighbourhood of `1`.
  This is the shrinking half of the basis property, the half the proofs use. Its
  `N = ⋃_m t^{-m} K_N t^m` is the `exhaust` field.
  `t^{-1} K_M t = K_M` is stated in the source as an equality; the `levi` field asks only for
  the inclusion, and for the central elements `g` used here equality holds anyway.
- *`C_A^{++}` versus `A^{++}`.* The first conjunct of `RepresentedIwahoriContractionStatement`
  lets `t₀` range over all of `A(F)`, not only over the lattice image `C_A`. Since `C_A ⊆ A(F)`,
  the existence clause is implied by the source's choice of `t ∈ C_A^{++}`. The second clause
  for all of `A^{++}` is the form used by the published Remark 3 target and
  `SplitComponentOppositeContractionStatement`.
- *Representations.* Representations are complex, on a carrier in an arbitrary universe `v`,
  as in the published dynamic `RationalPointFamily.GeneralizedJacquetLemmaStatement`.
  Admissibility is the Library's `Langlands.IsAdmissible`.

## Relation to published statements

- `Langlands.Aubert.General.RationalPointFamily.GeneralizedJacquetLemmaStatement` (module
  `Langlands.Representation.Exponents.UniformCompressionStabilizationStatement`, proof task
  `cac6f709`) is VI.9.1 for the dynamic parabolic of a cocharacter `χ` and for those `K` that
  are given together with an `M`-central `g` satisfying `Jacquet.IsIwahoriContraction`.
  `RepresentedGeneralizedJacquetLemmaStatement` has the source's scope: actual parabolics and
  every `K` with an Iwahori decomposition.
- `Langlands.Jacquet.fixedJacquetMap_surjective_of_iwahoriContraction` (module
  `Langlands.Representation.Jacquet.IwahoriContractionAdmissibility`, proved) is the admissible
  argument of VI.6.1 for an abstract triple `(N, M, N̄)` and one given contracting element.
- `RepresentedParabolic.ArbitraryParabolicJacquetAdmissibilityStatement` (VI.6.1 Corollary,
  proved as `arbitraryParabolicJacquetAdmissibility`) is not restated.
- `SplitComponentOppositeContractionStatement` gives the uniform contraction by `A^+(ε)` of
  compact subsets of `N(F)` and `N̄(F)`. `RepresentedIwahoriContractionStatement` is a
  consequence of it together with the centrality of `A` in `M`.
- `Langlands.Jacquet.StandardCanonicalSectionStatement` (VI.6.1 Proposition) and the VI.9.4 statements still
  assume the V.5.2 basis-member conditions (framework comparison F3). This unit does not change
  them.

## Proof obligations

Nothing is proved here. The intended routes are as follows.

- `RepresentedIwahoriContractionStatement`.
  - *Existence of `t₀`.* The restrictions `Δ(P)` are linearly independent in `X^*(A) ⊗ ℚ`.
    Choose a cocharacter `λ` of `A` with `⟨α, λ⟩ > 0` for all `α ∈ Δ` and put `t₀ = λ(ϖ)`.
  - *Contraction.* `K` is compact and `N(F)`, `N̄(F)` are closed, so `K_N` and `K_N̄` are
    compact. Apply `SplitComponentOppositeContractionStatement` with `C = K_N`, `C̄ = K_N̄` and
    `L = K`. Since `characterNorm` is multiplicative, `t₀^r ∈ A^+(ε)` for large `r`, and `A`
    normalizes `N` and `N̄`. This gives the `upper` and `lower` fields.
  - *Levi field.* `incG` takes values in the centre of `M(F)`, so the `levi` field holds.
  - *Exhaustion.* Apply the same statement to `C = {x}` and `L = K`; for `s` large,
    `t₀^{rs} ∈ A^+(ε)`, and this gives `exhaust`. Take `r₀ ≥ 1`.
  - *Uniform contraction.* For the `contract` field, let `L` be an open subgroup of `G(F)`.
    Apply the same statement with `C̄ = K_N̄` (compact, as above) and this `L`; it gives one
    `ε` for all of `K_N̄`. Since `r ≥ 1`, the norms `|α(t₀^{rs})|_F = |α(t₀)|_F^{rs}` tend to
    `0`, so some `s` has `t₀^{rs} ∈ A^+(ε)`. Then `g^{-s} l g^s ∈ L` for every `l ∈ K_N̄`, with
    `g = incG (t₀ ^ r)`. This obligation is separate from the pointwise `exhaust` field for
    `N`: one `s` must serve all of `K_N̄`.
- `RepresentedJacquetLemmaStatement` from `RepresentedIwahoriContractionStatement` (with a
  presentation from the proved `parabolicRootPresentationExistence` and a split component of
  `M`), the centrality of
  `incG (t₀ ^ r)` in `M(F)`, and `fixedJacquetMap_surjective_of_iwahoriContraction`.
- `RepresentedGeneralizedJacquetLemmaStatement` from `RepresentedIwahoriContractionStatement`
  and the dynamic `RationalPointFamily.GeneralizedJacquetLemmaStatement`. This uses a standard
  cocharacter realizing `P` and `M` (the `realization` field of the presentation), and the
  identification of the supplied radicals with the dynamic ones (as in
  `pointImage_radical_eq_dynamic`, module
  `Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityReduction`).
