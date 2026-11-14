# Renard VI.6.1 Proposition and VI.9.1 Proposition along an arbitrary parabolic (statements)

Module `Langlands.Representation.Exponents.RepresentedCanonicalSectionStatements`.
Namespace `Langlands.Aubert.General.RepresentedParabolic`. Universe parameters: `u` (the base
field) and, for the three statements about representations, `v` (the representation space).

The module contains four `Prop`-valued definitions and nothing else:

- `RepresentedChamberIwahoriContractionStatement` (universe `u`, derived): every element of a
  small chamber `A^+(ε)` gives the Library's Iwahori contraction conditions for a compact open
  subgroup with an Iwahori decomposition;
- `RepresentedCanonicalSectionStatement` (universes `u`, `v`): Renard VI.6.1, (VI.6.1.2) and
  the Proposition (the canonical section `s_P^K`), for admissible representations;
- `RepresentedUniformCompressionStabilizationStatement` (universes `u`, `v`): Renard VI.9.1,
  the Proposition, with the conclusion drawn from it at the end of the proof of the VI.9.1
  Theorem;
- `RepresentedGeneralizedJacquetRemarksStatement` (universes `u`, `v`): Renard VI.9.1, the
  bound `b ≤ c(G, K)` and Remarks 1–2.

None of them is proved here. There are no new objects.

Worker 4 wrote this unit under the whole-book task `f5d1f399-a1f8-4ab5-a981-90b92abd4857`,
with the agreement of Worker 1222. It completes the framework comparison **F2** of the
Chapter VI item ledger (`notes/renard/item-ledger-vi.md`) for the rows "VI.6.1 Proposition"
and "VI.9.1 Proposition" and for the bound and Remarks 1–2 of VI.9.1. The published module
`RepresentedIwahoriDecompositionStatements` already states the VI.6.1 and VI.9.1 Theorems
(the Jacquet lemmas) for an arbitrary parabolic and every `K` with an Iwahori decomposition.
The Proposition of VI.6.1 was published only for standard parabolics
(`Langlands.Jacquet.StandardCanonicalSectionStatement`). The Proposition and the Remarks of
VI.9.1 were published only for dynamic parabolics and for those `K` that are given together
with an `M`-central contracting element
(`RationalPointFamily.UniformCompressionStabilizationStatement`,
`RationalPointFamily.GeneralizedJacquetRemarksStatement`). This unit states them for actual
rational parabolics `P = MN` in the setting of the published
`GeneralizedJacquetContractingRangeStatement` (VI.9.1, Remark 3), which is the setting of the
source.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. PDF page numbers are
one-based and equal printed page numbers plus six. The PDF text layer loses overbars, so the
author checked every formula with `N̄` or `C̄` on the rendered pages (PDF pp.129, 182, 183,
201, 203).

**Iwahori decomposition (V.5.2 (ii), printed p.123 / PDF p.129).**

> Pour tout sous-groupe parabolique standard `P = MN`, on a une décomposition
> `K = K_N̄ K_M K_N`, `K_N̄ = K ∩ N̄`, `K_N = K ∩ N`, `K_M = K ∩ M`
> dite décomposition d'Iwahori de `K` selon `P`.

The next sentence ("De plus, `C_A` normalise `K_M`, `C_A^+` contracte `K_N` et
`C_A^- := (C_A^+)^{-1}` contracte `K_N̄`") and the clauses (iii)–(iv) are further properties of
the members of the neighbourhood basis that the Theorem constructs. They are not part of the
term "décomposition d'Iwahori". VI.6.1 and VI.9.1 use the term for an arbitrary parabolic
("La notion de décomposition d'Iwahori d'un sous-groupe ouvert compact et les notations
afférentes ont été introduites en V.5.2", PDF p.182).

**`A^+(ε)` (V.3.22.1, printed p.117 / PDF p.123).** `A^+(ε) = {a ∈ A_M | |α(a)|_F < ε,
α ∈ Δ(P)}`; `C_A^+(ε)` is its intersection with the lattice image `C_A`.

**VI.6.1, after the Theorem (printed p.177 / PDF p.183).** For `K` with an Iwahori
decomposition along `P` and `(π, V)` admissible, the text constructs a section of the
surjection `j : V^K → V_N^{K_M}`:

> Pour tout `v ∈ V^K ∩ ker j = V^K ∩ V(N)`, il existe d'après la proposition III.2.9, un
> sous-groupe compact ouvert `Γ` de `N` tel que `e_Γ · v = 0`. Comme `V^K` est de dimension
> finie, on peut même choisir `Γ` de telle sorte que `e_Γ · v = 0` pour tout
> `v ∈ V^K ∩ ker j`. D'après le théorème V.5.2 (iv), il existe `ε > 0` tel que pour tout
> `t ∈ C_A^+(ε)`, `Γ ⊂ t^{-1} K_N t`.

It deduces (VI.6.1.2) `V^K ∩ ker j = V^K ∩ V(N) ⊂ ker π(a_{t,K})`, then that `j` induces an
isomorphism of `Im π(a_{t,K})` onto `V_N^{K_M}` (the surjectivity uses "le lemme de Jacquet",
the Theorem), then `ker j|_{V^K} = ker π(a_{t,K})` and `V^K = ker π(a_{t,K}) ⊕ Im π(a_{t,K})`.
It sets `V_0^K = ker π(a_{t,K})`, `V_*^K = Im π(a_{t,K})`:

> **Proposition.** La décomposition `V^K = V_0^K ⊕ V_*^K` obtenue ci-dessus ne dépend pas du
> choix de `t ∈ C_A^+(ε)`. On obtient en inversant la restriction de `j` à `V_*^K` une
> section, ne dépendant que de `P` et `K`, `s_P^K : V_N^{K_M} → V_*^K ⊂ V^K`.

The proof: "Soit `t′` un autre élément satisfaisant les mêmes hypothèses que `t`. Alors `tt′`
vérifie encore ces hypothèses, et comme d'après le lemme V.5.3,
`a_{t,K} a_{t′,K} = a_{tt′,K} = a_{t′,K} a_{t,K}`, …". Here `a_{t,K} = e_K ∗ δ_t ∗ e_K`, which acts
on `V^K` by `v ↦ e_K(π(t) v)`.

**VI.9.1 (printed pp.195–197 / PDF pp.201–203).** The Theorem is the Jacquet lemma for
smooth `V`. Its proof chooses `t ∈ C_A^{++}`, sets `A` = the endomorphism of `V^K` given by
`a_{t,K}`, and proves two lemmas: `V(N) ∩ V^K = ⋃_i ker A^i`, and that the localization of
`V^K` at `A` is `(V_N^{K_M}, π_N(t))` through `j`. Then:

> **Proposition.** Le morphisme `A` est finalement stable. Plus précisément, il existe une
> constante `b = b(G, K)` ne dépendant que de `G` et `K` telle que pour toute représentation
> lisse `(π, V)`, `A^b` est un endomorphisme stable de `V^K`. Posons `V_0^K = ker A^b`,
> `V_*^K = Im A^b`. On a alors `V^K = V_0^K ⊕ V_*^K`. Le localisé de `V^K` en `A` est alors
> aussi (naturellement) isomorphe à `(V_*^K, A|V_*^K)`, le morphisme canonique `ι` étant donné
> par la projection sur `V_*^K` parallèlement à `V_0^K`. De plus la constante `b` peut être
> choisie plus petite ou égale que la constante `c(G, K)` du théorème d'admissibilité
> uniforme VI.2.3.
>
> […] finissons la démonstration du théorème. On déduit des deux lemmes et de la
> proposition que `j` réalise un isomorphisme (naturel) de `V_*^K` dans `V_N^{K_M}` et que le
> noyau de `j` sur `V^K` est `V_0^K`.
>
> *Remarques.* 1. La décomposition `V^K = V_0^K ⊕ V_*^K` ne dépend pas du choix de `t` dans
> `C_A^{++}`. Si `(π, V)` est admissible, on retrouve la décomposition de la proposition
> VI.6.1. — 2. Il existe des sous-groupes ouverts compacts `C` de `N` et `C̄` de `N̄` tels que
> pour tout `(π, V) ∈ M(G)`, `V_0^K = V^K ∩ ker e_C`, `V_*^K = e_K ∗ e_{C̄} · V`. — 3. Il
> existe `ε > 0` tel que pour tout `t ∈ A^+(ε)`, `V_0^K = ker π(a_{t,K})`,
> `V_*^K = Im π(a_{t,K})`.

The proof of Remark 1 uses "pour tout autre élément `s` de `C_A^{++}`, d'après le lemme V.5.3,
… `a_{s^n,K} a_{t^n,K} = a_{(st)^n,K}`".

## Common setting

The field, group and parabolic data are those of the published
`GeneralizedJacquetContractingRangeStatement`, `SplitComponentOppositeContractionStatement`
and `RepresentedIwahoriDecompositionStatements`, word for word:

- `k : Type u` with
  `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`
  (both characteristics allowed); a group scheme `G` over `Spec k` with
  `hG : IsConnectedReductive G`; the instance `hG.isAffineHom`, the topology
  `RationalPointFamily.pointTopology` on `rationalPoints G`, and instances
  `[LocallyCompactSpace (rationalPoints G)]`, `[NonarchimedeanGroup (rationalPoints G)]`;
- group schemes `P`, `Pbar`, `M`, `N`, `Nbar`; maps `p : P ⟶ G`, `m : M ⟶ P`, `n : N ⟶ P`
  with `IsParabolicSubgroup p`, `IsRationalLeviSubgroup m`,
  `LeviSubgroup.IsGeometricUnipotentRadical n` and `IsIso (subgroupMultiplication m n)`
  (`P = MN`); maps `pbar`, `mbar`, `nbar` with the same four predicates (`P̄ = M N̄`);
- `mbar ≫ pbar = m ≫ p` (the same Levi) and
  `pointImage p ⊓ pointImage pbar = pointImage (m ≫ p)` (`P(F) ∩ P̄(F) = M(F)`). So `P̄` is
  the parabolic opposite to `P` with respect to `M`.

Write `N(F) = pointImage (n ≫ p)`, `M(F) = pointImage (m ≫ p)`,
`N̄(F) = pointImage (nbar ≫ pbar)`, and `hMN = pointImage_le_normalizer p m n hn` for the
normalization of `N(F)` by `M(F)` used by the Jacquet action.

**Split component and chamber.** The first two statements also take a commutative group
scheme `A`, a map `a : A.toGrp ⟶ M` and `pres : ParabolicRootPresentation p m a` (which
includes `IsSplitComponent a`). As in the published Remark 3 target,
`Δ = (fun α => pres.data.f ≫ α) '' (simpleRelativeRoots pres.data.i pres.data.ν \ pres.data.J)`
is `Δ(P)`, `incG = rationalPoints.map (a ≫ m ≫ p) : A(F) →* G(F)`, and
`CocharacterUniformizer.characterNorm k A α t` is the normalized norm `|α(t)|_F`. "`t ∈ A^+(ε)`"
below means `∀ α ∈ Δ, characterNorm k A α t < ε`, for `t : rationalPoints A.toGrp`.

**The source's hypothesis on `K`.** In the first two statements,
`K : OpenSubgroup (rationalPoints G)` is compact and

```text
∀ x ∈ K, ∃ l ∈ K.toSubgroup ⊓ N̄(F), ∃ y ∈ K.toSubgroup ⊓ M(F), ∃ z ∈ K.toSubgroup ⊓ N(F),
  x = l * y * z,
```

that is, `K = K_N̄ K_M K_N`, the Iwahori decomposition of `K` along `P`. This is the hypothesis
of the published `RepresentedIwahoriDecompositionStatements`, and the only one on `K`.

**Contracting elements.** The last two statements take, as the published dynamic VI.9.1
statements do, a compact open `K` and `g : rationalPoints G` with `∀ x ∈ M(F), x * g = g * x`
and `Jacquet.IsIwahoriContraction K N(F) M(F) N̄(F) g`. The seven fields of that structure
(module `Langlands.Representation.Jacquet.IwahoriContraction`) are: `mem_levi` (`g ∈ M(F)`);
`factor` (the Iwahori decomposition `K = K_N̄ K_M K_N` above); `upper`
(`g K_N g⁻¹ ⊆ K_N`); `levi` (`g⁻¹ K_M g ⊆ K_M`); `lower` (`g⁻¹ K_N̄ g ⊆ K_N̄`); `exhaust`
(every `x ∈ N(F)` has some `g^r x g^{-r} ∈ K`); `contract` (for every open subgroup `L` of
`G(F)` some `s` has `g^{-s} l g^s ∈ L` for all `l ∈ K_N̄`). So these `K` have an Iwahori
decomposition along `P`, and `g` plays the role of the source's `t ∈ C_A^{++}`.
`RepresentedChamberIwahoriContractionStatement` provides such `g` for every `K` with an
Iwahori decomposition.

**Representations.** Complex representations `ρ : Representation ℂ (rationalPoints G) V` on
`V : Type v` with `[AddCommGroup V] [Module ℂ V]`. For smooth `ρ` (`hρ : IsSmooth ρ`) and
`h : G(F)`:

- `Jacquet.compressedAction ρ hρ K hK h` is `v ↦ e_K(ρ(h) v)` on
  `V^K = fixedVectors ρ K.toSubgroup`, the source's `π(a_{h,K})` (and `A` for `h = t`);
- `Jacquet.powerKernelSup ρ hρ K hK h` is `⨆ r, ker (compressedAction ^ r)` and
  `Jacquet.stableImage ρ hρ K hK h` is `⨅ r, range (compressedAction ^ r)`;
- `j = Jacquet.fixedJacquetMap ρ N(F) M(F) hMN K.toSubgroup : V^K → (V_N)^{K ∩ M(F)}` is the
  Jacquet quotient map, with values in the vectors of `V_N = Coinvariants ρ N(F)` fixed by
  `K.toSubgroup.comap M(F).subtype` for the action `Jacquet.action`;
- `Jacquet.compressedImageJacquetMap ρ hρ K hK h N(F) M(F) hMN` is `j` restricted to
  `range (compressedAction …)`, `Jacquet.compressedImageLift … hb` its inverse followed by
  the inclusion into `V^K` (given a proof `hb` of bijectivity), and
  `Jacquet.stableImageJacquetMap ρ hρ K hK h N(F) M(F) hMN` is `j` restricted to the stable
  image.

## `RepresentedChamberIwahoriContractionStatement` (derived)

In the common setting, for every compact open `K` with an Iwahori decomposition along `P`,
every `A`, `a`, `pres`, there is a real `ε` with `0 < ε ≤ 1` such that:

1. `A^+(ε)` is nonempty: some `t : rationalPoints A.toGrp` has `|α(t)|_F < ε` for all
   `α ∈ Δ`;
2. for every `t ∈ A^+(ε)`,
   `Jacquet.IsIwahoriContraction K N(F) M(F) N̄(F) (incG t)` holds, with all seven fields.

So every element of a small chamber, not only a large power of one element, is a contracting
element for `K`. The bound `ε ≤ 1` makes `A^+(ε)` closed under products and powers.

## `RepresentedCanonicalSectionStatement` (VI.6.1, (VI.6.1.2) and Proposition)

In the common setting, for every compact open `K` (with `hK`) with an Iwahori decomposition
along `P`, every `A`, `a`, `pres`, and every `ρ` on `V : Type v` with
`hρ : Langlands.IsAdmissible ρ` (smooth with finitely generated `fixedVectors ρ L` for every
open subgroup `L`), write `C_t = Jacquet.compressedAction ρ hρ.1 K hK (incG t)`. There are a
real `ε` with `0 < ε ≤ 1`, a point of `A^+(ε)`, and a linear map
`s : (V_N)^{K ∩ M(F)} →ₗ[ℂ] V^K` with `j ∘ s = id`, such that for every `t ∈ A^+(ε)`:

1. `ker j ≤ ker C_t` — (VI.6.1.2);
2. `ker C_t = ker j`;
3. `IsCompl (ker C_t) (range C_t)` — `V^K = V_0^K ⊕ V_*^K`;
4. `compressedImageJacquetMap … (incG t) …` is bijective — `j` maps `Im π(a_{t,K})` isomorphically
   onto `(V_N)^{K_M}`;
5. `range C_t = stableImage … (incG t)`;
6. `powerKernelSup … (incG t) = ker j`;
7. `range s = range C_t`;
8. for every proof `hb` of the bijectivity in 4,
   `compressedImageLift … (incG t) … hb = s`.

Since `ε` and `s` are chosen before `t`, the decomposition `V^K = ker C_t ⊕ range C_t` and
the section `s = s_P^K` (the inverse of `j` on `V_*^K`) do not depend on `t ∈ A^+(ε)`, which is
the Proposition. Clauses 5 and 6 identify this decomposition with the one of VI.9.1 (kernel
supremum and stable image of the same compressed action), which is the second sentence of
VI.9.1 Remark 1. The conclusions are those of the published
`Langlands.Jacquet.StandardCanonicalSectionStatement` for standard parabolics, with
`A^+(ε)` in place of its `C_A^+(ε)`.

## `RepresentedUniformCompressionStabilizationStatement` (VI.9.1 Proposition and Theorem)

In the common setting, for every compact open `K` (with `hK`) and every `M(F)`-central
`g` with `Jacquet.IsIwahoriContraction K N(F) M(F) N̄(F) g`, there is `b : ℕ` such that for
every smooth `ρ` (`hρ : IsSmooth ρ`) on `V : Type v`, with `A` the compressed action of `g`:

1. for every `s ≥ b`, `stableImage = range (A ^ s)` and `powerKernelSup = ker (A ^ s)` — the
   stability of `A^b`, with `V_0^K = ker A^b` and `V_*^K = Im A^b`;
2. `Jacquet.CompactCompressionSplits ρ hρ K hK g`, i.e.
   `IsCompl powerKernelSup stableImage` — `V^K = V_0^K ⊕ V_*^K`;
3. `ker j = powerKernelSup` — "le noyau de `j` sur `V^K` est `V_0^K`";
4. `stableImageJacquetMap … g …` is bijective — "`j` réalise un isomorphisme de `V_*^K` dans
   `V_N^{K_M}`".

Clauses 1–2 are the conclusion of the published dynamic
`RationalPointFamily.UniformCompressionStabilizationStatement`. Clauses 3–4 are the
conclusion the source draws from the Proposition and the two lemmas at the end of the proof
of the Theorem. With `RepresentedChamberIwahoriContractionStatement`, clause 4 gives the
published `RepresentedGeneralizedJacquetLemmaStatement` (the surjectivity of `j`).

## `RepresentedGeneralizedJacquetRemarksStatement` (VI.9.1, bound and Remarks 1–2)

Same data as the previous statement: `K`, `hK`, and an `M(F)`-central `g` with
`IsIwahoriContraction K N(F) M(F) N̄(F) g`. With `A`, `V_0^K = powerKernelSup` and
`V_*^K = stableImage` for `g`, the conclusion is the conjunction of:

1. **Bound.** For every `c : ℕ` such that `Module.rank ℂ (fixedVectors A'.representation K) ≤ c`
   for every irreducible `A' : SmoothRep.{0, u, v} ℂ (rationalPoints G)`, every smooth `ρ` on
   `V : Type v` and every `s ≥ c`: `stableImage = range (A ^ s)` and
   `powerKernelSup = ker (A ^ s)`.
2. **Remark 1.** For every `M(F)`-central `g'` with `IsIwahoriContraction K N(F) M(F) N̄(F) g'`
   and every smooth `ρ`, `g'` and `g` have the same `powerKernelSup` and the same
   `stableImage`.
3. **Remark 2.** There are `C : OpenSubgroup N(F)` and `Cbar : OpenSubgroup N̄(F)`, compact in
   the subspace topologies, such that for every smooth `ρ` on `V : Type v`:
   `powerKernelSup = ker (e_C ∘ inclusion of V^K)` and the image of `stableImage` in `V` is
   `range (e_K ∘ e_{C̄})`. Here `e_C = Compact.averageMap (ρ.comp N(F).subtype) _ C hC`, the
   normalized average over `C` of the restriction of `ρ` to `N(F)` (smooth by the published
   `isSmooth_comp`), `e_{C̄}` is defined in the same way, and
   `e_K = Compact.averageMap ρ hρ K hK`.

This is the published dynamic `RationalPointFamily.GeneralizedJacquetRemarksStatement`, with
the same three clauses, transcribed to actual rational parabolics; its Markdown explains the
modelling of the bound (every bound `c` on `dim V^K` over irreducibles is a valid exponent)
and of Remark 2 (`V^K ∩ ker e_C` as a kernel on `V^K`, `e_K ∗ e_{C̄} · V` as a range on `V`).

## Formalization choices and source issues

- **The source's `t ∈ C_A^{++}` for a general `K`.** The source's proofs apply to its
  `t ∈ C_A^{++}` (VI.9.1) or `t ∈ C_A^+(ε)` (VI.6.1) the properties that V.5.2 (ii)–(iv)
  asserts for the V.5.2 basis members: `t K_N t⁻¹ ⊂ K_N`, `t⁻¹ K_N̄ t ⊂ K_N̄`,
  `t⁻¹ K_M t = K_M` and the neighbourhood-basis properties. For a compact open `K` with only an
  Iwahori decomposition these can fail for a given `t`: a compact open subgroup of `N(F)` need
  not be stable under conjugation by every element of `C_A^+`. Then `a_{t^i,K} = (a_{t,K})^i`
  (V.5.3) is not available. The statements handle this as follows.
  - In `RepresentedCanonicalSectionStatement` the point `t` ranges over `A^+(ε)` for an
    existential `ε`. This `ε` is in general smaller than the source's `ε` (which is chosen
    from `Γ` alone): the statement does not claim the conclusions for every `t` with
    `Γ ⊂ t⁻¹ K_N t`, only for every `t` in some chamber `A^+(ε)`. By
    `RepresentedChamberIwahoriContractionStatement`, a small enough chamber consists of
    contracting elements, and on it the source's argument applies verbatim.
  - In the two VI.9.1 statements, `t ∈ C_A^{++}` is replaced by every `M(F)`-central `g` with
    `IsIwahoriContraction`, as in the published dynamic VI.9.1 statements. By
    `RepresentedChamberIwahoriContractionStatement` (and by the published
    `RepresentedIwahoriContractionStatement`, for large powers of any `t₀ ∈ A^{++}`), such `g`
    exist in the image of `A(F)` for every `K` with an Iwahori decomposition along `P`, so the
    statements are not vacuous on the source's class of `K`. Remark 1 then says that the
    decomposition does not depend on the choice of `g`.
- **`A^+(ε)` versus `C_A^+(ε)`.** `t` ranges over all of `A(F)` with `|α(t)|_F < ε`, not only
  over the lattice image `C_A`. Since `C_A ⊆ A(F)`, the uniform clauses imply those for
  `C_A^+(ε)`. The existence clause asserts only a point of `A^+(ε)`; a point of `C_A^+(ε)` also
  exists (a cocharacter `λ` with `⟨α, λ⟩ > 0` on `Δ`, evaluated at a high power of the
  uniformizer), but is not stated. `A^+(ε)` is the set of VI.9.1 Remark 3 and of the published
  `GeneralizedJacquetContractingRangeStatement`.
- **`ε ≤ 1`.** The statements require `ε ≤ 1`, shrinking `ε` if necessary, so that the
  product of two points of `A^+(ε)` lies in `A^+(ε)`, as the source's proof of the VI.6.1
  Proposition requires ("Alors `tt′` vérifie encore ces hypothèses"). The existence of a point
  of `A^+(ε)` is asserted so that the uniform clauses are not vacuous.
- **The order of choices in VI.6.1.** In the source, `Γ`, hence `ε`, depends on `(π, V)`.
  Accordingly `ε` and `s` are chosen after `ρ`. `ker j ≤ ker C_t` (VI.6.1.2) is implied by
  `ker C_t = ker j` and is kept as a separate clause to record the source's display.
- **Which `b`.** In `RepresentedUniformCompressionStabilizationStatement`, `b` is chosen after
  `K` and `g`, as in the published dynamic statement; the source's `b = b(G, K)` follows from
  the bound clause of `RepresentedGeneralizedJacquetRemarksStatement` together with VI.2.3
  (any bound `c(G, K)` on `dim V^K` over irreducibles serves for every `g`).
- **Stability.** "`A^b` est un endomorphisme stable" is expressed, as in the published
  statements, by constancy from `b` on of the power ranges and kernels, identified with
  `stableImage` and `powerKernelSup`.
- **Not stated.** The localization part of the VI.9.1 Proposition (the localization of `V^K`
  at `A` is `(V_*^K, A|V_*^K)`), as in the published dynamic statement: it is the C.II theorem
  `Langlands.Renard.EndomorphismLocalization.stablePowerImageStatement` applied to the stable
  power. Remark 3 is the published `GeneralizedJacquetContractingRangeStatement`, already in
  this setting. Independence of `s_P^K` from `A` and the presentation is not stated
  separately. It is expected to follow from clauses 4, 5 and 7, `RepresentedChamberIwahoriContractionStatement`
  and Remark 1 of `RepresentedGeneralizedJacquetRemarksStatement`: the range of `s` is the
  stable image of a contracting element, and that stable image does not depend on the
  contracting element.
- **Representations.** Complex, on a carrier in an arbitrary universe `v`; admissibility is
  `Langlands.IsAdmissible`, as in the published VI.6.1 statements.

## Provenance

`RepresentedCanonicalSectionStatement` is a **source** statement: VI.6.1, (VI.6.1.2) and the
Proposition for an arbitrary parabolic and every `K` with an Iwahori decomposition along it,
with the chamber choice explained above. `RepresentedUniformCompressionStabilizationStatement`
and `RepresentedGeneralizedJacquetRemarksStatement` are **source** statements (VI.9.1
Proposition and the end of the proof of the Theorem; bound and Remarks 1–2), with the
contracting element `g` in place of `t ∈ C_A^{++}` as in the published dynamic statements.
`RepresentedChamberIwahoriContractionStatement` is **derived**: it isolates the step, taken
from V.5.2 in the source's proofs, that a small chamber consists of contracting elements for
`K`. For the V.5.2 basis members it is part of V.5.2 (ii)–(iv); for a general `K` it follows
from the "plus généralement" clauses of V.5.2 (iii)–(iv) (see Proof obligations).

## Relation to published statements

- `RepresentedIwahoriContractionStatement` (module
  `Langlands.Representation.Exponents.RepresentedIwahoriDecompositionStatements`) gives
  contracting elements `incG (t₀ ^ r)` for large `r`, for a given `t₀ ∈ A^{++}`.
  `RepresentedChamberIwahoriContractionStatement` gives all of a small chamber, which the
  VI.6.1 Proposition needs (it uses arbitrary points of `C_A^+(ε)` and their products).
- `RepresentedGeneralizedJacquetLemmaStatement` and `RepresentedJacquetLemmaStatement` (same
  module) follow from `RepresentedChamberIwahoriContractionStatement` together with clause 4
  of `RepresentedUniformCompressionStabilizationStatement`, resp. clause 4 of
  `RepresentedCanonicalSectionStatement`, given a split component with a presentation.
  Conversely, the proofs of the present statements use the Jacquet lemmas.
- `RationalPointFamily.UniformCompressionStabilizationStatement` and
  `RationalPointFamily.GeneralizedJacquetRemarksStatement` are the dynamic-parabolic forms of
  the last two statements.
- `GeneralizedJacquetContractingRangeStatement` is VI.9.1 Remark 3 in the present setting.
- `Langlands.Jacquet.StandardCanonicalSectionStatement` (proved) is the VI.6.1 Proposition for
  standard parabolics and `K` with the V.5.2 basis-member conditions; the companion
  `StandardIwahoriCanonicalSectionStatement` (module
  `Langlands.Representation.Jacquet.StandardIwahoriDecompositionStatements`, accepted
  candidate `3c7e8531`) is the same with only the Iwahori decomposition on `K`. Neither is
  imported here, and no implication between them and the present statement is claimed.

## Proof obligations

Nothing is proved here. The intended routes:

- `RepresentedChamberIwahoriContractionStatement`. `K` is compact and `N(F)`, `N̄(F)` are
  closed (`isClosed_pointImage_comp`), so `K_N` and `K_N̄` are compact. Apply the published
  `SplitComponentOppositeContractionStatement` with `C = K_N`, `C̄ = K_N̄`, `L = K`; this
  gives `ε₀ > 0` such that every `t ∈ A^+(ε₀)` has `t K_N t⁻¹ ⊆ K` and `t⁻¹ K_N̄ t ⊆ K`; since
  `incG t ∈ M(F)` normalizes `N(F)` and `N̄(F)`, this is `upper` and `lower`. Take
  `ε = min(ε₀, 1)`. `mem_levi` and `levi` hold because `incG` takes values in the centre of
  `M(F)` (`splitComponentPointsMap_mem_center`); `factor` is the hypothesis. For `exhaust`
  apply the same statement to `C = {x}`; for `contract` apply it to `C̄ = K_N̄` and the given
  open subgroup `L`. In both cases `|α(t^s)|_F = |α(t)|_F^s → 0` because `|α(t)|_F < ε ≤ 1`,
  so `t^s` lies in the chamber given by that application for large `s`. Nonemptiness: a
  cocharacter `λ` with `⟨α, λ⟩ > 0` for `α ∈ Δ` (the restrictions `Δ` are linearly
  independent) gives `t₀ = λ(ϖ)` with `|α(t₀)|_F < 1`, and a power of `t₀` lies in `A^+(ε)`.
- `RepresentedCanonicalSectionStatement`. Take `ε₀` from the previous statement. Since
  `V^K ∩ ker j` is finite-dimensional, and `N(F)` is the increasing union of the compact open
  subgroups `g^{-r} K_N g^r` for a contracting `g = incG t₀` (`exhaust`), there is a compact
  open `Γ ⊆ N(F)` with `e_Γ v = 0` on `V^K ∩ ker j` (III.2.9). Apply
  `SplitComponentOppositeContractionStatement` with `C = Γ` and `L = K` to get `ε₁` with
  `t Γ t⁻¹ ⊆ K_N` on `A^+(ε₁)`, and set `ε = min(ε₀, ε₁)`. For `t ∈ A^+(ε)` the element
  `incG t` is contracting, so the Library's proved lemmas apply:
  `compressedAction_mul_of_factor` (V.5.3), `mk_compressedAction_of_iwahoriContraction`
  ((VI.6.1.1)), `powerKernelSup_eq_ker_of_iwahoriContraction`,
  `stableImageJacquetMap_bijective_of_iwahoriContraction` and
  `fixedJacquetMap_surjective_of_iwahoriContraction` (module
  `Langlands.Representation.Jacquet.IwahoriContractionAdmissibility`). The inclusion
  `Γ ⊆ t⁻¹ K_N t` gives (VI.6.1.2); the source's dimension count gives clauses 2–4.
  Products and powers of points of `A^+(ε)` stay in `A^+(ε)` (`ε ≤ 1`), so the source's
  argument shows that `range C_t` and `ker C_t` do not depend on `t`; with `C_t^r = C_{t^r}`
  this gives clauses 5–6, and `s` is the inverse of `j` on the common range (clauses 7–8).
- `RepresentedUniformCompressionStabilizationStatement`. Clauses 1–2: transport the published
  dynamic `RationalPointFamily.UniformCompressionStabilizationStatement` along a cocharacter
  realizing `P` and `M` (the `realization` field of a presentation from the proved
  `parabolicRootPresentationExistence`, with a split component of `M`), identifying the
  supplied radicals with the dynamic ones (`pointImage_radical_eq_dynamic`, module
  `Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityReduction`).
  Clause 3 is the proved `powerKernelSup_eq_ker_of_iwahoriContraction`. Clause 4 follows from
  clauses 1–3 as in the proof of `stableImageJacquetMap_bijective_of_iwahoriContraction`,
  which uses finite dimension only to obtain the splitting and the bijectivity of `A` on the
  stable image.
- `RepresentedGeneralizedJacquetRemarksStatement`. Transport the published dynamic
  `RationalPointFamily.GeneralizedJacquetRemarksStatement` in the same way.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Exponents.GeneralizedJacquetRemarksStatements` | the actual-parabolic setting, `pointImage`, `ParabolicRootPresentation`, `CocharacterUniformizer.characterNorm`, `compressedAction`, `stableImage`, `powerKernelSup`, `stableImageJacquetMap`, `CompactCompressionSplits`, `IsIwahoriContraction`, `SmoothRep.IsIrreducible`, `isSmooth_comp`, `Compact.averageMap` (through its imports) |
| `Langlands.Representation.Exponents.ArbitraryParabolic` | `pointImage`, `pointImage_le_normalizer` |
| `Langlands.Representation.Jacquet.CompressedImageLift` | `compressedImageJacquetMap`, `compressedImageLift` |
| `Langlands.Representation.Smooth.Definitions` | `IsSmooth`, `Langlands.IsAdmissible` |
