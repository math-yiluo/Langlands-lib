# Renard VI.6.1 Proposition and VI.9.4 for compact open subgroups with an Iwahori decomposition (statements)

Module `Langlands.Representation.Jacquet.StandardIwahoriDecompositionStatements`.
Namespace `Langlands.Jacquet`. Universe parameters: `uF` (the field and group schemes) and
`uV` (the representation spaces).

The module contains three `Prop`-valued definitions and three proved comparison theorems:

- `StandardIwahoriCanonicalSectionStatement`: Renard VI.6.1, (VI.6.1.2) and the Proposition
  (the canonical section `s_P^K`), for a standard parabolic;
- `StandardIwahoriFixedVectorSubquotientGenerationStatement`: Renard VI.9.4, Corollary;
- `StandardIwahoriFixedVectorHeckeEquivalenceStatement`: Renard VI.9.4, Proposition;
- `standardCanonicalSectionStatement_of_standardIwahori`,
  `standardFixedVectorSubquotientGenerationStatement_of_standardIwahori` and
  `standardFixedVectorHeckeEquivalenceStatement_of_standardIwahori`: each new statement
  implies the corresponding published statement.

The three statements are not proved here. There are no new objects.

Worker 4 wrote this unit under the whole-book task `f5d1f399-a1f8-4ab5-a981-90b92abd4857`.
It addresses the framework comparison **F3** of the Chapter VI item ledger
(`notes/renard/item-ledger-vi.md`). The published statements
`StandardCanonicalSectionStatement`, `StandardFixedVectorSubquotientGenerationStatement` and
`StandardFixedVectorHeckeEquivalenceStatement` assume that `K` satisfies the published
`StandardParabolicBasisMember`, that is, the clauses (ii)–(iv) of the V.5.2 Theorem for
members of its neighbourhood basis. The source assumes of `K` only an Iwahori decomposition
(V.5.2 (ii), first sentence). The new statements make the same assertions under the source's
hypothesis. Everything else is copied word for word from the published statements: data,
other hypotheses and conclusions.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. PDF page numbers are
one-based and equal printed page numbers plus six. The author read the following pages,
checking every formula with overbars on the rendered pages:

- V.5.2, Theorem, printed p.123 / PDF p.129, and the second Lemma of V.5.3,
  printed p.124 / PDF p.130;
- VI.6.1, the Theorem (Jacquet lemma), the construction of `s_P^K`, (VI.6.1.2) and the
  Proposition with its proof, printed pp.176–177 / PDF pp.182–183;
- VI.6.3, Lemma, Proposition and Corollary with their proofs, printed pp.178–179 /
  PDF pp.184–185;
- VI.9.4, Corollary and Proposition, printed pp.200–201 / PDF pp.206–207.

**Iwahori decomposition (V.5.2 (ii)).** For a standard parabolic `P = MN` the source writes
"`K = K_N̄ K_M K_N`, `K_N̄ = K ∩ N̄`, `K_N = K ∩ N`, `K_M = K ∩ M`, dite décomposition
d'Iwahori de `K` selon `P`". The next sentence, "De plus, `C_A` normalise `K_M`, `C_A^+`
contracte `K_N` et `C_A^- := (C_A^+)^{-1}` contracte `K_N̄`", and the clauses (iii)–(iv) are
further properties of the members of the basis that the Theorem constructs. They are not
part of the term "décomposition d'Iwahori".

**VI.6.1.** The Theorem assumes "Soit `K` un sous-groupe ouvert compact de `G` admettant une
décomposition d'Iwahori selon `P`". The text then constructs a section of
`j : V^K → V_N^{K_M}`. It chooses a compact open subgroup `Γ` of `N` with `e_Γ · v = 0` for
every `v ∈ V^K ∩ ker j`, and continues: "D'après le théorème V.5.2 (iv), il existe `ε > 0` tel
que pour tout `t ∈ C_A^+(ε)`, `Γ ⊂ t^{-1} K_N t`". This gives
(VI.6.1.2) `V^K ∩ ker j = V^K ∩ V(N) ⊂ ker π(a_{t,K})`, then the isomorphism
`Im π(a_{t,K}) → V_N^{K_M}` induced by `j`, then
`V^K = ker π(a_{t,K}) ⊕ Im π(a_{t,K})`. Writing `V_0^K = ker π(a_{t,K})` and
`V_*^K = Im π(a_{t,K})`:

> **Proposition.** La décomposition `V^K = V_0^K ⊕ V_*^K` obtenue ci-dessus ne dépend pas du
> choix de `t ∈ C_A^+(ε)`. On obtient en inversant la restriction de `j` à `V_*^K` une section,
> ne dépendant que de `P` et `K`, `s_P^K : V_N^{K_M} → V_*^K ⊂ V^K`.

The proof multiplies two such points `t, t'` and uses "le lemme V.5.3,
`a_{t,K} a_{t',K} = a_{tt',K} = a_{t',K} a_{t,K}`".

**VI.9.4.** "Une première conséquence du lemme de Jacquet généralisé est que le corollaire
VI.6.3 est maintenant valide sans l'hypothèse d'admissibilité."

> **Corollaire.** Soit `K` un sous-groupe ouvert compact de `G`, inclus et distingué dans
> `K₀` et admettant une décomposition d'Iwahori selon les sous-groupes paraboliques
> standards. Soit `(π, V)` une représentation lisse de `G` telle que `V^K` engendre `V`.
> Alors tout sous-quotient de `V` est engendré par ses vecteurs fixés par `K`.
>
> **Proposition.** Soit `K` est un sous-groupe ouvert compact de `G`, inclus et distingué
> dans `K₀` et admettant une décomposition d'Iwahori selon les sous-groupes paraboliques
> standards. Alors la sous-catégorie pleine de `M(G)` des représentations engendrées par
> leurs vecteurs `K`-invariants est équivalente à la catégorie des modules unitaires sur
> l'algèbre de Hecke `H(G, K)`.

## The hypothesis on `K`

In every statement `K : OpenSubgroup (rationalPoints G)` is compact
(`IsCompact (K : Set (rationalPoints G))`) and satisfies the published
`HasIwahoriIntersectionDecomposition K.toSubgroup M N N̄`, with
`M = standardLeviPoints i ν J`, `N = standardUnipotentPoints i ν J` and
`N̄ = standardOppositeUnipotentPoints i ν J`. This predicate says that the map
`(K ∩ N̄) × (K ∩ M) × (K ∩ N) → K`, `(x, y, z) ↦ x * y * z`, with the actual multiplication
of `G(F)`, is bijective. That is the source's ordered decomposition `K = K_N̄ K_M K_N`,
together with uniqueness of the factors. Uniqueness is no extra condition for these
subgroups, because `N̄(F) ∩ M(F) N(F) = {1}` and `M(F) ∩ N(F) = {1}`. Nothing else is assumed of `K` in the VI.6.1 statement. The VI.9.4 statements
also keep the published conditions that `K` is contained and normal in `K₀`.

- In `StandardIwahoriCanonicalSectionStatement` the hypothesis `_hIwahori` is this
  decomposition for the one standard index `J` of the statement.
- In the two VI.9.4 statements `_hIwahori` is the decomposition for every
  `J ⊆ simpleRelativeRoots i ν`. That is the source's "selon les sous-groupes paraboliques
  standards". Unlike the published statements, no split component `A` or map `q` is chosen
  for each `J`: the decomposition does not involve them.

`HasIwahoriIntersectionDecomposition` is exactly the first conjunct of the published
`StandardParabolicBasisMember i ν J q K`. The other conjunct, `ContractionAndCofinality`,
contains the normalization of `K ∩ M` by `C_A`, the contraction of `K ∩ N` by `C_A^+` and of
`K ∩ N̄` by `C_A^-` (`WeakChamberContraction`), and the clauses (iii)–(iv) of V.5.2 for the
chambers of `A`. It is not assumed here.

## `StandardIwahoriCanonicalSectionStatement`

The data and conclusions are those of the published `StandardCanonicalSectionStatement`;
its Markdown explains them in full. In short:

- `F` is a nonarchimedean local field of either characteristic, and `G` an actual connected
  reductive group scheme over `Spec F`. `rationalPoints G` has the topology
  `rationalPointTopology F G.X` and the topological group structure
  `rationalPoint_isTopologicalGroup F G`.
- `i : S.toGrp ⟶ G` is a maximal split torus, `ν` a generic cocharacter,
  `J ⊆ simpleRelativeRoots i ν`, `_hstandard` the existence of a standard cocharacter for
  `J`, and `q : A.toGrp ⟶ S.toGrp` a compatible split component
  (`IsCompatibleStandardSplitComponent i ν J A q`).
- `hMN : M ≤ Subgroup.normalizer N` is the algebraic normalization used by the Jacquet
  action.
- `ρ` is an admissible complex representation (`IsAdmissible ρ`) on `V`.

Write `j = fixedJacquetMap ρ N M hMN K.toSubgroup` for the map `V^K → (V_N)^{K ∩ M}` and
`C_t = compressedAction ρ hρ.1 K hK t` for Renard's `π(a_{t,K})` on `V^K`. The conclusion is:
there are `ε` with `0 < ε ≤ 1`, a point of `standardComponentCAepsilon i ν J q ε` (Renard's
`C_A^+(ε)`, so the chamber is nonempty) and a linear map `s` with `j ∘ s = id`, such that for
every `t ∈ standardComponentCAepsilon i ν J q ε`:

1. `ker j ≤ ker C_t` (VI.6.1.2) and `ker C_t = ker j`;
2. `IsCompl (ker C_t) (range C_t)`, the decomposition `V^K = V_0^K ⊕ V_*^K`;
3. `compressedImageJacquetMap ... t ...`, the restriction of `j` to `range C_t`, is
   bijective onto `(V_N)^{K ∩ M}`;
4. `range C_t = stableImage ... t` and `powerKernelSup ... t = ker j`;
5. `range s = range C_t`, and `s` equals `compressedImageLift ... t ... hb` for every proof
   `hb` of the bijectivity in 3.

Since `s` and `ε` are chosen before `t`, the decomposition and the section `s = s_P^K` do not
depend on `t`, which is the Proposition.

## The VI.9.4 statements

The data and conclusions are those of the published
`StandardFixedVectorSubquotientGenerationStatement` and
`StandardFixedVectorHeckeEquivalenceStatement`; their Markdown explains them. In short:
`F`, `G`, `i`, `ν` as above; `_hstandard` for every standard index `J`; a compact subgroup
`K₀` with the Iwasawa factorization `G(F) = M_∅(F) N_∅(F) K₀` (V.5.1 (1)); `K` compact open
with `K ≤ K₀` and `K₀ ≤ Subgroup.normalizer K`, and the Iwahori decompositions above.
"Generated by its `K`-fixed vectors" means: every subrepresentation whose underlying
submodule contains the `K`-fixed vectors is `⊤`.

- `StandardIwahoriFixedVectorSubquotientGenerationStatement`: if `V` in
  `SmoothRep.{0, uF, uV} ℂ (rationalPoints G)` is generated by its `K`-fixed vectors, every
  subquotient `D` of `V` (`SmoothRep.IsSubquotient D V`) is generated by its `K`-fixed
  vectors.
- `StandardIwahoriFixedVectorHeckeEquivalenceStatement`: on the full subcategory `P` of
  smooth representations generated by their `K`-fixed vectors, the functor
  `P.ι ⋙ Langlands.Shimura.LevelHecke.heckeModuleFunctor ℂ K.toSubgroup` is an equivalence
  onto modules over the measure-free Hecke algebra `LevelHeckeAlgebra ℂ K`. The published
  Markdown explains why this ring stands for the source's `H(G, K)`.

## Comparison with the published statements

The three theorems of the module show that each new statement implies the published one.
Given the published hypotheses, the proof passes the same data to the new statement and
replaces the basis-member hypothesis by its first conjunct, the Iwahori decomposition:

- for VI.6.1, `hBasis.1`;
- for VI.9.4, `(hBasis J hJ).choose_spec.choose_spec.2.1` (the published hypothesis is
  `∃ A q, IsCompatibleStandardSplitComponent i ν J A q ∧ StandardParabolicBasisMember i ν J q K`).

So the new statements are at least as strong as the published ones. They cover more
subgroups `K` as soon as some compact open `K` has an Iwahori decomposition but does not
satisfy `ContractionAndCofinality`. The author expects such `K` to exist, because a compact
open subgroup of `N(F)` need not be stable under conjugation by every element of `C_A^+`.
This is not claimed or proved here.

## Why the source's hypothesis suffices

None of the three statements is proved here. This section records why the source's proofs
are expected to work for every `K` with an Iwahori decomposition, so that the statements
are not stronger than the source's results. It describes the expected route, not a Lean
proof.

The source's proofs use, beyond the decomposition, only properties of `K` from V.5.2
(ii)–(iv) for the chamber elements involved. For a compact open `K` the Library already
proves all of them except the contraction of `K ∩ N` and `K ∩ N̄` by the whole weak chamber:

- `IsCompatibleStandardSplitComponent.uniform_containment_and_cofinality` (module
  `Langlands.BruhatTits.SpecialCompact.UniformChamberConsequences`) gives
  `UniformCompactContainment` and `UniformCompactOpenCofinality` (the "plus généralement"
  clauses of V.5.2 (iii)–(iv)) for every compact open subgroup;
- `IsCompatibleStandardSplitComponent.strictChamber_power_basis_and_exhaustion` (module
  `...StrictChamberPowerBasis`) gives the exhaustion and the power neighbourhood bases of
  V.5.2 (iii)–(iv) for every compact open subgroup;
- `IsCompatibleStandardSplitComponent.contractionAndCofinality_of_weak` (module
  `...WeakIwahoriBasisReduction`) combines them with the normalization of `K ∩ M`: a compact
  open `K` satisfies `ContractionAndCofinality` as soon as it satisfies
  `WeakChamberContraction`.

For the VI.6.1 Proposition, apply `UniformCompactContainment` with `Γ = K ∩ N(F)` and
`Γ̄ = K ∩ N̄(F)`. This gives `ε₀ > 0` such that every `t ∈ C_A^+(ε₀)` satisfies
`t (K ∩ N) t⁻¹ ⊆ K ∩ N` and `t⁻¹ (K ∩ N̄) t ⊆ K ∩ N̄`, which is the weak contraction on that
smaller chamber. The source's arguments then apply to `t ∈ C_A^+(ε)` for
`ε ≤ min(ε₀, 1)` also smaller than the source's own `ε`:

- (VI.6.1.2) uses only the decomposition and `Γ ⊂ t⁻¹ K_N t`;
- (VI.6.1.1) uses `t⁻¹ K_N̄ t ⊂ K_N̄` and `t⁻¹ K_M t = K_M`;
- the surjectivity uses the Jacquet lemma (the VI.6.1 Theorem), whose hypothesis on `K` is
  already only the Iwahori decomposition. The companion statement
  `RepresentedJacquetLemmaStatement` (see below) states it in that form. Its proof needs
  the contraction properties only for large powers of one strict chamber element;
- the V.5.3 multiplicativity `a_{t,K} a_{t',K} = a_{tt',K}` uses
  `t K_N t⁻¹ ⊂ K_N` and `t'⁻¹ K_N̄ t' ⊂ K_N̄`.

With `ε ≤ 1`, the product of two points of `C_A^+(ε)` is again in `C_A^+(ε)`, as the
source's proof of the Proposition requires.

For VI.9.4, the source's proof of the Corollary uses:

- the VI.6.3 Lemma, which needs only `G = K₀ P` and `K` normal in `K₀`;
- the VI.6.3 Proposition, which holds for every compact open `K`;
- Corollary VI.2.1 and the `K₀`-conjugacy of parabolics (V.5.1);
- the generalized Jacquet lemma VI.9.1 for `K` with an Iwahori decomposition along the
  standard parabolic considered. The source states VI.9.1 under exactly that hypothesis.
  The companion statement `RepresentedGeneralizedJacquetLemmaStatement` (namespace
  `Langlands.Aubert.General.RepresentedParabolic`, the accepted unit for the comparison F2
  of the same ledger) states it in that form, in the represented-parabolic framework.
  `RepresentedJacquetLemmaStatement`, cited above, is in the same module.

The Proposition follows from the Corollary by the Theorem of I.3.2, which involves no
condition on `K`.

## Scope

Not stated here: the VI.6.1 Proposition for a non-standard parabolic; independence of the
section from the maximal split torus, the compatible split component, the uniformizer or
`K`; the VI.6.3 Corollary in its admissible form, which is a special case of the VI.9.4
Corollary; and the comparisons listed as not stated in the published Markdown of the VI.9.4
statements (the inverse functor, the Haar-measure Hecke algebra).
