# Renard VI.8.2–VI.8.3: flatness and admissibility of induction and Jacquet modules of families

Author: Worker 709. Module
`Langlands.Representation.Families.RenardFamilyParabolicFlatnessStatements`,
namespace `Langlands.Renard.AlgebraicFamily`. It contains three **statements**, the
closed `Prop`-valued definitions `InductionFlatStatement` and
`InductionAdmissibleStatement` (universe parameters `u', uB', uE'`) and
`JacquetFlatStatement` (universe parameters `u', uB', uV'`), and their closed
conjunction `ParabolicFlatnessStatements` (universe parameters
`u', uB', uE', uV'`). It proves nothing.

## Original source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated **9 July 2026**:

- VI.8.2, "`(G, B)`-modules et induction": the opening paragraph, printed p. 189 /
  PDF p. 195, continued on printed p. 190 / PDF p. 196, and the Lemma that follows
  it on PDF p. 196.
- VI.8.3, "`(G, B)`-modules et restriction": the opening paragraph, printed p. 191 /
  PDF p. 197.
- `(G, B)`-modules and admissibility: VI.8.1, printed pp. 187–189 /
  PDF pp. 193–195.

Literature ID `renard-2026-representations-groupes-reductifs-padiques`, file
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 709 read PDF pages 193–197.

The passages are:

- (I), PDF pp. 195–196. For a parabolic `P = MN` and an `(M, B)`-module `(σ, E)`,
  after `B` is made to act on the values of the functions: "Pour montrer que
  `i_P^G(σ, E)` est un `(G, B)`-module, il reste à montrer que c'est un `B`-module
  plat." The argument uses the VI.8.1 Remark (flatness can be tested on the
  `K`-fixed vectors for compact open `K`) and the description (VI.8.2.1)
  `i_P^G(E)^K ≃ ⊕_{g ∈ Ω} E^{K_M^g}` over a finite set `Ω` of representatives of
  `P\G/K`, and concludes "Ceci nous montre que nous avons un foncteur
  `i_P^G : M(M, B) → M(G, B)`."
- (L2), PDF p. 196: "Il est alors facile de généraliser le lemme III.2.3 :
  Lemme. Soit `P = MN` un sous-groupe parabolique de `G`. Alors le foncteur
  `i_P^G : M(M, B) → M(G, B)` envoie les modules admissibles sur des modules
  admissibles."
- (J), PDF p. 197. For a `(G, B)`-module `(π, V)`: "Montrons que `r_P^G(V)` est un
  `B`-module plat." As a vector space `r_P^G(V) = V_N = V/V(N) = V ⊗_{H(N)} ℂ`,
  so `E ⊗_B r_P^G(V) ≃ (E ⊗_B V) ⊗_{H(N)} ℂ` for every `B`-module `E`; both
  functors are exact, and "Ainsi nous obtenons un foncteur
  `r_P^G : M(G, B) → M(M, B)`."

By VI.8.1, a `(G, B)`-module is a smooth representation on a flat `B`-module
whose `G`-action commutes with `B`, and it is admissible if moreover `V^K` is a
finitely generated `B`-module for every compact open subgroup `K`. `B` is, as
throughout VI.8, "une `ℂ`-algèbre commutative noethérienne de type fini réduite".

## Lean model

The group-theoretic binders are those of the published VI.1.3 statement
[LeviJacquetFiniteTypeStatement](../Exponents/LeviJacquetFiniteTypeStatement.md)
and of the sibling (P2)/(P3) statements:

- a field `k : Type u'` with `[Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]`, so any nonarchimedean local
  field of any characteristic;
- a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. The
  statements install `hG.isAffineHom` and the canonical topology
  `RationalPointFamily.pointTopology` on `rationalPoints G`, and assume
  `[LocallyCompactSpace (rationalPoints G)]` and
  `[NonarchimedeanGroup (rationalPoints G)]`;
- in the two induction statements, every actual rational parabolic
  `p : P ⟶ G` (`hp : IsParabolicSubgroup p`) with rational Levi `l : M ⟶ P`
  (`hl : IsRationalLeviSubgroup l`) and matching geometric unipotent radical
  `r : U ⟶ P` (`hr`, and `hmul : IsIso (subgroupMultiplication l r)`). They also
  install `hl.isConnectedReductive.isAffineHom` and the canonical topology
  `leviPointTopology l hl` on `rationalPoints M`, which the smoothness hypothesis
  on `σ` and the compact open subgroups of `M(F)` use. `P = G` is allowed.

The coefficient ring is `B : Type uB'` with `[CommRing B] [Algebra ℂ B]
[IsNoetherianRing B] [Algebra.FiniteType ℂ B] [IsReduced B]`, the standing
hypothesis of VI.8.

A family over `B` is a `B`-linear representation, as in the published
[RenardFamilyStatements](RenardFamilyStatements.md). An `(M, B)`-module is
`σ : Representation B (rationalPoints M) E` with `IsSmooth σ` and
`Module.Flat B E`; a `(G, B)`-module is
`ρ : Representation B (rationalPoints G) V` with `IsSmooth ρ` and
`Module.Flat B V`. A compact open subgroup is `K : OpenSubgroup _` with
`IsCompact (K : Set _)`, and its fixed vectors are the published
`fixedVectors ρ K.toSubgroup`, as in `RenardFamilyStatements`.

The functors are the definitions of
[RenardFamilyParabolicFunctors](RenardFamilyParabolicFunctors.md):

- `i_P^G(E)` is `LeviInduced p l r hp hr hl hmul σ` with the action
  `leviInducedRepresentation p l r hp hr hl hmul σ`: Renard's normalized induction
  on smooth functions `f` from `G(F)` to `E`, with the covariance (VI.1.2.3) and with
  `B` acting on the values. That module's Markdown explains Renard's reciprocal
  `δ_P` convention;
- the `B`-module of `r_P^G(V)` is `Jacquet ρ (pointImage (r ≫ p))`, the
  coinvariants `V/V(N)` of the unipotent radical image, Renard's `V_N`.

## Declarations

| Declaration | Source | Statement |
| --- | --- | --- |
| `InductionFlatStatement` | VI.8.2 opening paragraph, PDF pp. 195–196 | For smooth `σ` on a flat `B`-module `E`, `Module.Flat B (LeviInduced p l r hp hr hl hmul σ)` |
| `InductionAdmissibleStatement` | VI.8.2 Lemma, PDF p. 196 | For smooth `σ` on a flat `E` with `fixedVectors σ K` finitely generated over `B` for every compact open `K` of `M(F)`, `fixedVectors (leviInducedRepresentation … σ) K` is finitely generated over `B` for every compact open `K` of `G(F)` |
| `JacquetFlatStatement` | VI.8.3 opening paragraph, PDF p. 197 | For smooth `ρ` on a flat `B`-module `V`, `Module.Flat B (Jacquet ρ (pointImage (r ≫ p)))` |
| `ParabolicFlatnessStatements` | — | The conjunction of the three |

## Correspondence notes

1. (I) is the claim that `i_P^G(σ, E)` is a `(G, B)`-module. Its other
   conditions are definitional in the model: `B` acts on values,
   `leviInducedRepresentation` is `B`-linear, and it is smooth by the
   `isSmooth_inducedRepresentation` law of the functors module. So only flatness
   is stated.
2. (L2) concludes that `i_P^G(E)` is an admissible `(G, B)`-module, which is
   flatness together with finite generation of the compact-open fixed modules.
   Flatness is (I), so `InductionAdmissibleStatement` states only finite
   generation. Its hypotheses are those of an admissible `(M, B)`-module:
   smoothness, flatness and finite generation of every compact-open `E^K`.
3. (J) is the claim that `r_P^G(V)` is a flat `B`-module. Flatness concerns the
   `B`-module `V_N` only, which does not depend on the Levi or on the
   normalization of the `M`-action. So `JacquetFlatStatement` quantifies only over
   the parabolic `p` and its unipotent radical `r`, with no Levi binders and no
   `hmul`. With a rational Levi `l` and `hmul`, the carrier of the published
   `leviJacquetRepresentation p l r hp hr hl hmul ρ` is exactly
   `Jacquet ρ (pointImage (r ≫ p))`, so the statement covers Renard's
   `r_P^G(V)` for every `P = MN`. Dropping the Levi binders makes the statement
   formally more general; the reading is Worker 709's.
4. The source proves the three claims under its standing hypotheses on `B`,
   and the statements keep them. No admissibility is assumed in (I) or (J), and
   no finiteness of `E^K` in (I).
5. The source's functors `i_P^G : M(M, B) → M(G, B)` and
   `r_P^G : M(G, B) → M(M, B)` are not bundled; only the objects are stated to
   be flat.

## Relation to published work

At Library `8b14de0b`, the VI.8 progress note
[algebraic-families-progress](../../../notes/renard/algebraic-families-progress.md)
lists (I), (L2) and (J) with no statement over a general `B`. Results a proof can
use:

- the published `FlatnessCriterionStatement` of `RenardFamilyStatements` (the
  VI.8.1 Remark) and its proved sufficient direction `flat_of_smooth_fixed_flat`,
  recorded in row (R1) of that note, which reduces flatness of a smooth family to flatness of
  its compact-open fixed modules;
- the published `Langlands.Induction.fixedEvaluationEquiv` of
  [FixedVectorModel](../Induction/FixedVectorModel.md), the description
  (VI.8.2.1) of the `K`-fixed vectors of a smooth induced representation over any
  commutative coefficient ring as a finite product indexed by double-coset
  representatives;
- for the universal unramified family only, the flatness and admissibility
  results listed in rows (I) and (L2) of that note.

This module asserts none of them. Proofs of the three statements are separate
work.
