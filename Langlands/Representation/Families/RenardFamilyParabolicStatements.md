# Renard VI.8.2–VI.8.3: base change commutes with induction; Jacquet modules of finite type

Author: Worker 709. Module
`Langlands.Representation.Families.RenardFamilyParabolicStatements`, namespace
`Langlands.Renard.AlgebraicFamily`. It contains two **statements**, the closed
`Prop`-valued definitions `InductionBaseChangeStatement` (universe parameters
`u', uB', uC', uE'`) and `JacquetFiniteTypeStatement` (universe parameters
`u', uB', uV'`), and their closed conjunction `ParabolicStatements` (universe
parameters `u', uB', uC', uE', uV'`). It proves nothing.

## Original source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated **9 July 2026**:

- VI.8.2, "`(G, B)`-modules et induction": the base-change paragraph, the
  Proposition, its proof and the formula (VI.8.2.2), printed p. 190 /
  PDF p. 196.
- VI.8.3, "`(G, B)`-modules et restriction": the opening paragraph and the
  Proposition, printed p. 191 / PDF p. 197.
- `(G, B)`-modules: VI.8.1, printed pp. 187–189 / PDF pp. 193–195.
- The Proposition of VI.1.3, which VI.8.3 generalizes: printed p. 136 /
  PDF p. 142.

Literature ID `renard-2026-representations-groupes-reductifs-padiques`, file
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 709 read PDF pages 142 and 193–198.

The VI.1.3 Proposition (PDF p. 142) reads: "Soit `(π, V)` une représentation
lisse de type fini de `G`. Alors `(π_N, V_N)` est de type fini. Il en est de même
de `r_P^G(π, V)`", where "de type fini" means generated as a representation of
`G` by finitely many vectors, as its proof shows.

The base-change paragraph (PDF p. 196) takes "une autre `ℂ`-algèbre commutative
noethérienne réduite" `C` and supposes "que `C` soit un `B`-module". It defines the
functor "`M(G, B) → M(G, C)`, `V ↦ V ⊗_B C`". The VI.8.2 Proposition reads: "Le
changement de base commute à l'induction. Plus précisément, si `E` est un
`(B, M)`-module, alors `i_P^G(E) ⊗_B C` est naturellement isomorphe (comme
`(G, C)`-module) à `i_P^G(E ⊗_B C)`." The proof ends with the formula

(VI.8.2.2) `i_P^G(E) ⊗_B C → i_P^G(E ⊗_B C)`, `f ⊗ c ↦ f̃`, where
`f̃(g) = f(g) ⊗ c`,

and "Il est clair que (VI.8.2.2) est un isomorphisme de `(G, C)`-modules."

The VI.8.3 Proposition (PDF p. 197) reads: "Le foncteur
`r_P^G : M(G, B) → M(M, B)` préserve les `B`-modules de type fini." It is
introduced by "La proposition VI.1.3 se généralise alors aux `(G, B)`-modules",
and followed by "Là encore, le point crucial est la compacité de `P\G`, et donc la
finitude de `P\G/K` pour tout sous-groupe ouvert compact `K` de `G`."

## Lean model

The group-theoretic binders are those of the published VI.1.3 statement
[LeviJacquetFiniteTypeStatement](../Exponents/LeviJacquetFiniteTypeStatement.md):

- a field `k : Type u'` with `[Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]`, so any nonarchimedean local
  field of any characteristic;
- a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. The
  statements install `hG.isAffineHom` and the canonical topology
  `RationalPointFamily.pointTopology` on `rationalPoints G`, and assume
  `[LocallyCompactSpace (rationalPoints G)]` and
  `[NonarchimedeanGroup (rationalPoints G)]`;
- every actual rational parabolic `p : P ⟶ G` (`hp : IsParabolicSubgroup p`)
  with rational Levi `l : M ⟶ P` (`hl : IsRationalLeviSubgroup l`) and
  matching geometric unipotent radical `r : U ⟶ P` (`hr`, and
  `hmul : IsIso (subgroupMultiplication l r)`). `P = G` is allowed.

`InductionBaseChangeStatement` also installs `hl.isConnectedReductive.isAffineHom`
and the canonical topology `leviPointTopology l hl` on `rationalPoints M`, which
the smoothness hypothesis on `σ` uses.

The coefficient rings are:

- `B : Type uB'` with `[CommRing B] [Algebra ℂ B] [IsNoetherianRing B]
  [Algebra.FiniteType ℂ B] [IsReduced B]`, the standing hypothesis of VI.8:
  "une `ℂ`-algèbre commutative noethérienne de type fini réduite";
- in `InductionBaseChangeStatement`, `C : Type uC'` with `[CommRing C]
  [Algebra ℂ C] [IsNoetherianRing C] [IsReduced C] [Algebra B C]
  [IsScalarTower ℂ B C]`: a commutative Noetherian reduced `ℂ`-algebra, as in
  the source, which is a `B`-algebra compatibly with its `ℂ`-structure (see
  note 2). It is not assumed of finite type, as the source does not assume it.

A family over `B` is a `B`-linear representation, as in the published
[RenardFamilyStatements](RenardFamilyStatements.md). An `(M, B)`-module is
`σ : Representation B (rationalPoints M) E` with `IsSmooth σ` and
`Module.Flat B E`; a `(G, B)`-module is
`ρ : Representation B (rationalPoints G) V` with `IsSmooth ρ` and
`Module.Flat B V`. These are the two conditions of the VI.8.1 definition.

The functors are the published definitions of
[RenardFamilyParabolicFunctors](RenardFamilyParabolicFunctors.md):

- base change to `C` is `baseChange C`, on the space `C ⊗[B] E`, where `g` acts
  by `1 ⊗ σ(g)`;
- `i_P^G(E)` is `LeviInduced p l r hp hr hl hmul σ` with the action
  `leviInducedRepresentation p l r hp hr hl hmul σ`: Renard's normalized
  induction, on smooth functions `f` from `G(F)` to `E` with the covariance
  (VI.1.2.3), the Levi half modulus being inflated along the projection, and with
  `B` acting on the values. `Induction.eval _ _ f g` is the value `f(g)`. That
  module's Markdown explains Renard's reciprocal `δ_P` convention: the Library
  modulus `c_U` of conjugation on the radical is Renard's `δ_P^{-1}` on the Levi;
- `r_P^G(V)` is `leviJacquetRepresentation p l r hp hr hl hmul ρ`, Renard's
  normalized Jacquet module, a family of `M(F)` over `B`.

## Declarations

| Declaration | Source | Statement |
| --- | --- | --- |
| `InductionBaseChangeStatement` | VI.8.2 Proposition and (VI.8.2.2), PDF p. 196 | For smooth `B`-flat `σ`, there is a `C`-linear equivalence `e : C ⊗[B] i_P^G(E) ≃ i_P^G(C ⊗[B] E)` that intertwines `baseChange C` of the induced action with the induced action of `baseChange C σ`, and satisfies `e (c ⊗ f)(g) = c ⊗ f(g)` for all `c`, `f`, `g` |
| `JacquetFiniteTypeStatement` | VI.8.3 Proposition, PDF p. 197 | For smooth `B`-flat `ρ`, if `ρ.asModule` is finitely generated over `MonoidAlgebra B (rationalPoints G)`, then the normalized Jacquet module `leviJacquetRepresentation … ρ` is finitely generated over `MonoidAlgebra B (rationalPoints M)` |
| `ParabolicStatements` | — | The conjunction of the two |

## Correspondence notes

1. Order of the tensor factors. The source writes `i_P^G(E) ⊗_B C` and
   `E ⊗_B C`; the Lean statement writes `C ⊗[B] i_P^G(E)` and `C ⊗[B] E`, as
   the published `baseChange` and Mathlib's base change do. The two orders are
   identified by the symmetry of the tensor product over the commutative ring
   `B`. Under it the source's `f ⊗ c ↦ f̃`, `f̃(g) = f(g) ⊗ c` becomes
   `c ⊗ f ↦ (g ↦ c ⊗ f(g))`, which is the formula in the statement.
2. "`C` soit un `B`-module". `V ⊗_B C` must be a `C`-module, so `C` is read as
   a commutative `B`-algebra, `[Algebra B C]`; this is reading note 2 of the
   [VI.8 note](../../../notes/renard/algebraic-families-progress.md). The source
   calls `C` a `ℂ`-algebra, and its two `ℂ`-structures are taken to agree,
   `[IsScalarTower ℂ B C]`, as when `B → C` is a morphism of `ℂ`-algebras. The
   normalizing character of `i_P^G(C ⊗_B E)` is the Levi half modulus
   `c_U^{1/2}` (Renard's `δ_P^{-1/2}`) with values in `C`, so this
   compatibility is what makes it the image of the one of `i_P^G(E)`. The
   reading is Worker 709's.
3. "`(B, M)`-module" is the source's misprint for `(M, B)`-module (reading
   note 2 of the VI.8 note). By the VI.8.1 definition it is smooth and flat, and
   the statement assumes both.
4. "Naturellement isomorphe (comme `(G, C)`-module)". The statement asserts a
   `C`-linear equivalence that is `G(F)`-equivariant and is given by
   (VI.8.2.2) on pure tensors. Naturality in `E` is not stated. Because the
   pure tensors `c ⊗ f` generate `C ⊗[B] i_P^G(E)` additively, the formula
   determines `e`, and naturality for a morphism of `(M, B)`-modules follows
   from it; this remark is Worker 709's and is not checked in Lean. The
   statement does not assert that `C ⊗[B] E` is `C`-flat, which the source
   derives before the Proposition.
5. "`B`-modules de type fini" in VI.8.3. Every quotient of a finitely generated
   `B`-module is finitely generated, and `r_P^G(V)` is a quotient of `V`, so
   the literal reading over `B` alone would need neither VI.1.3 nor the
   compactness of `P\G` that the source names as the crucial point. The
   statement therefore reads "de type fini" as for the `(G, B)`-module:
   finite generation under the joint action of `G(F)` and `B`, that is of
   `ρ.asModule` over the group algebra `MonoidAlgebra B (rationalPoints G)`,
   and over `MonoidAlgebra B (rationalPoints M)` for the Jacquet module. This
   is reading note 3 of the VI.8 note, and it is the convention of the
   published VI.1.3 statement for `B = ℂ`. The reading is Worker 709's.
6. Normalization. Only the normalized Jacquet module is stated. The
   unnormalized module `V_N` has the same carrier, and the two actions of
   `m` differ by the unit `c_U(m)^{-1/2} · 1_B` (Renard's `δ_P^{1/2}(m)`), so
   the same vectors generate
   both. This is the argument of the published VI.1.3 statement and is not
   checked in Lean here.
7. Hypotheses not used by the source's arguments are not added: no
   admissibility, finite length or finiteness of `V^K` is assumed, and in
   `JacquetFiniteTypeStatement` no topology or instance is installed on
   `rationalPoints M`, which the conclusion does not need.

## Relation to published work

The VI.8 progress note lists the two Propositions as (P2) and (P3), with no
published statement at Library `8b14de0b`. Results a proof can use:

- (VI.8.2.1), the published `Langlands.Induction.fixedEvaluationEquiv` of
  [FixedVectorModel](../Induction/FixedVectorModel.md): over any commutative
  coefficient ring, the `K`-fixed vectors of the unnormalized `smoothInduced`
  are a finite product of fixed vectors of the inducing representation, indexed
  by double-coset representatives. The source's proof of (P2) uses this
  description.
- For `B = ℂ`, the published `Langlands.Aubert.General.jacquetFiniteGenerationOfCompactQuotient`
  proves the argument of (P3) for an abstract semidirect decomposition with
  compact quotient, and the published `ArbitraryParabolicQuotientCompactStatement`
  (Renard V.5.1 Corollary) states the compactness of `P\G`.
- (C2), the specialization case `C = ℂ` of (P2) for the universal normalized
  induced family, is the published, proved
  `RationalNormalizedInducedSpecializationStatement`. It is a different object
  and is not derived from this module.

This module asserts none of them. Proofs of the two statements are separate
obligations, each of which must prove its declaration unchanged.

## Environment

Environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0 at
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib at
`5ed2965256430c3649e86755f9576b54eca72435`. The project imports are
`Langlands.Representation.Families.RenardFamilyParabolicFunctors` (the functors)
and `Langlands.GroupScheme.Reductive.Basic` (`IsConnectedReductive`). No
construction or axiom is introduced.
