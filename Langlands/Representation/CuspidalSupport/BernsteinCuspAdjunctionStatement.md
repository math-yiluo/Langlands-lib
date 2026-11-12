# The functors `I` and `R` of the Bernstein decomposition: statement

Module `Langlands.Representation.CuspidalSupport.BernsteinCuspAdjunctionStatement`.
Namespace `Langlands.CuspidalSupport`.
Entry proposition `BernsteinCuspAdjunctionStatement`. Nothing is proved here.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read VI.7.2, printed pp.181–184 / PDF pp.187–190. The assertion
stated here is the second Lemma of VI.7.2, printed p.182 / PDF p.188.

Before the Lemma, Renard defines (printed p.182):

> Définissons Cusp(`G`) comme le produit sur les sous-groupes paraboliques
> standards `P = MN` de `G` des catégories `M(M)_sc`. Définissons alors les
> foncteurs `I : Cusp(G) → M(G)`, `(ρ_M, W_M)_P ↦ ⊕_P i_P^G(ρ_M, W_M)` et
> `R : M(G) → Cusp(G)`, `(π, V) ↦ (r_P^G(π, V)_sc)_P` où par `r_P^G(π, V)_sc`
> on entend la partie cuspidale de la représentation `r_P^G(π, V)`.

> **Lemme.** (i) Le foncteur `R` est l'adjoint à gauche du foncteur `I`.
> (ii) `R` est exact, fidèle, et préserve les représentations de type fini. Le
> foncteur `I` est exact et fidèle.
> (iii) Pour toute représentation `(π, V)` dans `M(G)`, le morphisme
> d'adjonction `α_V : (π, V) → IR(π, V)` est une injection.

`M(M)_sc` is the full subcategory of supercuspidal representations of `M`
(definition and Remark 1 of VI.2.1, printed p.137 / PDF p.143: all Jacquet
modules along proper, equivalently proper standard, parabolics vanish;
notation on printed p.139 / PDF p.145). By VI.3.5 (printed pp.146–147) it is a
factor of `M(M) = M(M)_sc × M(M)_ind`; the proof of the Lemma uses that "la
projection `M(M) → M(M)_sc` définit aussi un foncteur exact".

## The objects

All objects are published. This file constructs nothing new; `I` and `R` are
composites of published functors, written with `let`. The framework is the
standard-family construction (modules `BernsteinData` and `BernsteinBlock`),
as in the published VI.7.2 statement `BernsteinDecompositionStatements`.

- `F`, `G`, `G(F) = rationalPoints G` with its canonical topology
  `pointTopology`, `[LocallyCompactSpace]`, `[NonarchimedeanGroup]`, and
  `T`, `i`, `ν`, `family : BernsteinStandardFamily i ν` are as in
  `BernsteinDecompositionStatements`. The family records connected
  reductivity, the maximal split torus, a generic cocharacter, finiteness of
  the simple roots, and the semidirect decompositions and closedness of the
  actual standard parabolics, Levis and unipotent radicals.
- The standard parabolic subgroups `P = MN` are indexed by the finite sets
  `J : Finset (SimpleRoot i ν)`: `P_J = parabolic i ν J`, `M_J = levi i ν J`,
  `N_J = unipotent i ν J`. They form a finite family because the simple roots
  are finite (`family.finiteSimpleRoots`).
- `cusp J` is `M(M_J)_sc`: the smooth representations `W` of the literal
  standard Levi subgroup `M_J(F)` satisfying the published
  `Langlands.Aubert.General.IsLeviCuspidal`, i.e. the Jacquet modules of `W`
  along the proper standard parabolics `P_I ∩ M_J` (`I ⊊ J`) of `M_J` vanish.
  This is Renard's definition of supercuspidality, tested on standard
  parabolics as allowed by Remark 1 of VI.2.1. The same predicate defines the cuspidal data of the
  standard family.
- `Cusp(G)` is the product category
  `∀ J, (cusp J).FullSubcategory` (Mathlib's `CategoryTheory.Pi`).
- `jac J` is the published normalized Jacquet functor
  `normalizedJacquetFunctor (unipotent i ν J) (levi i ν J) …`, which is
  `r_{P_J}^G`.
- `Ifun` is `I`: on each factor, the inclusion `(cusp J).ι` followed by the
  published normalized induction
  `normalizedInductionFunctor (family.decomposition J) (family.closedUnipotent J)`,
  which is `i_{P_J}^G`. Mathlib's `Functor.pi` assembles these into a functor
  to the product category `Finset (SimpleRoot i ν) → M(G)`; then
  `piEquivalenceFunctorDiscrete` passes to `Discrete (Finset (SimpleRoot i ν)) ⥤ M(G)`,
  and `colim` takes the coproduct. The coproduct is finite. It exists because
  `SmoothRep ℂ G(F)` is abelian (published instance
  `Langlands.SmoothRep.abelian`).
- `sc J` is a functor `M(M_J) ⥤ M(M_J)_sc` with an adjunction
  `sc J ⊣ (cusp J).ι`: a cuspidal-part functor `W ↦ W_sc`.
- `R` is `Functor.pi' fun J => jac J ⋙ sc J`, i.e.
  `V ↦ (r_{P_J}^G(V)_sc)_J`. This is Renard's `R`.

## The Lean statement

`BernsteinCuspAdjunctionStatement` says: for all the data above,

1. for every `J`, the inclusion `(cusp J).ι` has a left adjoint `sc J`;
2. for every family `sc` of functors with adjunctions `sc J ⊣ (cusp J).ι`, and
   `R` built from `sc` as above:
   - (i) `Nonempty (R ⊣ Ifun)`;
   - (ii) `R.Faithful`; for every short exact sequence `A → B → C` of smooth
     representations (`SmoothRep.IsShortExact`: injective, surjective,
     range = kernel), every component `R(A)_J → R(B)_J → R(C)_J` is short exact;
     if `V` is of finite type (`Module.Finite` over `MonoidAlgebra ℂ G(F)`),
     every component `R(V)_J` is of finite type over `MonoidAlgebra ℂ M_J(F)`;
     `Ifun.Faithful`; and `Ifun` sends componentwise short exact sequences to
     short exact sequences;
   - (iii) for every adjunction `adj : R ⊣ Ifun` and every `V`, the unit
     morphism `adj.unit.app V : V ⟶ IR(V)` is injective.

## Formal choices

- **The cuspidal part.** Renard takes the projection onto the factor `M(M)_sc`
  of the VI.3.5 decomposition. The statement uses instead any left adjoint
  `sc J` of the inclusion. Given the decomposition, the projection is such a
  left adjoint, since there are no nonzero morphisms from the `M(M)_ind`
  component to a cuspidal representation. Conversely any two left adjoints
  are isomorphic, so the properties in (i)–(iii) do not depend on the choice.
  Clause 1 asserts that such a left adjoint exists. This is a consequence of
  VI.3.5 that the Lemma needs in order to define `R`. Clause 2 quantifies over
  all choices.
- **Exactness and faithfulness.** "Exact" is stated as preservation of short
  exact sequences of actual intertwining maps, as in the published VI.1
  exactness statements, with `Cusp(G)` handled componentwise. Short exactness
  in a product of full subcategories is componentwise. Each `M(M)_sc` is
  closed under subquotients (Renard, p.139), so its short exact sequences are
  those of `M(M)`. "Fidèle" is `Functor.Faithful`.
- **Finite type.** "Type fini" is finite generation of the carrier as a module
  over the group algebra, as in the published VI.1.3 statement
  `JacquetFiniteGenerationOfCompactQuotientStatement` (module
  `Langlands.Representation.Aubert.General.JacquetFiniteGenerationStatement`).
  For `Cusp(G)` it means that every component is of finite type.
- **The adjunction morphism.** Renard's `α_V` is the unit of his adjunction.
  An adjunction `R ⊣ I` is not unique, so (iii) is stated for every adjunction.
  Any two units differ by an automorphism of `IR(V)`, so this is equivalent to
  the statement for one adjunction.
- **Universes.** All carriers, of `G`-representations and of the Levi
  representations, lie in `Type (max uF uV)`. Normalized induction enlarges
  carriers to `max uF uV` (`normalizedInductionFunctor`). With Levi carriers
  already in `max uF uV`, `I` lands in the same universe as `R` starts from,
  as an adjunction requires. The published `bernsteinSaturatedBlockProperty`
  uses the same saturated universe. Renard's categories have no universe restriction.
- **`P = G`.** The index `J` ranges over all finite sets of simple roots,
  including the set of all simple roots. That index corresponds to Renard's
  term `P = G`, whose component of `R(V)` is the cuspidal part of `V`.

## Relation to existing work

- Worker 1751's published `RationalCuspidalInducedEmbeddingStatement`
  (module `Langlands.Representation.CuspidalSupport.RationalCuspidalInducedEmbeddingStatement`)
  states the consequence drawn in the paragraph after the Lemma: every smooth
  representation embeds in a finite direct sum of normalized inductions of
  cuspidal representations of the standard Levis. It does not state the
  functors, the adjunction, exactness or faithfulness. Statement (iii) here,
  with clause 1, implies the existence of such an embedding at the saturated
  universe. This implication is not formalized.
- Worker 6's published `RationalCuspidalCategory` defines the factors of the
  VI.3.5 decomposition and the decomposition predicate. It proves no
  decomposition. Clause 1 here is a consequence of that decomposition.
- The published `BernsteinDecompositionStatements` (Worker 1222) states the
  Theorem and first Lemma of VI.7.2. Its Markdown lists this second Lemma as a
  remaining obligation, which this unit addresses.

## Scope

This file states the second Lemma of VI.7.2 and proves nothing. Proofs belong
to a separate `lean.proof@1` task targeting
`BernsteinCuspAdjunctionStatement`. Renard's route: compose the
Frobenius reciprocity of `r_P^G ⊣ i_P^G` with the adjunctions `sc ⊣ ι`, and use
finiteness of the set of standard parabolics to replace the product of Hom
groups by Homs into the coproduct (i); exactness of `r_P^G`, `i_P^G` and of
the cuspidal-part projection (ii); faithfulness of `R` from a minimal
standard parabolic with `r_P^G(V) ≠ 0`, whose Jacquet module is cuspidal
(proof of VI.2.1 Corollary), and finite type from VI.1.3; for (iii), the
kernel `V′` of `α_V` satisfies `α_{V′} = 0`, which forces `R(V′) = 0` and hence
`V′ = 0` by faithfulness.

Not stated here: (VI.7.2.1) (induction commutes with the decomposition of a
supercuspidal representation into inertia components) and the remaining steps
of the proof of the Theorem. VI.7.3 (Bernstein decomposition and
induction/restriction) is not stated either.

The file imports `Langlands.Representation.CuspidalSupport.BernsteinBlock`,
`Langlands.Representation.Smooth.FiniteLengthGrothendieck` (for
`SmoothRep.IsShortExact`), `Langlands.Representation.Category.Abelian`, and
Mathlib's `CategoryTheory.Pi.Basic`, `CategoryTheory.Discrete.Basic` and
`CategoryTheory.Adjunction.Basic` (environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`).
