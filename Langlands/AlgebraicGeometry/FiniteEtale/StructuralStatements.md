# Structural obligations for geometric finite étale Galois axioms

This module defines exactly three propositions in
`Langlands.AlgebraicGeometry.FiniteEtale`. They separate the structural
obligations needed for `GeometricGaloisFiberFunctor` into finite limits and
coproducts, monomorphisms/epimorphisms/conservativity, and finite group
quotients. The module states these obligations; it proves none of them and
installs no instances for them.

## Source and derived provenance

The geometric source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary draft, Chapter X §3, Definitions (10.25)–(10.26), printed p.150
(PDF p.154), and Theorem (10.28), printed p.151 (PDF p.155). The registered
source is `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Definition (10.25) supplies the finite étale category and geometric point
functor. Definition (10.26) defines its automorphism group for a connected
locally noetherian base, and Theorem (10.28) states the geometric
classification by finite continuous actions.

The three propositions are an internal, derived decomposition of the fields
of `CategoryTheory.PreGaloisCategory` and
`CategoryTheory.PreGaloisCategory.FiberFunctor` in pinned Mathlib
`Mathlib.CategoryTheory.Galois.Basic` (commit
`5ed2965256430c3649e86755f9576b54eca72435`). AV states the geometric
classification, not these exact Lean class fields or this grouping.
The decomposition exposes independent geometric proof obligations: it does
not assume the classification as a premise and does not implement a
derivation from it.

## Common parameters and existing constructions

Each definition explicitly has the same complete parameter list:

```lean
{S : Scheme.{u}} [ConnectedSpace S] [IsLocallyNoetherian S]
{Ω : Type u} [Field Ω] [IsAlgClosed Ω]
(s : Spec (.of Ω) ⟶ S)
(hfin : ∀ Y : Cover S, Finite (Fiber s Y))
```

The connectedness, local noetherianity and algebraic closure hypotheses are
retained in each declaration even where the body does not use them to
elaborate. The common universe agrees with the existing constructions.
`Cover S` is the actual full subcategory of `Over S` consisting of finite
étale morphisms. `Fiber s Y` is the type of morphisms `Over.mk s ⟶ Y.obj`
in the slice. `fiberFunctor s hfin` is the existing functor to `FintypeCat`
whose underlying sets are those fibres and whose maps are postcomposition.
The module imports `Langlands.AlgebraicGeometry.FiniteEtale.Statements` and
does not replace or duplicate these constructions.

The explicit hypothesis `hfin` supplies only the finite-set packaging.
The published theorem `geometricFiberFinite` can supply it under the stated
geometric hypotheses; this module keeps it explicit for compatibility with
`GeometricGaloisFiberFunctor`. No Galois-category, fibre-functor,
action-equivalence, or structural conclusion is an additional premise.

## The three propositions

`GeometricFiniteLimitsCoproducts s hfin` is the right-associated conjunction,
in this exact order, of:

1. `HasTerminal (Cover S)`;
2. `HasPullbacks (Cover S)`;
3. `HasFiniteCoproducts (Cover S)`;
4. `PreservesLimitsOfShape (Discrete PEmpty.{1}) (fiberFunctor s hfin)`;
5. `PreservesLimitsOfShape WalkingCospan (fiberFunctor s hfin)`;
6. `PreservesFiniteCoproducts (fiberFunctor s hfin)`.

Thus it asks for terminal objects, pullbacks and finite coproducts and for
preservation of each by the specified functor. Terminal objects and
pullbacks are the generating limit shapes used by Mathlib's Galois axioms.

`GeometricMonoEpiConservative s hfin` is the right-associated conjunction of:

1. For every monomorphism `i : X ⟶ Y` in `Cover S`, there exist a cover `Z`
   and a morphism `v : Z ⟶ Y` such that
   `Nonempty (IsColimit (BinaryCofan.mk i v))`.
2. `Functor.PreservesEpimorphisms (fiberFunctor s hfin)`.
3. `(fiberFunctor s hfin).ReflectsIsomorphisms`.

The first conjunct uses the given monomorphism as the first coproduct
inclusion, expressing that it identifies its source with a direct summand
of its target. The second preserves categorical epimorphisms. The third
says that any morphism of covers whose image under the functor is an
isomorphism is itself an isomorphism.

`GeometricFiniteGroupQuotients s hfin` asserts, for every `G : Type u` with
`[Group G] [Finite G]`, the conjunction

```lean
HasColimitsOfShape (SingleObj G) (Cover S) ∧
PreservesColimitsOfShape (SingleObj G) (fiberFunctor s hfin)
```

These are colimits of all diagrams indexed by the one-object category of
the finite group, encoding the existence and preservation of finite group
quotients. The group universe is exactly `u`, as in the hom universe used
by the imported Galois class fields.

## Relationship to the final geometric target

The first proposition supplies `PreGaloisCategory.hasTerminal`,
`hasPullbacks`, and `hasFiniteCoproducts`, together with the three
corresponding preservation fields of `FiberFunctor`. The second supplies
`monoInducesIsoOnDirectSummand`, `preservesEpis`, and `reflectsIsos`.
The third supplies `hasQuotientsByFiniteGroups` and
`preservesQuotientsByFiniteGroups`.

Together their conclusions are the structural data needed to construct
`PreGaloisCategory (Cover S)` and a fibre-functor witness for the specific
`fiberFunctor s hfin`, and hence to obtain the existing
`GeometricGaloisFiberFunctor s hfin` target. That assembly and the geometric
proofs of the three propositions are separate obligations. No such
assembly, geometric classification, or action equivalence is proved here.
