# Separate monomorphism, epimorphism, and conservativity obligations

This module defines three propositions in
`Langlands.AlgebraicGeometry.FiniteEtale`, separating the three conjuncts of
the published `GeometricMonoEpiConservative`. It imports
`Langlands.AlgebraicGeometry.FiniteEtale.StructuralStatements`. These are
statement definitions: the module proves none of the geometric obligations
and introduces no instances.

## Common parameters and constructions

Each declaration explicitly retains this complete parameter list:

```lean
{S : Scheme.{u}} [ConnectedSpace S] [IsLocallyNoetherian S]
{Ω : Type u} [Field Ω] [IsAlgClosed Ω]
(s : Spec (.of Ω) ⟶ S)
(hfin : ∀ Y : Cover S, Finite (Fiber s Y))
```

The parameters remain present even where the body does not use them.
In particular, the monomorphism proposition retains `s` and `hfin`.
All three definitions use the existing `Cover S`, the full subcategory of
`Over S` on finite étale structure morphisms; `Fiber s Y`, the morphisms
`Over.mk s ⟶ Y.obj`; and, where needed, `fiberFunctor s hfin`, the actual
geometric fibre functor to `FintypeCat` with maps given by postcomposition.
The explicit `hfin` supplies finiteness of those fibres.

## Exact propositions

`GeometricMonomorphismComplements s hfin` has body

```lean
∀ {X Y : Cover S} (i : X ⟶ Y) [Mono i],
  ∃ (Z : Cover S) (v : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i v))
```

Thus every categorical monomorphism `i` must be the first inclusion of a
binary coproduct cocone with vertex its given target `Y`. The proposition
asserts the existence of a complementary cover and a colimit witness.

`GeometricEpimorphismPreservation s hfin` has body

```lean
Functor.PreservesEpimorphisms (fiberFunctor s hfin)
```

It asks that the specified functor send categorical epimorphisms of covers
to epimorphisms of finite sets.

`GeometricFiberConservative s hfin` has body

```lean
(fiberFunctor s hfin).ReflectsIsomorphisms
```

It asks that a morphism of covers be an isomorphism whenever its image
under this functor is an isomorphism.

The right-associated conjunction of these propositions, in the order above,
unfolds to exactly `GeometricMonoEpiConservative s hfin`. No assumption
of a Galois category, a fibre-functor class witness, or a continuous-action
equivalence is added. The geometric proofs remain separate obligations.

## Internal provenance and geometric source

This is an internal decomposition of the existing `StructuralStatements`
definition. Its three bodies correspond to
`CategoryTheory.PreGaloisCategory.monoInducesIsoOnDirectSummand` and
`CategoryTheory.PreGaloisCategory.FiberFunctor.preservesEpis` and
`reflectsIsos` in `Mathlib.CategoryTheory.Galois.Basic`, pinned at commit
`5ed2965256430c3649e86755f9576b54eca72435`. Those class fields explain the
choice of obligations; the classes are not hypotheses here.

The geometric context is Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, preliminary draft, Chapter X §3, Definitions
(10.25)–(10.26), printed p.150 (PDF p.154), and Theorem (10.28),
printed p.151 (PDF p.155). Registered source:
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Definition (10.25) specifies finite étale covers and the geometric point
functor; Definition (10.26) uses a connected locally noetherian base.
Theorem (10.28) states the classification by finite continuous actions.
The three exact Lean propositions are derived internal interfaces, not
verbatim assertions of that source, and this module neither proves nor
assumes that classification.
