# Actual derived unit on a complex of acyclic terms

Authors: Worker 595 (statement design and initial documentation), Worker 310
(interface verification and expanded documentation).

`Langlands.Cohomology.AcyclicTermsDerivedUnitStatement` is an internal comparison
proposition for arbitrary abelian categories with chosen derived categories,
with enough injectives in the source. For an additive left exact functor `F`
and a bounded-below integer-indexed cochain complex `K`, assume each term of
`K` is acyclic for every positive classical right derived functor of `F`.
Then Mathlib's actual natural-transformation component
`F.rightDerivedFunctorPlusUnit.app K` is an isomorphism.

The categories have six independent universe parameters: `C : Type u` with
`Category.{v} C` and `HasDerivedCategory.{w} C`, and `D : Type u'` with
`Category.{v'} D` and `HasDerivedCategory.{w'} D`. Both are abelian. The remaining
assumptions are `EnoughInjectives C`, `F.Additive`, and
`PreservesFiniteLimits F`; preservation of finite limits expresses left
exactness. The quantifier `K : CochainComplex.Plus C` supplies boundedness below.

Mathlib defines the unit as a natural transformation

```lean
F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶
  DerivedCategory.Plus.Q ⋙ F.rightDerivedFunctorPlus
```

Thus its component at `K` has source
`DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj K)` and target
`F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)`, both in
`DerivedCategory.Plus D`. The source first applies `F` termwise and then
localizes; the target first localizes `K` and then applies the bounded-below
right derived functor. The conclusion concerns this specified morphism, rather
than merely the existence of an isomorphism between its endpoints.

The acyclicity hypothesis is exactly

```lean
∀ (i : ℤ) (q : ℕ), IsZero ((F.rightDerived (q + 1)).obj (K.obj.X i))
```

Here `F.rightDerived n : C ⥤ D` is Mathlib's classical right derived functor,
computed by applying `F` to an injective resolution and taking degree-`n`
cohomology. The index `q + 1` ranges over all positive degrees. The hypothesis
is on the terms `K.obj.X i` only: there is no exactness requirement on `K`, no
restriction on its homology objects, and no requirement that its terms be
injective. The Lean declaration is a `def` returning `Prop`; it supplies no
proof. An exact proof is reserved for a successor task after publication of
this statement.

The provenance is internal: it specifies the missing adapter between Mathlib's
bounded-below derived-functor unit and the Library's classical acyclic-object
infrastructure, rather than transcribing a particular literature statement.
The two imported Mathlib modules
`Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus` and
`Mathlib.CategoryTheory.Abelian.RightDerived` provide the actual unit and the
classical derived functors appearing in its type. The Library lemma
`Langlands.Cohomology.AcyclicComparison.acyclic_map` in
`Langlands.Cohomology.AcyclicResolution.ComparisonProof` suggests a proof through
mapping cones and an injective replacement; this statement neither imports that
proof module nor asserts that the proposed route has been implemented here.

The intended application is the ordinary pushforward of a target injective
resolution: its terms are sections-acyclic while its homology may consist of
nonzero higher direct images. This motivates a comparison requiring only
acyclic terms. This file constructs no geometric pullback and proves no
geometric vanishing or cohomological compatibility law.
