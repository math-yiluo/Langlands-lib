# Derived association for varying finite geometric covers

This internal construction takes the actual exact varying-cover association
functor to the unbounded derived categories. It constructs its comparison with
associated cochain complexes, single-degree objects and homology, and compares
exact cover evaluation with association at a chosen cover. These are functors
and natural isomorphisms on the actual localizations, including all derived
morphisms.

## Inputs and conventions

Fix a genuine scheme `X : Scheme.{u}`, a commutative ring `R : Type u`, a category
`J` with independent object and morphism universes `uJ` and `vJ`, and an actual
group diagram `D : J ⥤ GrpCat.{u}`. A geometric diagram
`Y : EquivariantDiagram D X.Etale` supplies the covers, actions and equivariant
transition maps. The hypothesis

```text
hY : ∀ j, IsFiniteGeometricTorsor X (Y.action j)
```

is required at every index. The predicate from `Etale.lean` means that the deck
group is finite, the structure map is finite, surjective and étale, and any two
geometric lifts over the same base map differ by a unique deck translation.
These are hypotheses on supplied geometry, rather than existence conclusions.
The coefficient modules and deck-group carriers share universe `u` with the
scheme and ring. The modules are arbitrary; no coefficient finiteness, topology,
smoothness or invertibility of deck-group orders is imposed.

Write

```text
C = EquivariantDiagram D (ModuleCat.{u} R)
S = Sheaf X.smallEtaleTopology (ModuleCat.{u} R)
B = J ⥤ S
A = etaleAssociatedVaryingSystemFunctor X Y hY : C ⥤ B
E_j = (evaluation J S).obj j : B ⥤ S
A_j = etaleAssociatedAt X Y j : C ⥤ S.
```

These are the existing coefficient and genuine small-étale sheaf categories.
Their abelian structures are inferred from the published project and Mathlib
instances. `A` and `A_j` are additive and preserve finite limits and colimits by
the published `VaryingCoverExact` constructions. `E_j` is exact by the usual
pointwise functor-category constructions.

The module uses independent choices `HasDerivedCategory.{wC} C` and
`HasDerivedCategory.{wS} B`, and, in the evaluation section,
`HasDerivedCategory.{wE} S`. Each is a genuine Mathlib localization of all
integer-indexed cochain complexes at quasi-isomorphisms. Mathlib supplies its
standard choice at the maximum object/morphism universe; no derived-morphism
smallness result is assumed. Derived homology is the existing cochain homology
functor `H^q` for `q : ℤ`. Shifts and distinguished triangles use Mathlib's
conventions. There is no boundedness or enough-injectives assumption.

## Constructed derived association

`etaleAssociatedVaryingDerivedFunctor` is `A.mapDerivedCategory`, denoted `Aᴰ`.
The published finite-preservation proofs enable Mathlib's actual localization
construction. Instances provide `Aᴰ.CommShift ℤ` and `Aᴰ.IsTriangulated` by
specializing Mathlib's exact-functor construction.

`etaleAssociatedVaryingDerivedFactors` is the natural isomorphism

```text
Q_C ⋙ Aᴰ ≅ A.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q_B.
```

The right-hand complex functor is the published
`etaleAssociatedVaryingComplexFunctor X Y hY (ComplexShape.up ℤ)`, with its actual
associated terms, differentials and cover transitions. The accompanying
`_naturality` equation states, for every coefficient chain map `f : K ⟶ L`,

```text
Aᴰ(Q_C(f)) ≫ factors_L = factors_K ≫ Q_B(A_complex(f)).
```

`etaleAssociatedVaryingDerivedSingleIso q` specializes
`mapDerivedCategorySingleFunctor`: placing a coefficient diagram in degree `q`
and applying `Aᴰ` agrees naturally with applying `A` and placing the resulting
sheaf diagram in the same degree.

## Homology and its actual maps

`etaleAssociatedVaryingDerivedHomologyIso q`, written `α`, is the constructed
natural isomorphism

```text
Aᴰ ⋙ H_B^q ≅ H_C^q ⋙ A.
```

It specializes the published `Langlands.Cohomology.exactDerivedHomologyIso`.
That construction descends the canonical complex-homology comparison through
localization. No comparison is supplied as an additional input.

The lemma `_hom_app_Q_obj` identifies this descended comparison on every cochain
representative `K`. If `λ_B : Q_B ⋙ H_B^q ≅ H_complex,B^q` and `λ_C` are the
standard derived-homology factorization isomorphisms, and `β_K` is the published
`etaleAssociatedVaryingHomologyIso` on `K`, its formula is

```text
α_(Q_C K) = H_B^q(factors_K) ≫ λ_B,A_complex(K) ≫ β_K ≫ A(λ_C,K⁻¹).
```

The proof specializes the generic representative-recovery equation, unfolds its
canonical composition and the existing complex comparison, and finishes by
definitional equality. Thus it retains the published canonical homology map.

The lemma `_naturality` applies to every morphism `f : K ⟶ L` in `DerivedCategory C`,
with no requirement that `f` be represented by an ordinary chain map:

```text
H_B^q(Aᴰ(f)) ≫ α_L = α_K ≫ A(H_C^q(f)).
```

The lemma `_transition` retains the actual cover maps. For `a : i ⟶ j` in `J`,

```text
(H_B^q(Aᴰ K))(a) ≫ (α_K)_j
  = (α_K)_i ≫ (etaleAssociatedTransition X Y hY a)_(H_C^q K).
```

Both equations are naturality of the already constructed isomorphism, at the
outer coefficient category and inner cover category respectively. Their
`reassoc` attributes also provide postcomposed versions.

## Exact cover evaluation

`etaleAssociatedAtDerivedFunctor j` is the actual `A_j.mapDerivedCategory`,
denoted `A_jᴰ`, using the published exactness proof at that cover. It also has
instances commuting with integer shifts and preserving distinguished triangles.

`etaleAssociatedVaryingDerivedEvaluationIso j` constructs

```text
Aᴰ ⋙ E_jᴰ ≅ A_jᴰ.
```

It uses Mathlib's `mapDerivedCategoryCompIso A E_j`. The ordinary composite
`A ⋙ E_j` is definitionally the actual `A_j`: both its objects and its maps
are the chosen cover's associated objects and maps. This is an isomorphism of
functors from the full derived coefficient category to the derived sheaf
category. The target of `Aᴰ` itself remains the derived category of sheaf
diagrams, not a replacement by a diagram of derived objects.

`etaleAssociatedVaryingDerivedEvaluationHomologyIso q j` constructs

```text
(Aᴰ ⋙ E_jᴰ) ⋙ H_S^q ≅ H_C^q ⋙ A_j.
```

Its composition first uses the generic exact-derived-homology comparison for
`E_j`, then evaluates `α`, and finally uses the existing ordinary association
evaluation isomorphism. If `γ_j : E_jᴰ ⋙ H_S^q ≅ H_B^q ⋙ E_j` is that generic
comparison, the lemma `_hom_app` proves the exact component formula

```text
evaluationHomology_K = (γ_j)_(Aᴰ K) ≫ (α_K)_j.
```

The proof unfolds the composition and identity evaluation components, removes
identity composites and uses definitional equality. Naturality of the
constructed functors and isomorphisms includes every derived morphism.

## Provenance and scope

This is an internal specialization and composition of published project
constructions in `VaryingCoverExact.lean` and `ExactDerivedHomology.lean`, and
Mathlib's `Algebra/Homology/DerivedCategory/ExactFunctor.lean` and
`DerivedCategory/HomologySequence.lean`. Exactness has already been proved for
association on the supplied finite geometric torsors; the derived functor and
all displayed comparisons are constructed from it. No new external-source
assertion is made. No inverse-limit or finiteness theorem from the transitive
imports is used in this unit.

The construction does not supply the actual Harris scheme or its torsors, global
or compactly supported sections, cohomology of a space, derived completion,
infinite-limit interchange, smooth or Galois actions, uniformization or a
geometric comparison theorem. Those remain obligations of the broad Harris
framework and its separately owned prerequisites. This unit provides actual
derived associated coefficients on supplied genuine geometry.
