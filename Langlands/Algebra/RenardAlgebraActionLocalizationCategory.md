# The category of compatible algebra actions and the localized structured arrow

Worker 709, for the whole-book task `f5d1f399-a1f8-4ab5-a981-90b92abd4857`,
revision 3. This unit contains definitions and construction lemmas only. All
declarations are in `Langlands.Renard.AlgebraActionLocalization`. It packages
the published B-linear localization as an actual structured arrow in an actual
category. It does not assert that this arrow is universal.

## Original source

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated **9 July 2026**. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`; file
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`;
SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, verified
for this unit. Printed body page = PDF page minus 6. Worker 709 reread these
passages for this unit:

- A.III.1, printed p. 251 / PDF p. 257: a solution `(X, i)` of the right
  universal problem posed by a functor F and an object Y is an object X with a
  morphism `i : Y → F(X)`. For every Z and every `f : Y → F(Z)` there must be a
  unique `g : X → Z` with `F(g) ∘ i = f`.
- A.III.1, example 5, printed p. 252 / PDF p. 258. Objects are pairs
  `(L, a)` with `a ∈ End_k(L)`. Morphisms `(L, a) → (L', a')` are linear maps
  intertwining a and a'. The example gives `(L_a, ã)` with ã invertible and
  `ι : (L, a) → (L_a, ã)`, factoring every morphism to a pair with invertible
  endomorphism. Its final sentence reads: « Si B est une k-algèbre, on peut
  faire la même construction en remplaçant les k-espaces vectoriels par des
  B-modules, et les endomorphismes d'espaces vectoriels par des endomorphismes
  de B-modules. »
- The conventions on printed p. 6 / PDF p. 12. Rings are not assumed unital
  unless stated. Modules over a unital ring are not assumed unital.

This unit constructs the categorical data of that final sentence. The pairs
are B-modules with B-module endomorphisms. The morphisms are B-module maps
intertwining the endomorphisms. The functor is the inclusion of the pairs whose
endomorphism is invertible, and `ι` is the canonical arrow. The final sentence
adds no unit, commutativity or nondegeneracy hypothesis on B or its modules,
and none is added here.

The registered supplementary source `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
verified, is the errata of the 2010 edition. A text search of all 19 pages
found one mention of A.III, on PDF p. 15. It redirects a cross-reference on
another page to "A.III.1 exemple 5" and does not correct the example. This is
a limited reading of an older edition's errata; the 2026 original governs.

## Formal encoding and derived content

The following choices are **derived formalization content**, not formulas
quoted from the book. The general commutative ring k, the categorical
packaging and the universe raising are internal. They follow the published
k-linear pattern `Langlands.Renard.EndomorphismLocalization.ChosenComparison`
(`RenardEndomorphismLocalizationSource.lean`, Worker 1581) without reusing
its code.

**B-modules.** As in the published
`Langlands/Algebra/RenardAlgebraActionLocalization.lean`, a B-module is a
k-module with an actual nonunital k-algebra homomorphism
`B →ₙₐ[k] Module.End k M`. Here `k : Type u` is an arbitrary commutative ring,
B is a `Type v` with only `[NonUnitalRing B] [Module k B]`, and carriers live
in `Type w`. B-module maps are actual `Langlands.Algebra.LinearIntertwiner`
objects. A field k is the special case `k := K` for a field K.

## The category of compatible actions

`ActionModuleCat.{u, v, w} k B` is a structure with fields `carrier : Type w`,
its `AddCommGroup` and `Module k` instances, and
`action : B →ₙₐ[k] Module.End k carrier`. `ActionModuleCat.of M ρ` bundles an
actual module with an actual action.

`ActionModuleCat.Hom M N` is a one-field structure wrapping
`hom : LinearIntertwiner M.action N.action`. The category instance uses
`LinearIntertwiner.id` and `LinearIntertwiner.comp`; its three laws hold by
`rfl`. `ofHom`, `hom_ofHom`, `hom_id` and `hom_comp` are the bundling and
`rfl` formulas. `hom_ext` is pointwise extensionality.
`ActionModuleCat.homEquiv M N` is the bijection between categorical morphisms
and the actual intertwiners. So every intertwiner is a morphism and nothing
else is.

## Pairs with a compatible endomorphism

`ActionEndomorphismCat.{u, v, w} k B` is Mathlib's
`Endofunctor.Algebra (𝟭 (ActionModuleCat.{u, v, w} k B))`. An object A is an
object `A.a` with a morphism `A.str : A.a ⟶ A.a`, that is, an actual B-module
endomorphism. A morphism `A ⟶ A'` is a morphism `f : A.a ⟶ A'.a` with
`(𝟭 _).map f ≫ A'.str = A.str ≫ f`.

- `endomorphism A : Module.End k A.a` is the underlying k-linear map of
  `A.str`.
- `endomorphism_action A b z` states
  `endomorphism A (A.a.action b z) = A.a.action b (endomorphism A z)`. This is
  the compatibility hypothesis of the published `localizedAction`.
- `intertwining_iff A A' f` identifies the categorical equation with
  `∀ z, f.hom (endomorphism A z) = endomorphism A' (f.hom z)`.
- `homEquiv A A'` is a bijection from `A ⟶ A'` to the actual intertwiners of
  the actions that also intertwine the two specified endomorphisms.

`invertibleActionProperty k B` is the property `IsUnit (endomorphism A)` in
the ring `Module.End k A.a`. Invertibility as a k-linear map is equivalent to
invertibility among B-module endomorphisms. A k-linear inverse of a B-linear
map is automatically B-linear, as recorded in
`RenardAlgebraLocalizationUniversalStatements.md`. This unit uses only the
k-linear condition. `InvertibleActionEndomorphismCat k B` is the full
subcategory of this property, `invertibleActionInclusion k B` its inclusion
`ObjectProperty.ι`, and `invertibleActionInclusionFullyFaithful k B` the
fully faithful structure `fullyFaithfulι`. So the subcategory retains every
ambient morphism.

## Lifting actions and intertwiners

For `ρ : B →ₙₐ[k] Module.End k V`, `liftAction.{u, v, w, x} ρ` is the action on
`ULift.{x} V` conjugated through the native linear equivalence
`ULift.moduleEquiv`: b acts by `ULift.up (ρ b z.down)`. Its zero, addition,
multiplication and scalar laws are proved from those of ρ.
`liftAction_up` and `liftAction_down` give the formulas by `rfl`.

For `f : LinearIntertwiner ρ σ` with `σ` acting on `W : Type y`,
`liftIntertwiner.{u, v, w, x, y, z} f` is the actual intertwiner from
`liftAction.{u, v, w, x} ρ` to `liftAction.{u, v, y, z} σ`. It is
`z ↦ ULift.up (f z.down)`; the source and target lift universes x and z are
independent. `liftIntertwiner_up` and `liftIntertwiner_down` are its `rfl`
formulas.

## The raised source, the localized object and the canonical arrow

`raisedFunctor.{u, v, w, x} k B` goes from
`ActionEndomorphismCat.{u, v, w} k B` to
`ActionEndomorphismCat.{u, v, max u w x} k B`. It sends A to the carrier
`ULift.{max u x} A.a` with the lifted action and the lifted endomorphism. A
morphism goes to its lifted intertwiner; its compatibility follows from
`intertwining_iff`. The functor laws hold by `rfl`. The three simp lemmas
`raisedFunctor_action_up`, `raisedFunctor_endomorphism_up` and
`raisedFunctor_map_up` record the formulas on `ULift.up z`. The common carrier
universe `max u w x` is needed because the localization below lives in
`Type (max u w)`. The independent x lets targets live in larger universes.

`objectLocalizedAction A` is the published
`localizedAction (endomorphism A) A.a.action (endomorphism_action A)` on the
published carrier `EndomorphismLocalization.Localized (endomorphism A)`.

`localizedObject.{u, v, w, x} A` is an object of
`InvertibleActionEndomorphismCat.{u, v, max u w x} k B`. Its carrier is
`ULift.{x} (Localized (endomorphism A))`, with the lifted
`objectLocalizedAction A`. Its endomorphism is the lifted published
`localizedEndIntertwiner`, whose underlying map is `localizedEnd`. Its
invertibility proof shows that the lifted endomorphism is bijective. It
composes the bijections of the two `ULift` equivalences with the published
automorphism `localizedEquiv (endomorphism A)`, then applies
`Module.End.isUnit_iff`. `localizedObject_action_up` and
`localizedObject_endomorphism_up` give the formulas by `rfl`.

`canonicalArrow.{u, v, w, x} A` is a morphism from
`(raisedFunctor k B).obj A` to the inclusion of `localizedObject A`. Its
underlying intertwiner is the lift of the published `iotaIntertwiner`, so
`canonicalArrow_up` gives `ULift.up z ↦ ULift.up (iota (endomorphism A) z)`.
Its compatibility with the endomorphisms is the published `iota_intertwines`.

`canonicalStructuredArrow.{u, v, w, x} A` is
`StructuredArrow.mk (canonicalArrow A)`. It lies in
`StructuredArrow ((raisedFunctor k B).obj A) (invertibleActionInclusion k B)`,
the category whose initial objects are the solutions of Renard's right
universal problem for this inclusion. `canonicalStructuredArrow_right` and
`canonicalStructuredArrow_hom` identify its components by `rfl`.

## Scope and checks

No declaration assumes a unit on B, commutativity of B, nondegeneracy of an
action, nontriviality, finite dimension or invertibility of a source
endomorphism. The zero ring, zero modules, zero actions and zero or nilpotent
endomorphisms are allowed. No universal property, factorization or uniqueness
is asserted here. Initiality of `canonicalStructuredArrow`, the factorization
for every invertible target and the field specialization are separate
successor statements. A proof can build on the published raw B-linear
universal property `UniversalPropertyStatements`
(`RenardAlgebraLocalizationUniversalStatements.lean` and its published proof).

The module imports the published `Langlands.Algebra.RenardAlgebraActionLocalization`
and four Mathlib modules: `Algebra.Module.ULift`,
`CategoryTheory.Comma.StructuredArrow.Basic`,
`CategoryTheory.Endofunctor.Algebra` and
`CategoryTheory.ObjectProperty.FullSubcategory`. It reuses published
declarations by Lean name and adds no axioms. In environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` it compiled with no errors or warnings.
An inspection of `canonicalStructuredArrow` reported level parameters u, v,
w, x and only `propext`, `Classical.choice` and `Quot.sound`.
