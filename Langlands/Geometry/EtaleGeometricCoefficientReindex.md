# Reindexing geometric coefficients and actual cohomological diagrams

The paired module constructs reindexing for the actual geometric coefficient
category over an arbitrary contravariant diagram of schemes. It compares the
resulting derived-section, ordinary-cohomology and section diagrams with
precomposition, naturally in compatible coefficients, and proves compatibility
with canonical homology and degree-zero recovery.

All declarations are in
`Langlands.Geometry.EtaleGeometricDiagram.CoefficientDiagram`.

## Mathematical input and scope

Let `R : Type u` be any commutative ring, let `J : Type v` have a
`Category.{w}` structure, and let `S : J ⥤ Scheme.{u}ᵒᵖ`. Write
`X_i = (S.obj i).unop`. Let `K : Type v'` have a `Category.{w'}` structure
and let `F : K ⥤ J` be any functor. Thus an arrow `a : i ⟶ j` in `J`
gives an actual scheme morphism `X_j ⟶ X_i`. There is no étaleness
assumption on this morphism.

The imported `CoefficientDiagram R S` has actual small-étale
`ModuleCat.{u} R` sheaves `D_i` and maps

`(S.map a).unop⁻¹(D_i) ⟶ D_j`,

where inverse image is the geometric functor constructed in
`EtaleInverseImage`. Its identity and composition laws include the canonical
inverse-image comparisons and the equalities `S.map_id` and `S.map_comp`.
The coefficient maps need not be isomorphisms. No cohomology object, desired
comparison map, field structure, finiteness or local-constancy premise is an
input to reindexing.

The sheaf-category construction, evaluation comparison, and identity and
composition comparisons require no derived-category hypotheses. For the
cohomological declarations, the module retains

- a common universe `wS` and
  `∀ i : J, HasDerivedCategory.{wS} (ModuleSheaf X_i R)`;
- an independent universe `wR` and
  `HasDerivedCategory.{wR} (ModuleCat.{u} R)`.

These hypotheses also occur in the ordinary-cohomology and section
comparisons, because the geometric diagrams obtain their transitions by
transport from derived sections. A local instance supplies the localization
at each image vertex `F.obj i` using the original instance. Schemes, the
ring and module carriers share universe `u`; all index object and morphism
universes above are independent. A further index category used for
composition has independent universes `v''` and `w''`. Ordinary cohomology
degrees are `q : ℕ`.

## The actual coefficient functor

`map_id_transport` and `map_comp_transport` are the existing coefficient
laws with an explicit equality of index arrows. In the first, an equality
`h : a = 𝟙 i` is carried through `S.map` and followed by `S.map_id i`.
In the second, `h : c = a ≫ b` is carried through `S.map` and followed
by `S.map_comp a b`. The resulting scheme-arrow equalities occur in
`inverseImageCongr`, with the same orientations as the original diagram
constraints. Equality elimination reduces each proof to the original law.

`reindex F D` has scheme diagram `F ⋙ S` and is defined by

`(reindex F D).obj i = D.obj (F.obj i)`

and

`(reindex F D).map a = D.map (F.map a)`.

Its identity and composition obligations follow from those two transported
laws with `F.map_id` and `F.map_comp`. In particular, reindexing does not
discard the propositional functor laws in the geometric constraints.

`reindexMap F α` has component `α.app (F.obj i)`. Its transition square
is the original square at `F.map a`. `reindexFunctor F` packages these
operations as a functor; preservation of identities and composition is
pointwise equality of actual sheaf morphisms.

`reindexEvaluationIso F i` identifies evaluation after reindexing with
evaluation at `F.obj i`. `reindexIdIso` identifies reindexing by `𝟭 J`
with the identity functor. For `H : L ⥤ K`, `reindexCompIso F H`
identifies reindexing first by `F` and then by `H` with reindexing by
`H ⋙ F`. These three isomorphisms are `Iso.refl` on definitionally equal
functors; their components are the categorical identities.

## Cohomological diagrams

For a geometric coefficient diagram `D`, let `B_D` denote its actual
bounded-below derived-section diagram, `C_D^q` its ordinary-cohomology
diagram, and `A_D` its actual section diagram. The imported geometric
construction assigns `RΓ(X_i, D_i)` to the first diagram and the ordinary
right-derived cohomology and actual sections of `D_i` to the others.
Its transition maps are the constructed geometric pullbacks followed by
the supplied coefficient maps; the ordinary and section transitions are
transported through the canonical derived recovery isomorphisms.

`reindex_derivedSections`, `reindex_cohomology` and `reindex_sections`
prove, respectively,

`B_(reindex F D) = F ⋙ B_D`,

`C_(reindex F D)^q = F ⋙ C_D^q`,

and

`A_(reindex F D) = F ⋙ A_D`.

All three equalities are definitional, including their arrow maps.
The corresponding `reindexDerivedSectionsIso`, `reindexCohomologyIso`
and `reindexSectionsIso` are identity isomorphisms of these diagrams.

The declarations `reindexDerivedSectionsFunctorIso`,
`reindexCohomologyFunctorIso` and `reindexSectionsFunctorIso` make the
comparisons natural in the entire coefficient category. In each case,
the source is reindexing followed by the corresponding functor for
`F ⋙ S`; the target is the corresponding functor for `S` followed by
Mathlib's left-whiskering functor at `F`. Their components are the
diagram isomorphisms just described. Both routes on a coefficient
morphism apply the same actual cohomological functor to
`α.app (F.obj i)`, so componentwise identity laws prove naturality.

## Canonical recovery compatibility

`reindex_derivedSectionsHomologyIso` and
`reindex_derivedSectionsZeroIso` identify the full canonical recovery
isomorphisms for `reindex F D` with left whiskering by `F` of the
corresponding recovery isomorphisms for `D`.
`reindex_cohomologyZeroIso` gives the same equality for the component of
`cohomologyZeroFunctorIso`, which identifies ordinary degree-zero
cohomology with actual sections. These are equalities of isomorphisms,
so they also determine the inverse maps. The proofs use isomorphism and
natural-transformation extensionality: the canonical maps at each
unchanged sheaf are identical.

More explicitly, let `H_q` be the bounded-below homology functor and
let `r_q(D) : B_D ⋙ H_q ≅ C_D^q` be canonical recovery.
`reindexDerivedSectionsIso_homology` proves the equality of composites

`(reindexDerivedSectionsIso F D ▷ H_q) ≪≫ (F ◁ r_q(D))`

`= r_q(reindex F D) ≪≫ reindexCohomologyIso F D q`.

Here `▷` and `◁` mean right and left whiskering of isomorphisms.
`reindexDerivedSectionsIso_zero` proves the same square with `H_0`,
canonical recovery to sections, and `reindexSectionsIso`.
At each vertex the equations reduce to a homology functor applied to an
identity, followed by the same canonical recovery map, versus that map
followed by an identity.

`reindexDerivedSectionsFunctorIso_homology` and
`reindexDerivedSectionsFunctorIso_zero` prove these squares as equations
of natural isomorphisms on the coefficient category. The displayed
functors for precomposition and postcomposition agree definitionally
where the composites meet. Extensionality in coefficients reduces the
proofs to the two diagram-level equations.

## Provenance and remaining obligations

This is an internal categorical construction, derived from the actual
geometric coefficient and cohomological functors in
`EtaleGeometricCoefficientDiagram`. The transported-law method reuses
the design of `EtaleCohomologyReindex` for restriction coefficients;
the present module uses geometric inverse image and requires no
étaleness. It does not replace that restriction construction or the
equivariant reindexing modules.

Reindexing is useful for changing the index of a tower, but this module
does not take a limit or construct a particular Harris tower. Interchange
with geometric-to-restriction coefficient transport, equivariant
geometric coefficients, smoothness, compact supports, scalar change,
Galois actions, arithmetic coefficient systems, and the actual Harris
specialization remain separate obligations.
