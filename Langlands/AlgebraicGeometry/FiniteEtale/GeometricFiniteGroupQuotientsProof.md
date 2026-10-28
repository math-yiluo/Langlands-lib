# Finite-group quotients and preservation by geometric fibres

The theorem
`Langlands.AlgebraicGeometry.FiniteEtale.geometricFiniteGroupQuotients`
proves the unchanged Library proposition
`GeometricFiniteGroupQuotients s hfin` from `StructuralStatements`.
Its parameters are exactly

```lean
{S : Scheme.{u}} [ConnectedSpace S] [IsLocallyNoetherian S]
{Ω : Type u} [Field Ω] [IsAlgClosed Ω]
(s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y))
```

For every `G : Type u` with `[Group G] [Finite G]`, it proves

```lean
HasColimitsOfShape (SingleObj G) (Cover S) ∧
PreservesColimitsOfShape (SingleObj G) (fiberFunctor s hfin)
```

Here `Cover S`, `Fiber s`, `pointFunctor s` and `fiberFunctor s hfin` are
the actual constructions in `Definitions`: finite étale schemes over `S`,
their geometric lifts of `s`, postcomposition on those lifts, and its lift
to finite sets using `hfin`. The quantifier over groups retains the full
universe `u`.

## Implemented proof

Fix such a group and a diagram `D : SingleObj G ⥤ Cover S`.
The published theorem `finiteGroupQuotientCocones` supplies a cocone `c`
in this category, a colimit witness, and its geometric orbit property.
Applying `HasColimit.mk` to the witness gives colimit existence for
every `D`, hence `HasColimitsOfShape (SingleObj G) (Cover S)`.

Specialize the same theorem's assertion about every algebraically closed
field and geometric point to `Ω` and `s`. The sole leg of the mapped
cocone `(pointFunctor s).mapCocone c` is surjective. If two points have
the same image, the forward implication of its orbit equivalence identifies
them by a group element. The helper `groupOrbitCoconeIsColimit` therefore
makes this mapped cocone a colimit in types. Its construction chooses
preimages; cocone naturality and the orbit property give factorization,
and surjectivity gives uniqueness.

The Mathlib theorem
`preservesColimit_of_preserves_colimit_cocone` then gives preservation
for the diagram from this one source colimit cocone and its mapped
colimit. Doing this for every `D` gives preservation of the whole shape
by `pointFunctor s`.

Finally `fiberFunctor_preservesColimitsOfShape_large` transfers preservation
to `fiberFunctor s hfin`: its composite with the fully faithful inclusion
`FintypeCat.incl` is definitionally `pointFunctor s`, and this inclusion
reflects colimits. The helper admits independent indexing universes,
so it applies to `SingleObj G` for `G : Type u`. The two conclusions
are the required conjunction.

## Provenance and scope

This is an internal categorical assembly of published Library results.
`QuotientCoconeGluingProof` constructs and proves the geometric quotient
cocones, using the invariant-section spectra over affine opens and their
relative gluing. Its paired Markdown records the geometric provenance.
`QuotientCoconeTools` supplies the orbit colimit construction and the
universe-general finite-set transfer. This module imports those results
by Lean name and introduces no additional literature claim.

There is no extra quotient-cocone hypothesis or Galois-category,
fibre-functor, or action-equivalence premise. The proof places no
restriction on the action and adds no affine-base or group-order
hypothesis. It retains the original connectedness and local
noetherianity parameters and leaves the statement and its imports
unchanged.
