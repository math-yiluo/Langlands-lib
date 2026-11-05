# Canonical geometric coefficients from an original base sheaf

This module constructs compatible small étale coefficient diagrams by actual
inverse image from a fixed base. The original base sheaf is arbitrary, and every
morphism of base sheaves is retained. All transition isomorphisms, identity laws
and composition laws are constructed; no coefficient cocycle or cohomological
comparison is assumed.

## Inputs and conventions

Fix a scheme `X : Scheme.{u}`, a commutative ring `R : Type u`, an index category
`J : Type v` with morphisms in universe `w`, and a contravariant scheme diagram
`S : J ⥤ Scheme.{u}ᵒᵖ`. The coefficient category `ModuleSheaf X R` is the existing
category of `ModuleCat.{u} R`-valued sheaves on the actual small étale site of `X`.
The ring and scheme universes coincide; the index object and morphism universes
are independent. The construction is noncomputable, as are the existing
inverse-image functors.

The geometric input is a natural transformation

```lean
π : (Functor.const J).obj (Opposite.op X) ⟶ S
```

This gives actual scheme projections `pᵢ = (π.app i).unop : (S.obj i).unop ⟶ X`.
For `a : i ⟶ j`, write `fₐ = (S.map a).unop`. The arrow goes from the scheme at
`j` to the scheme at `i`. The theorem `baseProjection_triangle` proves the literal
scheme equality `fₐ ≫ pᵢ = pⱼ` from `π.naturality a`, after removing the constant
identity map and reversing passage to the opposite category.

There is no étaleness, finiteness, invertibility or covering hypothesis on a
projection or diagram arrow. These are inverse images on small étale sites for
arbitrary scheme morphisms, using the existing constructed inverse image and
its adjunction. A natural projection is genuine input geometry, rather than a
record of desired cohomology groups or maps.

## Triangle isomorphisms and intrinsic coherence

In `Langlands.Geometry.EtaleInverseImage`, `projectionInverseImageIso` takes a
commuting triangle `f ≫ p = q` and defines the natural isomorphism

```lean
inverseImage p R ⋙ inverseImage f R ≅ inverseImage q R
```

It is exactly `inverseImageComp R p f` followed by `inverseImageCongr` for that
triangle equality. Both comparisons are the existing actual inverse-image
comparisons, not fresh arbitrary choices.

The generic helpers `inverseImageCongr_trans_app`,
`inverseImageComp_congr_left_app` and `inverseImageComp_congr_right_app` prove
that equality transport composes and commutes with inverse-image composition.
Each proof substitutes the equal scheme arrows, then uses
`inverseImageCongr_refl` and category or functor identity laws. These helpers are
valid in arbitrary universe `u` and at every original coefficient sheaf.

`projectionInverseImageIso_id` proves the identity constraint for a triangle
whose scheme arrow is equal to the identity. It specializes
`inverseImageComp_id_source`, retaining equality transport of the original
arrow before the inverse-image identity comparison. The triangle equality
proofs coincide by proof irrelevance after substitution.

For projections `p : Y ⟶ X`, `q : Z ⟶ X`, `r : W ⟶ X`, scheme arrows
`f : Z ⟶ Y`, `g : W ⟶ Z`, `k : W ⟶ Y`, commuting triangles and `g ≫ f = k`,
`projectionInverseImageIso_comp` proves that first pulling the `f` triangle
through `g` and then using the `g` triangle equals the original inverse-image
composition comparison, transport of `g ≫ f = k`, and the `k` triangle. The
implemented proof evaluates the already proved `inverseImageComp_assoc` at the
base sheaf. It moves triangle equality transport through that comparison with
the left and right congruence lemmas, then combines the resulting equality
transports. The two final scheme equality proofs have the same endpoints, so
proof irrelevance identifies them. The projections vary; no common projection
or endomorphism restriction is imposed.

## The canonical coefficient functor

In `Langlands.Geometry.EtaleGeometricDiagram`,
`baseProjectionInverseImageIso R π a` applies the triangle construction to the
original projection maps and `fₐ`. For a base sheaf `M`,
`canonicalCoefficients R π M : CoefficientDiagram R S` has

```text
coefficient at i  = inverseImage(pᵢ)(M)
transition at a   = inverseImageComp(pᵢ, fₐ)(M)
                    followed by inverseImageCongr(fₐ ≫ pᵢ = pⱼ)(M).
```

Its `map_id` field is proved by `projectionInverseImageIso_id` using `S.map_id`.
Its `map_comp` field is proved by `projectionInverseImageIso_comp` using
`S.map_comp`. In particular the diagram's original identity and composition
transports are retained, including their orientation in the opposite scheme
category. These fields are proofs, not hypotheses supplied by the caller.

`canonicalCoefficientsMap R π α` pulls every original base sheaf map `α` back at
each vertex. Naturality of `baseProjectionInverseImageIso` proves its commuting
square with every coefficient transition. `canonicalCoefficientsFunctor R π`
assembles the construction into

```lean
ModuleSheaf X R ⥤ CoefficientDiagram R S
```

using the original inverse-image functors' identity and composition laws.
`canonicalCoefficients_obj`, `canonicalCoefficients_map` and
`canonicalCoefficientsMap_app` state the exact object, transition and component
formulas. `canonicalCoefficients_map_isIso` derives invertibility of every
coefficient transition from the constructed natural isomorphism. It does not
assert that the underlying scheme map is invertible.

`canonicalCoefficientsEvaluationIso R π i` identifies evaluation at vertex `i`
with the original inverse-image functor along `pᵢ`, on every object and morphism.
This is an identity isomorphism of definitionally equal functors; the two
component formulas explicitly give identity sheaf maps.

## Reindexing

For any `F : K ⥤ J`, where `K` also has independent object and morphism
universes, `reindexBaseProjection π F` is the actual left whiskering of `π` by
`F`. Its components are the original projection components at `F.obj i`.
`canonicalCoefficients_reindex` proves that the existing reindexing of
`canonicalCoefficients R π M` is definitionally the canonical coefficient
diagram for the reindexed projection.

`canonicalCoefficientsReindexIso R π F` upgrades this equality to an identity
natural isomorphism between the two functors from original base sheaves to
coefficient diagrams. Both component directions are the original identity
coefficient maps, as stated by the two evaluation lemmas. It is natural in
every original base sheaf morphism. The existing reindexing construction and
its derived-section, ordinary-cohomology, section and comparison consumers
remain available without duplication here.

## Provenance and retained scope

This is an internal construction from the actual inverse images, their
adjunction-derived coherence, and the already constructed geometric
coefficient-diagram and reindexing categories. The immediate imported APIs are
in `EtaleInverseImageCoherence`, `EtaleGeometricCoefficientDiagram` and
`EtaleGeometricCoefficientReindex`. The underlying inverse image is the
existing affine-site Kan-extension and sheafification construction. No new
assertion is attributed to an external source in this module.

Worker 13 generalized and assembled the construction. Worker 57 contributed
the equality-transport and fixed-projection coherence proof pattern from the
private helper block of `HarrisTaylorCMGeometricGaloisCoefficients`. The helpers
here have arbitrary universe and the triangle composition allows different
schemes and projections. The CM specialization remains unchanged and is not
imported or assumed by this module. Both workers are credited for this reuse.

This constructs canonical geometric coefficients and their morphisms. The
existing coefficient-diagram functors can apply derived sections, ordinary
cohomology and sections to these objects. This file does not add a deck-action
specialization, an analytic étale realization, compact-support or trace
comparisons, an unconditional Shimura representation theorem, arithmetic Hecke
identifications or Harris compatibility. Those parts of the broader framework
remain separate obligations.
