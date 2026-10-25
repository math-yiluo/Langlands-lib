# Monomorphisms of finite étale covers are coproduct summands

`Langlands.AlgebraicGeometry.FiniteEtale.geometricMonomorphismComplements`
proves exactly the published proposition `GeometricMonomorphismComplements`
from `Langlands.AlgebraicGeometry.FiniteEtale.MonoEpiConservativeStatements`.
It retains the complete parameter list

```lean
{S : Scheme.{u}} [ConnectedSpace S] [IsLocallyNoetherian S]
{Ω : Type u} [Field Ω] [IsAlgClosed Ω]
(s : Spec (.of Ω) ⟶ S)
(hfin : ∀ Y : Cover S, Finite (Fiber s Y))
```

For every `i : X ⟶ Y` in the actual `Cover S` with `[Mono i]`, it constructs
`Z : Cover S` and `v : Z ⟶ Y` with
`Nonempty (IsColimit (BinaryCofan.mk i v))`. The conclusion uses the given
target `Y` as the coproduct vertex. The proof uses no property of the
geometric point or of `hfin`; connectedness, local noetherianity, and the
field hypotheses are retained to match the target. It adds no instances
or assumptions of Galois-category structure or a classification equivalence.

## Implemented proof

Write `f := i.hom.left` for the underlying scheme morphism.

1. The structural maps of `X` and `Y` are finite étale, and
   `f ≫ Y.obj.hom = X.obj.hom` by `Over.w`. The published
   `finiteEtale_hasOfPostcompProperty` therefore shows that `f` is finite
   étale, using `finiteEtale.of_postcomp`.
2. The inclusion `Cover S ⥤ Over S` preserves pullbacks, by the published
   closure of the cover property under pullbacks. Mathlib's
   `preserves_mono_of_preservesLimit` consequently transfers monicity of
   `i` to `i.hom`. Then `Over.mono_left_of_mono` transfers it to `f`.
   This argument uses preservation of pullbacks, rather than attributing
   preservation of monomorphisms to fullness alone.
3. By `IsClosedImmersion.iff_isFinite_and_mono`, `f` is a closed immersion.
   It is also an open immersion by `IsOpenImmersion.of_flat_of_mono`:
   étaleness supplies flatness and local finite presentation. Thus its
   range is both open and closed.
4. Let `U` be the open subset of `Y.obj.left` whose underlying set is the
   complement of `Set.range f`. Its canonical scheme inclusion `U.ι` is
   an open immersion. Its range is closed because `Set.range f` is open,
   so `IsClosedImmersion.of_isPreimmersion` also makes it a closed
   immersion. Hence `U.ι` is finite and étale. Composition with
   `Y.obj.hom` is finite étale, giving
   `Z := cover (U.ι ≫ Y.obj.hom)`. The morphism `v` is `U.ι` regarded
   as a map of these covers over `S`.
5. The open ranges of `f` and `U.ι` are complementary. Mathlib's
   `nonempty_isColimit_binaryCofanMk_of_isCompl` proves the actual
   scheme coproduct universal property for `BinaryCofan.mk f U.ι`.
   The functor `coverToScheme S := inclusion S ⋙ Over.forget S`
   reflects colimits: the full-subcategory inclusion reflects them, and
   `Over.forget S` creates them. Applying
   `isColimitMapCoconeBinaryCofanEquiv` and `isColimitOfReflects`
   transfers that witness to `BinaryCofan.mk i v` in `Cover S`.

The module imports the published finite-limit and coproduct proof for
its cancellation and closure infrastructure, and imports Mathlib's
`Morphisms.FlatMono` and `Limits.Constructions.EpiMono` for the two
monomorphism arguments. As in the finite-limit proof and Mathlib's
étale and finite morphism modules, it sets
`backward.isDefEq.respectTransparency.types false` to expose the
morphism-property instances. The existing statement pairs and their
imports are unchanged.

## Provenance

This is an internal geometric proof of a derived structural obligation.
The source context is Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, preliminary draft, Chapter X §3, Definitions
10.25–10.26, printed page 150 (PDF page 154), and Theorem 10.28,
printed page 151 (PDF page 155). Registered source:
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Definition 10.25 identifies the full category of finite étale covers
and notes that its morphisms are finite étale. The coproduct-complement
target is an internal component corresponding to Mathlib's
`PreGaloisCategory.monoInducesIsoOnDirectSummand`, not a verbatim
assertion of that source. The proof above uses Mathlib's scheme
geometry and does not use Theorem 10.28 as an input.

Worker 444 authored this proof pair.
