# The generation locus of a tensor product of line-bundle sections

`Langlands.SchemeModule.tensorSectionGenerationLocus` proves the published
proposition `Langlands.SchemeModule.TensorSectionGenerationLocusStatement.{u}`
from module `Langlands.AlgebraicGeometry.Modules.TensorSectionGenerationLocusStatement`.
The theorem's type is that proposition itself, with an arbitrary universe `u`
and no further hypotheses. For every scheme `X : Scheme.{u}`, all
`L M : LineBundle X`, and all global sections `s` of `L.obj` and `t` of
`M.obj`, it proves the equality in `X.Opens`

```lean
trivializationOpen (tensorObj L.obj M.obj) (tensorSection L.obj M.obj s t) =
  trivializationOpen L.obj s ⊓ trivializationOpen M.obj t
```

of the whole maximal trivialization opens. The scheme is arbitrary, and either
section may be zero. The published statement pair and everything it imports
are unchanged.

The module also proves the public theorem `isStalkFrame_tensorSection_iff`
and some private helper lemmas, all in namespace `Langlands.SchemeModule`.
They are described below.

## Implemented proof

The proof is pointwise. It shows that the product section is a stalk frame at
a point exactly when both factors are, and then passes from stalk frames to
trivialization opens with published results. Throughout, "`φ` is a stalk
isomorphism at `x`" means that the map of stalks at `x` induced by the
morphism of module sheaves `φ` is an isomorphism. The private abbreviation
`StalkIso φ x` names this condition. By definition (module
`Langlands.AlgebraicGeometry.Modules.SectionLocus`), `IsStalkFrame N u x`
says that `sectionHom N u : structureModule X ⟶ N`, the morphism sending
`1` to `u`, is a stalk isomorphism at `x`.

### Helper lemmas

- `stalkIso_iso_comp_iff`: composing a morphism on both sides with
  isomorphisms does not change whether it is a stalk isomorphism at `x`. The
  stalk functor sends the composite to a composite with isomorphisms.
- `unitEndCoefficient_comp`: for endomorphisms `α` and `β` of the structure
  module and an open `U`, the coefficient `unitEndCoefficient (α ≫ β) U`,
  that is `(α ≫ β).app U 1`, is the product of the two coefficients. This
  follows from `unitEndCoefficient_app`, which says that `β` acts on sections
  over `U` as multiplication by its coefficient.
- `stalkIso_unitEnd_comp_iff`: `α ≫ β` is a stalk isomorphism at `x` if and
  only if both `α` and `β` are. The published
  `unitEnd_stalkIso_iff_mem_basicOpen`
  (module `Langlands.AlgebraicGeometry.Picard.AffineGenerationLocusIntersectionProof`)
  turns each of the three conditions into membership of `x` in the basic open
  of the global coefficient. The previous lemma and Mathlib's
  `AlgebraicGeometry.Scheme.basicOpen_mul` give
  `X.basicOpen (a * b) = X.basicOpen a ⊓ X.basicOpen b`.
- `tensorLeftUnitor_conj_tensorMap`: for endomorphisms `α` and `β` of the
  structure sheaf,
  `(tensorLeftUnitor 𝒪).inv ≫ tensorMap α β ≫ (tensorLeftUnitor 𝒪).hom = α ≫ β`.
  The proof splits `tensorMap α β` as `tensorMap α 𝟙 ≫ tensorMap 𝟙 β`
  (`tensorMap_comp`). It then uses the published unitor laws of
  `Langlands.AlgebraicGeometry.Modules.TensorUnitorLaws`:
  `tensorLeftUnitor_naturality` moves `β` through the left unitor,
  `tensorUnitors_equal` replaces the left unitor of `𝒪 ⊗ 𝒪` by the right
  unitor, and `tensorRightUnitor_naturality` moves `α` through it.
- `stalkIso_tensorMap_iso_comp_iff`: if `φ` and `ψ` are each composed on both
  sides with isomorphisms, then `tensorMap` of the composites is a stalk
  isomorphism at `x` exactly when `tensorMap φ ψ` is. By `tensorMap_comp` the
  outer factors become `tensorMap` of isomorphisms, which are isomorphisms
  because `tensorMap` is the action of the tensor functor on morphisms.
- `stalkIso_pullback_ι_iff`: for an open `W` and `y : W`, the inverse image
  `(Scheme.Modules.pullback W.ι).map φ` is a stalk isomorphism at `y` exactly
  when `φ` is a stalk isomorphism at `W.ι y`. Mathlib's
  `Scheme.Modules.restrictFunctorIsoPullback` identifies the inverse image
  with the restriction functor, and the published `isIso_stalk_restrict_iff`
  (module `Langlands.AlgebraicGeometry.Modules.SectionLocusComparison`)
  handles the restriction.

### The pointwise statement

`isStalkFrame_tensorSection_iff L M s t x` proves

```lean
IsStalkFrame (tensorObj L.obj M.obj) (tensorSection L.obj M.obj s t) x ↔
  IsStalkFrame L.obj s x ∧ IsStalkFrame M.obj t x
```

for every point `x`. The `LineBundle` property gives opens `U` and `V`
containing `x` with trivializations `eL` of `L.obj` on `U` and `eM` of
`M.obj` on `V`. Let `W = U ⊓ V`, let `y` be the point `x` of the open
subscheme `W`, and let `P` be the inverse-image functor
`Scheme.Modules.pullback W.ι`. The published `pullbackTrivializationOfLE`
(module `Langlands.AlgebraicGeometry.Picard.LineBundleTensor`) restricts `eL`
and `eM` to isomorphisms `eL'` and `eM'` from `P.obj L.obj` and `P.obj M.obj`
to the structure sheaf of `W`. Let `ι` be the published `pullbackUnitIso W.ι`
from the inverse image of the structure sheaf to the structure sheaf of `W`.
Write `fs = sectionHom L.obj s` and `ft = sectionHom M.obj t`, and set

```lean
α = ι.inv ≫ P.map fs ≫ eL'.hom,    β = ι.inv ≫ P.map ft ≫ eM'.hom.
```

These are endomorphisms of the structure module of `W`. By
`stalkIso_iso_comp_iff` and `stalkIso_pullback_ι_iff`, `α` is a stalk
isomorphism at `y` exactly when `IsStalkFrame L.obj s x`, and similarly for
`β` and `t`.

For the product section, `stalkIso_pullback_ι_iff` reduces the claim to the
stalk at `y` of `P.map` of its section morphism. The published
`sectionHom_tensorSection` (module
`Langlands.AlgebraicGeometry.Modules.TensorSections`) writes that section
morphism as `(tensorLeftUnitor 𝒪_X).inv ≫ tensorMap fs ft`. Let
`c = pullbackTensorComparison W.ι` be the natural comparison from
`P (A ⊗ B)` to `P A ⊗ P B`. The published `pullbackTensorComparisonIsIso`
(module `Langlands.AlgebraicGeometry.Modules.PullbackTensorProof`) shows that
`c` is an isomorphism, and naturality of `c` at `(fs, ft)` gives

```lean
P.map (sectionHom (tensorObj L.obj M.obj) (tensorSection L.obj M.obj s t)) =
  P.map (tensorLeftUnitor 𝒪_X).inv ≫ c.app (𝒪_X, 𝒪_X) ≫
    tensorMap (P.map fs) (P.map ft) ≫ inv (c.app (L.obj, M.obj)).
```

A chain of equivalences of stalk-isomorphism conditions at `y` then
finishes the pointwise statement:

1. The outer factors above are isomorphisms, so the condition for `P.map` of
   the product's section morphism is the condition for
   `tensorMap (P.map fs) (P.map ft)` (`stalkIso_iso_comp_iff`).
2. `P.map fs = ι.hom ≫ α ≫ eL'.inv` and `P.map ft = ι.hom ≫ β ≫ eM'.inv`,
   so by `stalkIso_tensorMap_iso_comp_iff` this is the condition for
   `tensorMap α β`.
3. By `tensorLeftUnitor_conj_tensorMap` on the scheme `W`, `α ≫ β` is
   `tensorMap α β` conjugated by the left unitor of the structure sheaf of
   `W`. So the condition is the one for `α ≫ β`.
4. By `stalkIso_unitEnd_comp_iff` this holds exactly when both `α` and `β`
   are stalk isomorphisms at `y`, that is, when
   `IsStalkFrame L.obj s x` and `IsStalkFrame M.obj t x`.

### The whole trivialization opens

The main theorem compares underlying sets (`SetLike.coe_injective`). The
published `trivializationOpenInterior`
(module `Langlands.AlgebraicGeometry.Modules.SectionLocusComparison`) writes
the left-hand side as the interior of the set of points where the product
section is a stalk frame. No line-bundle property of the tensor product is
needed for this. The published `lineBundle_stalkFrame_set_eq` (module
`Langlands.AlgebraicGeometry.Modules.LineBundleFrameOpen`) writes the
trivialization opens of `s` and `t` as the sets of stalk-frame points of `s`
and `t`. By `isStalkFrame_tensorSection_iff`, the stalk-frame set of the
product is the intersection of these two sets. That intersection is open by
the published `isOpen_lineBundle_stalkFrame` (same module), so it equals its
interior. This proves the equality of the whole opens.

The argument works for every scheme and does not choose a smaller
neighbourhood or an affine subopen: both sides are the whole maximal
trivialization opens. It uses no residue-field comparison, rank-one property
of the tensor product, flatness, quasi-coherence, monoidal-preservation or
ampleness hypothesis. Local rank one of `L` and `M` enters only through the
`LineBundle` property, which supplies the trivializing opens. The
isomorphism property of the pullback-tensor comparison is the published
theorem `pullbackTensorComparisonIsIso`, not an assumption.

## Provenance

The proposition formalizes the remark `X_s ∩ X_{s'} = X_{ss'}` at the start of
The Stacks Project, Section 28.27, "Ample invertible sheaves", tag 01PR,
registered as `stacks-ampleness-tensor-isomorphism-2026-10-24` (retained file
`01PR.html`). The statement's Markdown explains the translation of the
source's loci into the Library's trivialization opens. The source states the
remark without proof. The Lean proof is the local argument above: on an open
where both line bundles are trivial, the product section corresponds to the
product of the two coordinates, and the basic open of a product of two
functions is the intersection of their basic opens.
