# Invertibility of the canonical presheaf pullback tensor comparison

`Langlands.Scheme.Modules.presheafPullbackTensorComparisonIsIsoStatement`
is a proposition with arbitrary universe parameter `u`. Its exact content is

```text
∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
  IsIso (Langlands.Scheme.Modules.presheafPullbackTensorComparison f).
```

The comparison is imported unchanged from
`Langlands.AlgebraicGeometry.Modules.PresheafPullbackTensor`.
Writing `L = presheafPullback f`, it is the fixed natural transformation

```text
MonoidalCategory.tensor Y.PresheafOfModules ⋙ L
  ⟶ L.prod L ⋙ MonoidalCategory.tensor X.PresheafOfModules.
```

Both functors have source `Y.PresheafOfModules × Y.PresheafOfModules`
and target `X.PresheafOfModules`. Their tensors are the existing sectionwise
tensor products of presheaves of modules. At `M,N`, the comparison is exactly
`presheafPullbackTensorComparisonApp f M N`. It is the inverse image under
`presheafPullbackPushforwardAdjunction f` of the composite of the tensor
of the two adjunction units with
`presheafPushforwardTensorApp f (L.obj M) (L.obj N)`.
Thus `IsIso` concerns this specific natural transformation, rather than the
existence of an unspecified isomorphism between its source and target.

The proposition has no flatness, affineness, quasicoherence, local freeness,
sheafness, or monoidal-preservation hypotheses. The indexing functor is
`TopologicalSpace.Opens.map f.base`, and the ring-presheaf map is
`CategoryTheory.Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)`,
as fixed by the imported construction. There is no generalization to an
arbitrary indexing functor.

## Provenance and downstream use

This is an internal derived statement isolating the presheaf
tensor-preservation prerequisite for the published sheaf target
`Langlands.Scheme.Modules.pullbackTensorComparisonIsIsoStatement`.
The conditional reduction through sheafification is being developed in
task `a2c3b108-b55b-4f55-862a-6ef3eac96399`. That development is separate
from this statement and is not evidence for its truth.

The motivating sheaf result is the Stacks Project, Section 17.16
([tag 01CA](https://stacks.math.columbia.edu/tag/01CA)), Lemma 17.16.4
([tag 01CD](https://stacks.math.columbia.edu/tag/01CD)). It asserts functorial
compatibility of sheaf-module pullback with tensor products for a morphism
of ringed spaces and omits its proof. It does not assert the present
presheaf proposition; this module is not a direct transcription of that
lemma. The retained source is
`stacks-module-tensor-products-2026-10-21`, *Stacks Project - Tensor
products of sheaves of modules (HTML snapshot 2026-10-21)*, SHA256
`825127394e5828c3a56f5134b8823afba20547d7ba5173f624b2f9556a058e34`.

A prospective proof can use preservation of finite intersections by the
inverse-image opens functor and the tensor universal property. No such
proof is supplied here. This module defines only the proposition and
provides neither a proof nor an `IsIso` instance. It assumes neither the
final sheaf invertibility result nor a monoidal pullback instance.

Worker 150 supplied the exact proposition and its intended role in the
sheafification reduction. Worker 368 implemented this statement pair.
