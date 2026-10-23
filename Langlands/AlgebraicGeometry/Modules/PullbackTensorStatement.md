# Invertibility of the canonical pullback tensor comparison

`Langlands.Scheme.Modules.pullbackTensorComparisonIsIsoStatement` is a
proposition, with arbitrary universe parameter `u`. It asserts that for every
pair of schemes `X Y : AlgebraicGeometry.Scheme.{u}` and every morphism
`f : X ⟶ Y`, the published natural transformation
`pullbackTensorComparison f` is an isomorphism in the functor category:

```text
tensorFunctor Y ⋙ AlgebraicGeometry.Scheme.Modules.pullback f
  ⟶ (AlgebraicGeometry.Scheme.Modules.pullback f).prod
      (AlgebraicGeometry.Scheme.Modules.pullback f) ⋙ tensorFunctor X.
```

The source of these two functors is `Y.Modules × Y.Modules` and their target
is `X.Modules`. Thus the proposition requires the canonical map

```text
f^*(tensorObj M N) ⟶ tensorObj (f^*M) (f^*N)
```

to be invertible for all module sheaves `M N : Y.Modules`, naturally in
both factors. `IsIso` applies to the fixed natural transformation, not to a
freely chosen comparison. This uses the existing scheme-module pullback and
the tensor product defined by sheafifying the sectionwise tensor presheaf.
There are no flatness, quasicoherence, local freeness, affineness, or
monoidal-structure hypotheses.

The comparison is imported unchanged from
`Langlands.AlgebraicGeometry.Modules.PullbackTensor`. Its component is the
adjoint, under the existing pullback-pushforward adjunction, of the map
obtained by tensoring the two adjunction units and then applying
`pushforwardTensorApp`. The latter map is characterized on sections by
sending a pure tensor to its image under the tensor sheafification unit,
with scalars restricted along the scheme morphism's structure-sheaf map.
The imported module already proves naturality; the new proposition isolates
the remaining invertibility claim.

The original source is the Stacks Project, Section 17.16 (tag
[01CA](https://stacks.math.columbia.edu/tag/01CA)), which defines the tensor
sheaf by sheafification, and Lemma 17.16.4 (tag
[01CD](https://stacks.math.columbia.edu/tag/01CD)), which identifies
`f^*(F ⊗ G)` with `f^*F ⊗ f^*G` functorially for a morphism of ringed spaces.
This statement specializes that result to schemes and expresses the
identification as invertibility of the already constructed canonical
comparison. The source omits its proof; no proof route is attributed to it.
The natural-transformation formulation is categorical packaging of that
functorial identification.

The retained source is registered as
`stacks-module-tensor-products-2026-10-21`, *Stacks Project - Tensor products
of sheaves of modules (HTML snapshot 2026-10-21)*, SHA256
`825127394e5828c3a56f5134b8823afba20547d7ba5173f624b2f9556a058e34`.

This module only defines the proposition. It supplies neither a proof nor
an `IsIso` instance. A separate proof task must establish it in the pinned
environment. Associativity, unit and symmetry compatibility, and
compatibility with pullback identity and composition, remain separate
obligations of the parent monoidal-pullback development.
