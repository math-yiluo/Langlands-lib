# Tensor-invertible scheme modules are locally free of rank one

This module proves the published proposition
`Langlands.AlgebraicGeometry.Picard.TensorInvertibleLocallyFreeRankOneStatement`
from `Langlands.AlgebraicGeometry.Picard.LocalComparisonDirections`, which it
imports unchanged. The theorem is

```lean
theorem tensorInvertibleLocallyFreeRankOne
    (X : AlgebraicGeometry.Scheme.{u}) :
    TensorInvertibleLocallyFreeRankOneStatement X
```

in namespace `Langlands.AlgebraicGeometry.Picard`, for arbitrary universe `u`.
It says that every actual module sheaf `M : X.Modules` with a tensor inverse
is locally free of rank one. The tensor is the published symmetric monoidal
tensor on scheme-module sheaves, whose unit is the structure module.

The conclusion is the actual neighborhood condition: for every `x : X`,
there is an open `U : X.Opens` with `x ∈ U` and an isomorphism

```text
M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf.
```

There are no additional hypotheses on `X` or `M`.

## Implemented proof

Fix `M`, its tensor-invertibility witness, and a point `x`. Unpacking
`Langlands.CategoryTheory.TensorInvertible M` gives a module sheaf `N` and
an isomorphism `e : M ⊗ N ≅ 𝟙_ X.Modules`.

Apply the published theorem
`Langlands.Scheme.Modules.tensorLocalUnitFactorization X M N e x`, imported
from `Langlands.AlgebraicGeometry.Modules.TensorLocalUnitFactorizationProof`.
It supplies an open `U` containing `x` and morphisms

```text
s : 𝟙_ U.toScheme.Modules ⟶ M.restrict U.ι
t : 𝟙_ U.toScheme.Modules ⟶ N.restrict U.ι
```

with `hst : IsIso (s ⊗ₘ t)`.

Apply the published theorem
`Langlands.CategoryTheory.Picard.unitTensorCancellation`, imported from
`Langlands.CategoryTheory.Picard.UnitTensorCancellationProof`, to the
braided monoidal category `U.toScheme.Modules` and these two morphisms.
Its first conclusion gives `IsIso s`. Install this as a local instance.
Then `(asIso s).symm` is the required isomorphism from `M.restrict U.ι` to
the structure module. The identification of the actual monoidal unit with
`SheafOfModules.unit U.toScheme.ringCatSheaf` is definitional. The witnesses
returned by Lean are `U`, its membership proof, and this isomorphism.

The geometric prerequisite already proves the local finite pure-tensor
expansion, selection of a scalar with unit germ in the scheme local ring,
shrinking to its basic open, and the section-pairing calculation through the
actual restriction/tensor comparison. In particular it imports the separately
proved `Langlands.Scheme.Modules.restrictTensorComparison`. The categorical
prerequisite separately proves that invertibility of the tensor of two maps
from the unit forces both maps to be isomorphisms. This module imports those
results by Lean name and performs only their final assembly.

## Source and provenance

The registered source is
`stacks-local-freeness-invertibility-sections-2026-10-21`, content SHA-256
`6d1641a9deb284be889ee6e2630a2be6e57cc5985c80af2c9da7d17543ed0785`.
The retained folder is *Stacks Project - Locally free sheaves and invertible
modules, Sections 17.14 and 17.25 (HTML snapshot 2026-10-21)*.

In `01C5.html`, [Definition 17.14.1(3)](https://stacks.math.columbia.edu/tag/01C6)
gives local freeness of fixed finite rank. In `01CR.html`,
[Lemma 17.25.2](https://stacks.math.columbia.edu/tag/0B8K) relates the tensor
functor definition of invertibility in
[Definition 17.25.1](https://stacks.math.columbia.edu/tag/01CS) to a tensor
inverse. [Lemma 17.25.4](https://stacks.math.columbia.edu/tag/0B8M) gives the
rank-one comparison when the structure-sheaf stalks are local rings, as they
are for schemes.

This implementation uses the internal unit-pairing route described above.
The source's converse proof instead derives finite presentation and spreads
a stalk basis. The finite expansion in the proof of Lemma 17.25.2 motivates
the geometric prerequisite; the present assembly does not derive or assume
finite presentation. Worker 124 authored the assembly. The cited definitions
and proofs were read in the retained source, and no source-specific project
erratum was found.

This module proves only the implication from tensor-invertibility to local
freeness of rank one.
