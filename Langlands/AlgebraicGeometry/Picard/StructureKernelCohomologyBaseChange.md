# Flat scalar cohomology base change for the actual structure-map kernel

This is an internal composition of the published
`StructureKernelFlatBaseChange.kernelModuleFlatBaseChangeIso` and
`CechResolution.quasicoherentScalarBaseChangeIso`. The coefficient is the actual
sectionwise ideal module `StructureKernelModule.kernelModule`, whose sections
are the kernel of the scheme structure map. All schemes and commutative rings
are in an arbitrary common universe `u`.

## Compatibility of the kernel identification with inclusion

`kernelModuleIso_hom_ι` and `kernelModuleIso_inv_ι` show that the published
identification with the categorical kernel preserves the actual inclusion
`kernelModuleι` in both directions. They are the two projection identities
for the unique isomorphism between limiting cones.

For a cartesian square

```text
Y' --p--> Y
 |        |
 i'       i
 |        |
 v        v
X' --b--> X
```

with affine `i` and flat `b`, `kernelModuleFlatBaseChangeIso_ι` proves

```text
(kernelModuleFlatBaseChangeIso b i i' p h).hom ≫ kernelModuleι i'
  = b^*(kernelModuleι i) ≫ (pullbackUnitIso b).hom.
```

The proof expands the four isomorphisms in the published comparison: pullback
of the actual-to-categorical kernel identification, preservation of the
categorical kernel by flat pullback, the induced map of kernels, and the
inverse actual-to-categorical identification. Their inclusion identities
give the displayed equation. No cohomological, compactness, separatedness,
or square-zero assumption is used in this calculation.

## Relative scalar cohomology comparison

Let `φ : R ⟶ S`, `f : X ⟶ Spec R`, and `f' : X' ⟶ Spec S`, with a second
cartesian square

```text
X' --b--> X
 |        |
 f'       f
 |        |
 v        v
Spec S --> Spec R.
```

Assume that `φ.hom` is flat, `f` is separated, `X` is quasi-compact
(`CompactSpace X`), and `i` is affine. Write `I = kernelModule i` and
`I' = kernelModule i'`. For every `n : ℕ`,
`kernelModuleCohomologyFlatBaseChangeIso` constructs an isomorphism of
`S`-modules

```text
S ⊗_R (relativeCohomology f n).obj I
  ≅ (relativeCohomology f' n).obj I'.
```

Here `relativeCohomology f n` is the actual right-derived functor of
`R`-module global sections over `f`. Affineness of `b` follows from base
change of the morphism between affine schemes, and flatness of `b` follows
from flatness of `φ.hom`; these facts are proved by `baseChange_isAffine`
and `baseChange_flat`. Neither is an additional hypothesis of the comparison.
The published `kernelModule_isQuasicoherent` supplies quasi-coherence of `I`.
The construction then composes the canonical scalar comparison for `I`
with the image of the actual kernel comparison under
`relativeCohomology f' n`.

`kernelModuleCohomologyFlatBaseChangeIso_hom` identifies the forward map
with `scalarBaseChangeMap` followed by this cohomology map of the kernel
comparison. `kernelModuleCohomologyFlatBaseChangeIso_one_tmul` evaluates it
at `1 ⊗ x`: the result is the published semilinear `baseChangeMap` of `x`,
followed by the same cohomology map. The local instances displayed in these
two equations are precisely the affineness, flatness, and quasi-coherence
already derived above.

`structureModuleCohomologyFlatBaseChangeIso` constructs the corresponding
comparison for the structure modules, using `pullbackUnitIso`. It requires
only the second cartesian square, flat `φ.hom`, separated `f`, and
quasi-compact `X`. `kernelModuleCohomologyFlatBaseChangeIso_ι` proves that
the two comparisons commute with the actual ideal inclusions on
cohomology. Its proof combines coefficient naturality of the published
scalar comparison with the kernel-inclusion identity above.

## Relation to cohomology over the global section ring

`DerivedSections.cohomology X n` takes values in modules over `Γ(X, ⊤)`.
It is related to relative cohomology by the published canonical
`relativeCohomologyRestrictScalarsIso f n`, which restricts scalars along
`structureRingHom f : R ⟶ Γ(X, ⊤)`.

`kernelModuleCohomologyRestrictScalarsBaseChangeIso` conjugates the relative
comparison by these isomorphisms. Its source is scalar extension from `R`
to `S` of the restricted `Γ(X, ⊤)`-module cohomology of `I`; its target is
the `Γ(X', ⊤)`-module cohomology of `I'` restricted to `S`. This explicitly
records the scalar restrictions rather than identifying the two derived
functors definitionally.

The construction imposes no square-zero, closed-immersion, noetherian,
properness, finite-presentation, or source-flatness hypothesis. It proves
no compatibility with the abelian-sheaf comparison or the multiplicative
unit-sequence boundaries, no scalar stability of a boundary image, and no
naturality or representability of Picard lifting fibres. Those remain
separate obligations in the full Picard representability argument.
