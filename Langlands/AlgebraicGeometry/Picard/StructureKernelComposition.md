# Actual structure-kernel maps under a factorization

This internal construction works in every common universe `u` with actual
scheme maps `j : Z → Y` and `h : Y → X`. It constructs the morphism

```text
kernelModule (j ≫ h) → h_* kernelModule j.
```

Here `kernelModule` is the unchanged sectionwise kernel of the actual
structure sheaf map, with its section-ring module action. No flatness,
closed-immersion, or square-zero hypothesis is needed for this sheaf map.

## Sections and the inclusion square

For an open `U` of `X` and a section `a` in the kernel of the composite,
`compositionMap j h` reuses
`SquareZeroAmbientObstructionNaturality.kernelModuleMap h j` and sends `a`
to `h.app U a.val`. The kernel condition is the original condition for the
composite. The reused map supplies naturality and section-ring linearity
from the structure sheaf map of `h`. `compositionMap_app` records the same
section formula.

`compositionMap_ι` proves the square with the actual kernel inclusions:

```text
compositionMap j h ≫ h_* (kernelModuleι j)
  = kernelModuleι (j ≫ h) ≫ unitToPushforwardUnit h.
```

The proof checks actual sections and is definitional after the inclusions
are unfolded.

## Cohomology and specified base scalars

Assume both `h` and `j` are affine morphisms. Supply commutative rings
`R`, `S`, a ring morphism `φ : R → S`, structure morphisms
`p : X → Spec R`, `p' : Y → Spec S`, and an equality
`h ≫ p = p' ≫ Spec.map φ`. Then `compositionCohomologyMap` constructs

```text
H^n_R(X, kernelModule (j ≫ h)) →
  restrictScalars φ (H^n_S(Y, kernelModule j)).
```

It applies relative cohomology to `compositionMap`, composes with the
inverse affine-pushforward cohomology isomorphism, and then with
`relativeCohomologyBaseRingIso` for the supplied square. Quasi-coherence
of `kernelModule j` comes from the imported affine structure-kernel
result. The source-ring scalars and the specified scalar restriction
are retained in the result.

## Provenance and scope

This is an internal construction from the actual structure maps, the
existing sectionwise kernel module, and the imported affine-pushforward
and base-ring cohomology comparisons. The implemented proof is described
above; no additional literature assertion is made. Compatibility with
tensor coordinates or Picard obstruction classes is not established by
this pair. The construction is a prerequisite for coefficient-change
naturality and does not prove the exact Picard atlas.
