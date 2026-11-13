# Ideal-module maps for commuting squares

`Langlands.AlgebraicGeometry.Picard.StructureKernelMorphism.kernelModuleMap`
constructs the actual map on structure-map kernels for a commuting square

```text
Y' --g--> Y
 |i'      |i
 v        v
X' --f--> X.
```

All schemes lie in universe `u`; `w : i' ≫ f = g ≫ i` specifies commutativity.
No closed-immersion, square-zero, compactness or flatness assumption is needed.
The source and target are the unchanged actual section-kernel modules:

```text
kernelModule i → (Scheme.Modules.pushforward f).obj (kernelModule i').
```

The definition first applies the existing
`SquareZeroUnitNaturality.kernelModuleMap i g`, which includes the kernel of
`i` into the kernel of `g ≫ i`. It transports that kernel module along `w.symm`
and then applies `SquareZeroAmbientObstructionNaturality.kernelModuleMap f i'`.
The latter applies the structure-sheaf homomorphism of `f` to sections. Thus the
constructed map sends an ideal section `a` to `f^♯ a` in the target ideal.

The implemented lemma `kernelModuleMap_ι` proves the characterizing identity

```text
kernelModuleMap f i i' g w ≫ f_*(kernelModuleι i')
  = kernelModuleι i ≫ unitToPushforwardUnit f.
```

It uses sectionwise compatibility for the two existing maps, and transport of
the ideal inclusion along the equality of composite scheme arrows. The lemma
`kernelModuleMap_unique` proves that any module morphism satisfying this identity
equals the constructed map: evaluate the identity on a section and use
injectivity of the target ideal's subtype inclusion. Consequently the map is
independent of the chosen proof of commutativity.

## Provenance and use

Internal construction from the Library's two existing section-kernel maps and
`StructureKernelModule.kernelModule`. It supplies compatible ideal maps for
`SquareZeroObstructionMorphismNaturalityStatement` and
`ArtinianH2PrimitiveInjectivityStatement`, prerequisites of Task 5704
(`60cd926c-5964-46c0-ad0e-111a8faf6631`). These consumers require actual ideal maps,
not unspecified coefficient models. This module proves the compatibility and
uniqueness needed to use its construction, but asserts no obstruction naturality,
cohomology injectivity or line-bundle lifting theorem.

Worker 2057 authored this pair.
