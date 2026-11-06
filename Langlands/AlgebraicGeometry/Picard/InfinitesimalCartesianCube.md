# Sections of cartesian cubes over affine open immersions

This internal prerequisite proves the actual global-sections ring pullback for
any cartesian cube over an affine open immersion into the relative space over
`R`. It extends the inverse-image-open specialization in
`InfinitesimalAffineOpenSquare` to arbitrary supplied cartesian faces.

The coefficient `k` is any field, and `R, A, B, C` are arbitrary commutative
`k`-algebras at the same universe. The maps `p, q, a, b` form a categorical
pullback of their actual underlying ring maps. The family morphism
`f : X ⟶ Spec k` is arbitrary.

`baseProjection f t` is the composite of
`t : T ⟶ (relativeSpace f).obj (affineBase k R)` with the actual relative
projection to `Spec R`. When `t` is an open immersion, this composite is flat:
the relative projection is a base change of a morphism to the spectrum of a
field, and an open immersion is flat.

`cartesianCube_appTop_isPullback` assumes additionally that `T` is affine.
It takes schemes `T₀, T₁, T₂`, maps `s₁ : T₁ ⟶ T`, `s₂ : T₂ ⟶ T`,
`ι₁ : T₀ ⟶ T₁`, `ι₂ : T₀ ⟶ T₂`, and maps `g₁, g₂, g₀` to the actual
relative spaces over `A, B, C`. Its three cartesian hypotheses identify the
`A` and `B` faces as pullbacks along `t`, and the `C` face as the pullback
along `g₁` of the relative map induced by `a`. The remaining face equation is
`ι₂ ≫ g₂ = g₀ ≫ relativeSpace.map (affineBaseMap b)`, and the top square
commutes as `ι₁ ≫ s₁ = ι₂ ≫ s₂`. It concludes precisely

```text
IsPullback s₁.appTop s₂.appTop ι₁.appTop ι₂.appTop.
```

The proof transports the original ring pullback to the global sections of the
four spectra using `Scheme.ΓSpecIso`. It pastes the supplied cartesian faces
with `relativeProjection_isPullback`; the `C` face uses the pasting of the
first and third supplied faces. The two face compatibility equations follow
from those of the cube and naturality of the relative projection. The
published `InfinitesimalAffineOpenSquare.affineCube_appTop_isPullback` then
applies to the flat `baseProjection f t`.

The provenance is internal, derived from the published relative-space and
affine-square sections constructions and Mathlib's pullback pasting,
flatness and spectrum-section interfaces. No particular choice of pullback
objects or inverse-image opens is imposed. Properness of `f`, surjectivity
and nilpotence of a ring map, and finiteness conditions on the test algebras
are unnecessary. This local ring result is a prerequisite for the global
Picard gluing proof; it does not assert that the Picard comparison is an
equivalence.
