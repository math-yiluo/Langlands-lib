# Vanishing after arbitrary affine base change

The theorem
`Langlands.AlgebraicGeometry.Modules.higherDirectImageVanishingAffineBaseChange`
proves the entire published proposition
`Langlands.AlgebraicGeometry.Modules.HigherDirectImageVanishingAffineBaseChangeStatement.{u}`.
It has this exact type in arbitrary universe `u`, with no outer parameters
or extra hypotheses.

For schemes `X` and `Y`, a smooth proper morphism `f : X ⟶ Y`, and an actual
line bundle `Q : Picard.LineBundle X`, assume that
`(DerivedSections.higherDirectImage f n).obj Q.obj` is zero for every natural
degree `n`, including zero. For every commutative ring object
`R : CommRingCat.{u}`, arbitrary `x : Spec R ⟶ Y`, and `n : ℕ`, the theorem
proves that

```lean
IsZero
  ((DerivedSections.relativeCohomology (pullback.snd f x) n).obj
    ((Scheme.Modules.pullback (pullback.fst f x)).obj Q.obj))
```

These are the actual scheme-module pushforward, pullback, and relative
cohomology functors. The affine base change need not be flat, and its image
need not lie in one affine open of `Y`.

## Implemented proof

For each affine open `V` of `Y`, the proved
`DerivedSections.isZero_higherDirectImage_pullback` from
`HigherDirectImageOpenRestriction` transports the assumed vanishing to
the higher direct images along `f ∣_ V` of the pullback of `Q.obj` to
`f ⁻¹ᵁ V`. Its comparison identifies these objects with the restrictions
of the original higher direct images; restriction and pullback along an
open immersion are isomorphic. The result covers every natural degree.

Apply `DerivedSections.isZero_relativeCohomology_of_higherDirectImage`
to `f ∣_ V` and the affine identification
`hV.isoSpec.hom : V ⟶ Spec Γ(Y,V)`. This gives zero relative cohomology of
the restricted line bundle over every affine restriction of the family,
again in every natural degree.

The final step is the proved
`DerivedSections.isZero_relativeCohomology_pullback_of_affineRestricts`
from `AffineBaseChangeVanishing`. Its affine scalar-change argument uses
the proved `universalPerfectSections` to represent sections by a bounded
finite-projective complex. Joint natural-degree vanishing, together with
negative-degree vanishing of the right-derived complex, makes that
representative acyclic. The bounded-above flat-complex theorem
`ModuleComplex.exactAt_baseChange_of_flat` preserves its acyclicity after
arbitrary scalar extension. The perfect-sections comparison then returns
vanishing of the actual relative cohomology.

For arbitrary `Y` and `x`, that helper uses the basis
`DerivedSections.affineSubordinateBasis x`: affine opens `W` of `Spec R`
contained in the inverse image of some affine open `V` of `Y`. On each
such `W`, pullback pasting and the affine identifications transport the
scalar-change vanishing to the open cohomology of the base-changed
family. Basis detection gives zero higher direct images of the second
projection. The total-vanishing comparison over `Spec R` gives the required
relative cohomology. All these inputs are proved imported results.

## Original sources and derived specialization

This theorem is a derived consequence of the Stacks Project's proper
perfect direct-image and arbitrary-base-change results, using their
affine perfect-representative route. The registered original is
`stacks-perfect-complexes-a04446e5`, folder SHA256
`54c831042614714cdb007a024d45dca7f60709efe2c307389ca2ad848b0ccbed`,
at commit `a04446e57ec1fbc252a871afcec7752fb2807b14`. In `perfect.tex`,
the relevant complete passages are the supporting lemma and proof at
lines 7396–7441, the remark `remark-explain-perfect-direct-image`
(tag 0A1I) at lines 7443–7455, and
`lemma-flat-proper-perfect-direct-image-general` (tag 0B91) and its proof
at lines 7524–7544.

A smooth proper morphism is flat and of finite presentation, and a line
bundle is a perfect coefficient flat over the base. These supply the
hypotheses of the imported perfect-sections theorem. The proof here
combines that theorem with acyclicity under ordinary scalar extension,
restriction of higher direct images, and affine-local detection. It is
not a transcription of a separately numbered source result.

The retained supplement
`stacks-universal-perfect-sections-comments-20261029` records the tag 0B91
comments #4352 and #4499: part (2) retains flatness of the coefficient
over the base and does not require flatness of the morphism. The pinned
TeX includes this correction; the present smooth specialization already
satisfies the stronger flat-morphism condition.
