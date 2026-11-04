# Translation spaces between actual torus embeddings

Author: Worker 118.

For an arbitrary field `k`, let `i : S.toGrp → G` and `j : S'.toGrp → H`
be morphisms into affine group schemes. Supply actual isomorphisms `e : S ≅ S'`
and `f : G ≅ H` with the commuting square
`i ≫ f.hom = groupHom e.hom ≫ j`. No splitness, reductivity, nonempty root
set, or surjectivity on rational points is assumed.

`translationSpaceTransportEquiv e f h` is the linear equivalence from
`TranslationSpace i` to `TranslationSpace j` induced by the published
`cocharacterRealCongr e`. On a representative `v : V S` it sends `[v]` to
`[cocharacterRealCongr e v]`. On pure tensors the latter map is
`r ⊗ ν ↦ r ⊗ (ν ≫ e.hom)`, so this is the original actual torus map on
cocharacters.

The construction uses the actual relative-root bijection already proved for
the commuting square. Invariance of the integral lattice pairing, extended
to real scalars in `FiniteRealTorusSpace`, gives
`eval S' (characterLattice.congr e a) (cocharacterRealCongr e v) = eval S a v`.
Consequently it preserves and reflects membership in the common root kernel.
Surjectivity of the linear equivalence identifies the two kernel submodules,
and Mathlib's quotient equivalence supplies the displayed constructor.
The root-form identity is the same evaluation identity on quotient
representatives, for the published actual root bijection.

When the two inclusions are monomorphisms, the original normalizer derivative
is intertwined by this equivalence. The normalizer point on the target is
exactly `normalizerPointsTransportEquiv e f h n`, with underlying point
`n ≫ f.hom`. Uniqueness of the normalizing automorphism identifies its torus
automorphism with `e.symm ≪≫ normalizingAut i n ≪≫ e`. Tensor induction
then proves compatibility on `V S`; quotient induction proves compatibility
of the original `translationAction` on the reduced translation spaces.

This unit has internal provenance: it constructs the induced quotient of
the published actual character, cocharacter, root and normalizer transport
maps and proves its intrinsic identities. It introduces no external theorem
or additional mathematical existence premise. It does not construct or compare
valuation families, apartment points, apartment intersections, valid building
data or the full cross-torus A2 axiom. Those remain separate constructions.
