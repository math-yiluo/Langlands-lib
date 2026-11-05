# Adjoint evaluation and intrinsic generation

This module derives a sufficient condition for the intrinsic generation used by
projective evaluation. Its inputs are actual scheme-module pullback and
pushforward, their adjunction, the affine pullback-section comparison in
`Modules.PullbackAffineSections`, affine surjectivity for quasi-coherent sheaves
in `Modules.CoherentClosure`, and field line-bundle triviality in
`Picard.FieldLineBundleTrivialityProof`. This is an internal derivation with no
new external literature assertion.

Fix schemes `X` and `S` in the same arbitrary universe, a morphism
`p : X ⟶ S`, a module sheaf `M` on `S`, a line bundle `L` on `X`, and an actual
morphism `ev : M ⟶ p_*L`.

`evaluationAdjoint p L ev` is the actual morphism `p^*M ⟶ L` corresponding to
`ev` under the pullback-pushforward adjunction. Its section formula says that
applying it to the pullback of a section `σ` over `U` gives `ev.app U σ` over
`p⁻¹U`. The restricted version gives the restriction of the same evaluation on
any smaller total-space open.

`localEvaluationAdjoint p L ev U` pulls back that morphism along the actual
open inclusion `ι : p⁻¹U ⟶ X`, using the inverse canonical composition
comparison to give source `(ι ≫ p)^*M`. Its target is the actual restriction
of `L` to `p⁻¹U`. It takes the restricted pullback of `σ` to
`localSectionEvaluation p L ev U σ`. Pullback preserves epimorphisms, so this
local adjoint is epi whenever the original adjoint is epi.

`evaluationGenerates_of_epi_evaluationAdjoint` assumes that `M` is
quasi-coherent and the actual adjoint is an epimorphism. It proves
`EvaluationGenerates p L ev`: every point has a base-open neighborhood and a
section of `M` there whose evaluation has nonzero residue-field value.
No local freeness, finite rank, noetherian, properness, or base-change
hypothesis is required for this implication.

The proof chooses an affine base open `U` containing `p(x)`, views `x` as a
point `y` of `p⁻¹U`, and pulls the local adjoint to `Spec κ(y)`. The inverse
canonical pullback-composition comparison gives an epimorphism from the
pullback of `M` along the composite map to `S` to the residue line bundle.
The section formulas identify its value on each pulled-back base section
with the residue of the local evaluated section. If all those residues were
zero, the affine tensor-section comparison and induction on tensors would
make the map zero on all global sections. Its source and target are
quasi-coherent, so the epimorphism is surjective on global sections of the
field spectrum. The residue line bundle is trivial by the existing field
triviality theorem; the inverse image of the nonzero structure-sheaf section
`1` contradicts this vanishing.

`frameEvaluationGenerates_of_epi_evaluationAdjoint` applies the existing
intrinsic-to-frame implication, giving `FrameEvaluationGenerates p L ev n`
for each `n`. As in that condition's definition, it concerns the opens
carrying frames of the specified rank. Local freeness of rank `n+1` is still
needed to ensure those opens cover the base when constructing the global
projective evaluation map.

This module does not prove the converse from intrinsic generation to
epimorphy. It does not establish cubic evaluation surjectivity or a cubic
embedding, and it does not prove ordinary full-level moduli representability.
