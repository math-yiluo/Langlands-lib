# Full fibre sections under the canonical comparison isomorphism

This internal derived construction works with schemes in one arbitrary
universe. Its inputs are an actual morphism `p : X ⟶ S`, a line bundle
`L` on `X`, a quasi-coherent module sheaf `M` on `S`, and a morphism
`ev : M ⟶ p_* L.obj`. Choose an affine frame open `U` for `M` with
`n + 1` entries and a point `s ∈ U.val`. The residue field throughout
is the original `S.residueField s`.

The construction explicitly assumes that the canonical morphism
`baseChangeEvaluation p L ev` for the actual fibre square is an
isomorphism. This morphism is the pullback of `ev` followed by the
canonical direct-image base-change comparison. Its target is the
pushforward of the actual single pullback of `L` along `p.fiberι s`.
Invertibility is a retained premise, rather than a result of this file.

`fibreFullSectionBasis` is a genuine basis indexed by `Fin (n + 1)`,
over `S.residueField s`, of
`(relativeGlobalSections (p.fiberToSpecResidueField s)).obj`
applied to the actual fibre line bundle's module sheaf. Thus it is a
basis of all global sections of that line bundle, with their scalars
from the specified morphism to the original residue spectrum.

The proof starts with the actual coefficient basis `fibreFrameBasis`.
It applies global sections to the assumed canonical isomorphism and
transports the basis through the resulting linear equivalence. The
private construction `specSectionBasis` then changes coefficients from
`Γ(Spec R, ⊤)` to `R` using `Scheme.ΓSpecIso R`. The scalar action in
`moduleSpecΓFunctor` is restriction along the inverse of that
isomorphism, so the two actions agree. Mathlib's `Basis.mapCoeffs`
therefore changes scalars and preserves the basis entries.

`fibreFullSectionBasis_apply` proves that each basis entry is exactly
`fibreFrameEvaluation p L ev U s hs i`, the section obtained by
applying the actual canonical changed evaluation to the pulled-back
frame coefficient. Its proof uses preservation of entries under the
scalar change and basis transport, followed by `fibreFrameBasis_apply`.

The final two lemmas additionally retain
`hgen : FrameEvaluationGenerates p L ev n`.
`fibreFullSectionBasis_generate` proves pointwise generation of the
actual fibre line bundle by these basis sections using the entry
formula and `fibreFrameEvaluation_generate`.
`fibreFullSectionBasis_coordinates` identifies their actual relative
linear-system map with `fibreEvaluationCoordinates`, by equality of
the ordered section families and the existing coordinate comparison.
The latter map is the previously constructed coordinate morphism of
the whole-fibre evaluation in a chosen frame.

The provenance is internal: this file combines the implemented affine
coefficient basis and canonical fibre evaluation with functoriality of
global sections and Mathlib's basis transport and coefficient change.
It supplies no theorem establishing the canonical comparison's
invertibility, cubic rank, generation from abelian geometry, very
ampleness, or ordinary representability.
