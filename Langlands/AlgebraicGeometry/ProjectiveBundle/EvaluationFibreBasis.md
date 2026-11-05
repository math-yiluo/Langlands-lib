# A genuine basis of the original-residue-field coefficients

This internal derived construction works with schemes in one arbitrary
universe. For a module sheaf `M` on `S`, a frame has `n + 1` entries.
`exists_affine_frameOpen` proves that fixed-rank local freeness
`IsLocallyFreeOfRank M (n + 1)` supplies an affine frame open containing
each point of `S`. Its proof chooses an existing frame open, refines it
to an affine neighborhood of the point, and restricts the frame.

For any actual `LocalFrame M n U`, `LocalFrame.sectionBasis` is a basis
of `Γ(M, U)` over `Γ(S, U)`, indexed by `Fin (n + 1)`. It is obtained
from the frame's coordinate linear equivalence. The proved entry formula
`LocalFrame.sectionBasis_apply` identifies this basis with the frame's
existing `basisSection` family over `U`. This construction does not
require affine or quasi-coherent hypotheses.

Now assume that `M` is quasi-coherent, choose an affine frame open
`U : FrameOpen M n`, and let `s ∈ U.val`. The actual residue-point map
`S.fromSpecResidueField s` lands entirely in this open.
`fibreFrameBasis` constructs a basis of the global sections of the
actual pulled-back sheaf
`(Scheme.Modules.pullback (S.fromSpecResidueField s)).obj M`, over the
ring `Γ(Spec (S.residueField s), ⊤)`, with the same index set
`Fin (n + 1)`. It uses the original residue spectrum, without replacing
its field by the residue field of an open subscheme.

The private construction `affineSectionPullbackBasis` applies more
generally to a quasi-coherent sheaf, affine source and target opens,
and an actual basis on the target open. It extends scalars along
`f.appLE`, then transports the resulting tensor-product basis through
the published bijective `pullbackTensorMap`. The latter sends
`1 ⊗ σ` to `sectionPullbackLE f M h σ`. The tensor basis entry
formula therefore proves the entry formula for the transported basis.
Specializing this construction and the frame section formula proves
`fibreFrameBasis_apply`: every entry is exactly the previously
constructed `fibreFrameSections U s hs i`.

The provenance is internal: the proof combines the implemented frame
coordinate equivalence, restriction of frames, affine refinement, the
affine section pullback comparison, and the tensor-product basis
construction. No rank or invertibility hypothesis is imposed on the
canonical direct-image base-change comparison. This is a basis of the
pulled-back coefficient sheaf's global sections; identifying it with a
basis of the full fibre direct image still requires that separate
comparison theorem. Cubic rank, cohomology, generation from abelian
geometry, very ampleness, and representability remain open obligations.
