# Existence of the canonical anti-affine quotient

`Langlands.GroupScheme.antiAffineQuotientExistence.{u}` proves the unchanged
`AntiAffineQuotientExistenceStatement.{u}` for every field in its arbitrary
universe and every smooth connected actual group scheme over that field.
It constructs the existing `AntiAffineQuotient` with its actual target,
projection and full scheme kernel. No affine-source, finite-type,
quasi-compactness, perfect-field or algebraic-closedness premise is added.

The proof uses `FieldAffinization.exists_of_smooth_connected` to construct
the actual affine group and actual canonical homomorphism inducing an
isomorphism on global functions. `affinizationGeometry` gives the smooth
connected affine target and the flat surjective quasi-compact projection.
The source is algebraic by the published quasi-compactness theorem and
smoothness, and its closed full kernel is therefore algebraic.
`IsAffinization.antiAffine_kernel` proves anti-affineness of this full kernel
by global-sections base change on the kernel pair. The helper
`antiAffineSmoothConnected` makes it smooth and connected.
`AntiAffineQuotient.ofFlatAffinization` supplies smoothness of the actual
projection by fpqc descent from the smooth kernel and assembles the
unchanged quotient structure. Its `IsAffinization` field identifies the
supplied map with the canonical scheme affinization through the existing
`targetIso` and `comp_targetIso` theorems.

The mathematical source is SGA 3, Exposé VI_B, Theorem 12.2 and Lemma 12.3,
printed pages 430–431 / PDF pages 100–101, Gille–Polo recomposed edition of
13 October 2024. Its Corollary 11.18.1, printed p.427 / PDF p.97, underlies
the geometric image step. Source identifier:
`sga3-expose-vib-gille-polo-2024`, SHA-256
`88d8ccb045fc959535155eb4b0fc72e3e4845730fb73355f2043e8023b7db3d2`.
The complete official Tome I errata dated 13 October 2024 do not alter these
results. The implemented kernel anti-affineness route and the affine
representation of the reduced-subgroup coset space differ from the
successive-quotient route in the source; their helper Markdown describes the
actual Lean constructions.
