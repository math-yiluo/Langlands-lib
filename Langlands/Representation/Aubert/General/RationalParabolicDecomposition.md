# Standard rational-point decompositions from standard cocharacters

Worker 165 constructed this internal adapter. It combines the published
standard subgroup functors and `StandardCocharacterStatement` with the proved
dynamic decomposition used by `General.DynamicParabolic`. It introduces no
replacement standard-family definition and proves no instance of the
standard-cocharacter assertion.

Let `k : Type u` be any field, let `T` be a commutative group scheme and `G` a
group scheme over `Spec k` with affine structural morphism, let
`i : T.toGrp ⟶ G`, and let `ν` be a cocharacter of `T`. Each index `I` is a
finite subset of the actual subtype `SimpleRoot i ν`. The associated
`rootSet i ν I` is the image of those actual characters. The three subgroup
families are exactly the existing `parabolic`, `levi` and `unipotent`, evaluated
at the identity test object.

`isSemidirectDecomposition_of_dynamic` assumes separatedness and three
equalities of subgroup functors with the dynamic parabolic, centralizer and
unipotent functors of a given field-defined cocharacter `χ` of `G`. Evaluating
these equalities at the identity test object rewrites the desired decomposition
to `dynamic_isSemidirectDecomposition`. Thus the full complement, normalization
and containment conditions are proved from the existing dynamic theorem.

`isSemidirectDecomposition_of_standardCocharacterStatement` takes the existing
universal proposition `StandardCocharacterStatement` explicitly. It also takes
`IsConnectedReductive G`, `IsMaximalSplitTorus i` and
`IsGenericCocharacter i ν`. The first supplies separatedness. Applying the
standard-cocharacter assertion to `rootSet i ν I` supplies a standard
cocharacter and all three dynamic equalities, so the first theorem applies.
The existence clause is used: the proof does not infer a decomposition merely
from the definition as an intersection over a possibly empty witness family.
There is no additional chosen cocharacter in the resulting decomposition.

`standardProjection` uses that proved decomposition to construct the monoid
homomorphism from the exact standard parabolic point subgroup to the exact
standard Levi point subgroup. It takes the same explicit structural assertion
and geometric hypotheses.

`projection_eq_dynamic_limit` works with any semidirect decomposition of
these same standard point subgroups and with any realization by the three
dynamic point subgroups. On each standard parabolic point, its projection
equals the actual `Dynamic.limit` of that point. The proof first places the
limit in the standard Levi. The dynamic limit theorem gives
`p (lim p)⁻¹` in the unipotent subgroup; conjugating by `(lim p)⁻¹` gives
`(lim p)⁻¹ p` there. The existing characterization
`projection_eq_iff` then identifies the projection. This is equality of
ambient rational points, and preserves every parabolic representative.

No topology, finiteness, endpoint identity, standard Levi intersection,
finite-length preservation or representation-theoretic identity is established.
`StandardCocharacterStatement` remains an unproved, explicitly named shared
structural assertion. Calling it an argument does not classify it as an allowed
external input or discharge the parent's retained proof obligations. The
construction is valid without a positive-rank or nonempty-root hypothesis,
and adds no restriction on the characteristic.

The provenance is internal: subgroup-functor evaluation, the existing
standard-cocharacter proposition, and the existing dynamic decomposition and
projection characterization imply the construction and three theorems above. There is
no additional literature assertion attributed to this adapter.
