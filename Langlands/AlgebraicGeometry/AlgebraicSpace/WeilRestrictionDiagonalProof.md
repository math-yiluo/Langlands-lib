# Diagonals under finite locally free Weil restriction

Authors: Worker 117 and Worker 160.

The theorem `weilRestrictionDiagonal_proof` proves the exact Library proposition
`Langlands.AlgebraicGeometry.AlgebraicSpace.WeilRestrictionDiagonalStatement`
from `WeilRestrictionGeometricInputsStatement`. For arbitrary commutative rings
`R` and `R'` in universe `u`, with `R'` a finite projective `R`-algebra, and every
quasi-separated algebraic space `X'` over `Spec R'`, the full presheaf diagonal
of its fppf Weil restriction is representable and has quasi-compact scheme
projections. If `X'` is separated, that diagonal is a representable closed
immersion. No finite-type condition on `X'` or on test schemes is imposed.

The target's paired Library Markdown identifies this proposition as a derived
diagonal input for Conrad's Lemma 5.10, rather than the complete lemma. The
implemented proof is an internal equalizer argument using the existing
scheme-Weil and local-representation APIs. It does not construct or assume an
algebraic-space structure on the restricted sheaf.

Worker 117 authored the diagonal geometry, equality-locus geometry,
closedness helpers, the two gluing lemmas in this module and the final theorem.
Worker 160 authored the full-slice section-equalizer and cartesian comparison
constructions and the arbitrary-affine-test assembly, with Worker 117's
geometric inputs. Their paired supporting modules explain those constructions.

The proof first uses
`exists_affineTest_sectionEqualizer_weil`. For every affine scheme `T` over
`Spec R` and every two sections `x`, `y` of the full restricted presheaf over
`T`, this supplies a scheme over `T.left` representing `sectionEqualizer x y`
on all schemes over `T.left`. Its structure map is quasi-compact and is closed
if `X'` is separated. Here affineness is a condition on the scheme carrying the
sections; probes of its equality presheaf remain arbitrary schemes.

The affine-test construction uses the actual coordinate ring `A` of `T` and
the tensor algebra `B = A ⊗[R] R'`. Its upper equality locus is monomorphic,
locally of finite type and quasi-compact. These properties follow from the
original space diagonal, whose local finite type is obtained from an etale
atlas without any finite-type assumption on the space. Over the affine upper
test base, the equality locus is quasi-affine by the Library's quasi-affine
form of Zariski's Main Theorem. Its actual quasi-affine Weil scheme represents
the lower equality locus. The supporting cartesian comparisons ensure this is
a natural representation on the full slice. If the original diagonal is
closed, the same upper equality locus and its Weil scheme have closed
structure maps, using affine Weil preservation of closed immersions and
Yoneda comparison of the affine and quasi-affine representatives.

The lemma `exists_sectionEqualizer_representation_of_affine` extends the
affine-test result to an arbitrary scheme `T` over a scheme `S`. More generally
it takes any fppf sheaf `F` and any scheme morphism property `P` local on the
target. It restricts the two sections to `T.left.affineCover`. The local full
representations are converted by `sectionEqualizerRestrictIso` into
representations of the restriction of one global equality presheaf.
`isSheaf_sectionEqualizer` supplies its fppf sheaf property, and
`LocalRepresentation.exists_representation` glues those local representatives
to an actual scheme over `T.left`. The structure map has property `P` by
`LocalRepresentation.property_of_local_representations`, using uniqueness of
representatives and locality on the target.

The lemma `relative_diagonal_of_affine_sectionEqualizer` applies this gluing
result and converts the resulting full representation isomorphism into a
monomorphic `RepresentsEqualizer` witness through
`representsEqualizer_of_sectionEqualizerIso`. The Library theorem
`relative_diag_of_representsEqualizer` then gives representability of the
full diagonal and property `P` for every represented scheme projection.
Thus the conclusion concerns every scheme test and every represented
projection, not merely the chosen local representatives.

Finally, the restricted presheaf is an fppf sheaf by the actual
`ringWeilRestriction` sheaf functor. The theorem applies the preceding
criterion once with `P = QuasiCompact` and once, under `IsSeparated X'`, with
the scheme closed-immersion property. Each application extracts the relevant
property from the affine-test assembly. These are exactly the two conjuncts
of the unchanged published statement.

All declarations retain universe `u`. The proof introduces no new axioms or
additional geometric assumptions and uses neither a proof of
`SpaceWeilRestrictionStatement` nor its conditional final assembly. The
restricted sheaf's algebraic-space representability and the etale-atlas
prerequisite remain outside the assertion proved here.
