# Field-valued fibres of relative groups of multiplicative type

`RelativeMultiplicativeType.FieldSplittingData G` retains a field extension of
the ground field, a finitely generated abelian character group and an actual
diagonalizing isomorphism after base change. The construction
`IsMultiplicativeType.fieldSplitting` chooses this data from a relative
diagonalizing cover over a field using the comparison proved below. It is a
noncomputable choice of splitting data, with no uniqueness or naturality claim.
The chosen model retains torsion in the character group.

`Langlands.GroupScheme.relativeMultiplicativeTypeField` proves the proposition
`Langlands.GroupScheme.RelativeMultiplicativeTypeFieldStatement` by the
field-valued-fibre construction below.

This is an internal comparison between the two existing Library predicates for
multiplicative type. It proves one direction over a field and its consequences
for fibres; it does not assert the fibral converse or any torsion-rank result.

`RelativeMultiplicativeType.IsMultiplicativeType.isMultiplicativeType` sends the
relative predicate over `Spec k` to the field predicate. Choose a point in a
member of the fppf diagonalizing cover above the unique point of `Spec k`, and
let `K` be its residue field. The composed map `Spec K → Spec k` equips `K`
with its `k`-algebra structure. Pull back the given diagonalizing isomorphism
along this point. Base-change composition and the published comparison
`Diagonalizable.relativeModelIso` identify the resulting model with the actual
diagonalizable group over `K`, retaining its finitely generated character group.
This gives exactly the extension and isomorphism in the field predicate.

`IsMultiplicativeType.fieldFiber` first uses the published arbitrary-base-change
stability of the relative predicate and then applies that comparison.
`IsMultiplicativeType.geometricFiber` specializes to the Library's geometric
point through the algebraic closure of the residue field. All universes are
arbitrary; there are no flatness, presentation, affineness, commutativity or
connectedness hypotheses on the input group. These are proved implications,
not an equivalence between the two predicates.

The proof route is the residue-field-of-a-cover-member construction already used
in `RelativeFieldComparison` for tori, together with the published affine and
relative diagonalizable model comparison. It is derived from these Library
constructions and does not rely on an additional external theorem.
