# Closedness of the actual Picard diagonal from class loci and an atlas

Author: Worker 509.

This internal assembly has two explicit geometric inputs. The first is
`FieldPicardClassEqualizerImmersionStatement`, concerning the fppf class
loci of pairs of actual line bundles on every scheme test. The second is an
actual etale-surjective scheme atlas of the full fppf Picard class sheaf,
locally of finite type over the field. For an arbitrary proper scheme over
an arbitrary field in universe `u`, these imply a closed-immersion diagonal.
The construction `fieldPicardSectionClosedEqualizer` then chooses an actual
closed equalizer locus for any pair of sheaf sections, with its factorization
criterion on every further scheme test. The immersion gives uniqueness of
such factorizations. The sections need not have global line-bundle
representatives.

The proof first applies the local-representative and fppf-descent bridge to
obtain representability by immersions of the full class-sheaf diagonal.
The generic relative-diagonal isomorphism transport lemma transfers this
property to the underlying presheaf of the actual abelian-group-valued
Picard sheaf through `RelativePicard.forgetSheafIso`. The given atlas is
composed with the inverse of the same natural isomorphism; this preserves
its etaleness, geometric surjectivity and actual source scheme.

The field-group closed-diagonal theorem now makes this underlying-group
diagonal closed. Its proof uses the two group-identity pullback squares,
closedness of an immersion from a scheme etale over a field into a locally
Noetherian scheme, and etale-surjective descent of closedness. The existing
closed-diagonal isomorphism transport brings the conclusion back to the
published actual class sheaf. The chosen closed equalizer is obtained from
the represented pullback of that diagonal along the pair of sections.
All transformations are natural on the full scheme slice, including
nonreduced and non-quasi-compact tests.

The theorem with explicit class equalizers and etale atlases expresses
that these two inputs suffice for the exact
`FieldPicardSheafAlgebraicSpaceStatement`: the immersed diagonal supplies
scheme representability of the diagonal, the given atlas supplies the
algebraic-space atlas and local finite type property, and the preceding
argument supplies closedness. It is a conditional reduction. It neither
proves the actual class-equalizer input nor constructs the atlas, and it
is not a proof or completion of the target task. No Picard representability,
projectivity, smoothness, reducedness, section, universal bundle or
condition on global functions is assumed. No new external source is used;
all content is derived from the imported geometric and categorical helpers.

`fieldPicardSheafAlgebraicSpace_of_stackInputs` specializes this reduction
using `FieldPicardAtlasAssembly`. It retains four explicit proposition
hypotheses: the actual class-equalizer immersion statement, the proper-field
smooth stack atlas, the smooth-automorphism quotient theorem, and fppf
descent of the etale class sheaf. The imported atlas assembly discharges
fpqc stack descent and smoothness of relative automorphisms through their
published proofs. This specialization still does not prove any of its
four remaining hypotheses and is not the unconditional target proof.
