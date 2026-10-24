# Geometric Picard-zero preservation by relative rigidified pullback

`Langlands.AbelianScheme.picardZeroPullback` proves exactly the published
proposition `Langlands.AbelianScheme.PicardZeroPullbackStatement.{u}`.
It applies to every base scheme `S`, abelian scheme `A/S`, morphism
`h : T ⟶ U` in `Over S`, and actual rigidified family `L` over `U`.
The conclusion is the geometric-fibre translation-invariance condition
for the existing `RigidifiedLineBundle.relativePullback` of `L`.
The theorem retains the arbitrary universe and all quantifiers of the
statement.

The proof fixes an algebraically closed field `K` in that universe and
a geometric point `s : Spec K ⟶ T.left`. The source hypothesis gives
translation invariance on the fibre of the family over `U` at
`s ≫ h.left`.

The published construction `GroupScheme.fibreComparison A.toGrp h s`
provides a homomorphism from the actual iterated base change over `s`
to the actual iterated base change over `s ≫ h.left`.
Its `fibreComparison_fst` identity says that the two projections to `A`
agree. The group objects underlying abelian-scheme base change are
definitionally the group-scheme base changes used by this construction.

The proof then applies
`isTranslationInvariant_fibre_relativePullback` from
`PicardZeroPullbackComparison`. This lemma pulls translation invariance
back along the group homomorphism and transfers it across the actual
line-bundle comparison to the fibre of the relative rigidified pullback.
The comparison uses the projection identity, the canonical inverse
symmetries of the relative spaces, and composition of line-bundle
pullbacks. Thus the resulting condition concerns the exact family in the
target statement.

This is a derived compatibility proof using the published statement and
the two published comparison modules. It does not require an inverse
to the fibre homomorphism or an additional hypothesis on `h` or `S`.
It makes no claim of representability or identification with an
identity component of a Picard scheme.
