# Classification of Picard-zero line bundles up to a base twist

The theorem
`Langlands.AbelianScheme.picardZeroLineBundleClassificationUpToBaseTwist.{u}`
has complete type
`Langlands.AbelianScheme.PicardZeroLineBundleClassificationStatement.{u}`.
It gives a separate proof entry for this published proposition.

For every proof `preservation` of `pullbackTensorComparisonIsIsoStatement`,
scheme `S`, abelian scheme `A/S`, witness `hA : HasDualScheme A`, parameter
scheme `T : Over S`, and line bundle `N` on `T ×_S A`, suppose that `N`,
transported along `(relativeSpaceSymmetry A.X.hom T).inv`, is geometrically
Picard-zero. The conclusion is a morphism `φ : T ⟶ dualScheme A hA` over `S`
and an isomorphism

`N ≅ P_φ ⊗ pr_T^*(e_T^*N)`.

Here `P_φ` is the underlying bundle of the actual rigidified relative
pullback of `poincareFamily A hA`, and `pr_T` and `e_T` are the published
relative projection and unit section. The tensor is
`LineBundle.tensor preservation`. All the quantifiers and product-order
transports are those of the imported proposition. The result asserts
existence of an underlying line-bundle isomorphism; it asserts neither
uniqueness nor compatibility with rigidifications. The base and parameter
schemes are arbitrary, including nonreduced schemes.

The implemented proof is the single term
`Langlands.AbelianScheme.picardZeroLineBundleClassification`, imported from
`Langlands.AlgebraicGeometry.Picard.PicardZeroLineBundleClassificationProof`.
That published theorem has exactly the same type. It applies
`picardZeroLineBundleClassification_of_inverse` to the proved
`LineBundle.exists_tensorObj_iso_structureSheaf`. Its construction
normalizes `N` with the dual of `e_T^*N`, classifies the resulting rigidified
Picard-zero family using the chosen universal family, and rearranges the
tensor factors to recover the displayed isomorphism. The present module
introduces no additional premise.

The mathematical provenance is Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, preliminary draft, Chapter VI, (6.2), printed
pp.88–89 (PDF pp.92–93), particularly the normalization in (6.2)(ii) and
the universal property of the Poincaré bundle. The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
This is the derived Picard-zero consequence described by the statement
and proof modules. Worker 516 read these original pages and found no
source-specific project errata note in the supplied Library.

Worker 266 authored the imported classification-from-inverse construction.
Worker 270 authored the imported dual-evaluation proof and classification
wrapper. Worker 516 prepared this thin proof entry and its explanation,
reusing those published results unchanged.
