# The fppf Picard sheaf of an abelian scheme over a finite-type `ℤ`-algebra: proof

Module: `Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafAlgebraicSpaceProof`.

Author: Worker 4828, for task `3931bd2c-94d1-4d23-acab-fbcd0c8074a7`.

The theorem
`Langlands.AlgebraicGeometry.Picard.finiteTypeAbelianPicardSheafAlgebraicSpace`
proves the published proposition
`Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafAlgebraicSpaceStatement.{u}`
for every universe `u`. Its type is exactly that proposition. This module leaves
the statement module and its Markdown unchanged.

## What is proved

Let `R : Type u` be any commutative ring of finite type over `ℤ`, and let `A` be
any abelian scheme over `Spec R`. No reducedness, domain, polarization,
projectivity or cohomological-flatness hypothesis is added. Then:

- the actual fppf Picard class sheaf `RelativePicard.classSheaf A.X.hom` on
  the full slice over `Spec R` is an algebraic space over `Spec R` in the
  Library's convention `AlgebraicSpace.IsAlgebraicSpace`; and
- there are a scheme `U` over `Spec R` and a transformation
  `a : (schemeYoneda _).obj U ⟶ RelativePicard.classSheafPresheaf A.X.hom`
  with `AlgebraicSpace.IsEtale a` and `AlgebraicSpace.IsSurjective a`, and with
  `U.hom` locally of finite presentation.

## The proof

The proof is a single application of a published conditional theorem to two
published proofs. Nothing is assumed.

`finiteTypeAbelianPicardSheafAlgebraicSpace_of_versalInputs hF hA`, from the
Library module `Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardAssembly`,
derives the target from two hypotheses:

- `hF : FiniteTypeFormalVersalBundleStatement.{u}`. Here it is supplied by
  the published theorem `finiteTypeFormalVersalBundle` from the module
  `Langlands.AlgebraicGeometry.Picard.FiniteTypeFormalVersalBundleProof`. That
  theorem gives a formally versal line bundle over a complete Noetherian local
  base at every finite-type field point of every proper flat scheme over a
  finite-type `ℤ`-algebra.
- `hA : CommutativeAlgebra.FiniteTypeIntEtaleCompletionApproximationStatement.{u}`.
  Here it is supplied by the published theorem
  `CommutativeAlgebra.finiteTypeIntEtaleCompletionApproximation` from the
  module `Langlands.CommutativeAlgebra.FiniteTypeIntEtaleCompletionApproximationProof`.
  That theorem gives finite-order approximation in etale neighbourhoods for
  maps into the completion of every maximal localization of a finite-type
  `ℤ`-algebra. Its proof uses Popescu factorization and the G-ring property
  of finite-type `ℤ`-algebras, both proved in the Library.

The conditional theorem itself is proved in that module from published
results:

1. `versalAlgebraization_of_etaleApproximation hA` gives
   `VersalAlgebraizationStatement.{u}`.
2. `picardOpennessOfVersality` gives `PicardOpennessOfVersalityStatement.{u}`.
3. `PicardGroupoid.finiteTypePicardStackAtlas_of_versalInputs` combines `hF`
   with steps 1 and 2 to give `FiniteTypePicardStackAtlasStatement.{u}`. This
   is a locally finite type smooth scheme atlas of the relative Picard
   groupoid of every proper flat scheme over a finite-type `ℤ`-algebra.
4. `finiteTypeAbelianPicardSheafAlgebraicSpace_of_stackAtlas` applies that
   atlas to the actual abelian scheme `A.X`, which is proper and smooth, hence
   flat. It then uses the published `smoothAutomorphismEtaleAtlas`,
   `lineBundleFpqcStack` and smooth relative automorphism schemes of abelian
   schemes to get an etale atlas of the etale class sheaf. The published
   `RelativePicard.classSheaf_algebraicSpace_of_etale_atlas` transports this
   to the fppf class sheaf. Noetherianity of `R` upgrades local finite type of
   the atlas to local finite presentation.

## Scope and provenance

This proof follows the corrected Artin route recorded in the target
statement's Markdown (Artin 1974, Appendix item 2). Versal deformations,
algebraization by Artin approximation, and openness of versality give a
smooth atlas of the Picard stack. Smooth automorphism groups then make the
etale sheaf of isomorphism classes an algebraic space, and this is compared
with the Library's fppf class sheaf. The module adds no external mathematical
assertion. Each step is a published Library theorem cited above by Lean name.
The final step proves no converse and uses no hypothesis beyond the target's
own.
