# Generic-to-special ampleness on an abelian scheme over a DVR: proof

Author: Worker 171.

Module `Langlands.AlgebraicGeometry.Picard.DvrAbelianAmpleSpecializationProof`.

## Theorem

```lean
theorem Langlands.AlgebraicGeometry.Picard.dvrAbelianAmpleSpecialization :
    DvrAbelianAmpleSpecializationStatement.{u}
```

The type is exactly the published proposition, in arbitrary universe `u`: for every
discrete valuation domain `R : Type u`, every `A : Langlands.AbelianScheme (Spec
(CommRingCat.of R))` and every `L : LineBundle A.X.left`, ampleness of the pullback of
`L` along `A.X.hom.fiberι ⟨⊥, _⟩` implies ampleness of its pullback along
`A.X.hom.fiberι (IsLocalRing.closedPoint R)`. No hypothesis is added: no normality,
polarization, symmetry, dual scheme, positivity, relative-dimension, residue
characteristic, algebraic closedness or completeness assumption. The statement pair
and its imports are unchanged. A development check reported only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Proof as implemented

The proof avoids Riemann–Roch, cohomology and base change, and dual abelian
schemes. It has two steps.

1. `DvrAbelianGeometry.exists_affine_section_meeting_closedFibre` (module
   `DvrAbelianAffineSection`) produces `m ≥ 1`, a global section `τ` of `L ^ m` whose
   generation open is affine, and a point `x` of that open over the closed point.
2. `isAmple_closedFibre_of_section` (this module) pulls `τ` back along the closed
   fibre inclusion `ι = A.X.hom.fiberι (closedPoint R)`. The closed fibre is the total
   space of the abelian scheme `AbelianScheme.baseChange` along
   `fromSpecResidueField`, over the residue field. By
   `LineBundle.sectionOpen_pullbackPowSection` the pulled-back generation open is
   `ι⁻¹(L.sectionOpen τ)`; it is affine because `ι` is an affine morphism (base change
   of a morphism of affine schemes) and nonempty because `x` lies in the image of
   `ι` (`Scheme.Hom.fiberHomeo`). The field criterion
   `AffineSectionAmple.isAmple_of_isAffineOpen_sectionOpen` then gives ampleness of
   the closed fibre bundle.

The helper modules, each with its own Markdown, are
`Langlands.AbelianScheme.AffineSectionAmple`,
`Langlands.CommutativeAlgebra.FactorialLocalHartogs`,
`Langlands.CommutativeAlgebra.SmoothDVRUniformizerDivision`,
`Langlands.AlgebraicGeometry.FactorialAffineComplement`,
`Langlands.AlgebraicGeometry.Picard.DvrAbelianGeometry`,
`Langlands.AlgebraicGeometry.Picard.DvrUniformizerDivision`,
`Langlands.AlgebraicGeometry.Picard.DvrLineBundleDivision` and
`Langlands.AlgebraicGeometry.Picard.DvrAbelianAffineSection`.

## Published inputs

The proof imports published proofs only: the theorem of the square
(`GroupScheme.fieldTheoremOfTheSquare`), field base-change reflection of ampleness
(`fieldBaseChangeAmpleReflection`), spreading of fibre ampleness
(`properFibreAmpleSpreading`), principal-open section extension and generation-open
lifting (`PrincipalSectionExtension.exists_global`, `principalGenerationOpenLift`),
generation-open calculus for tensor and pulled-back sections, smooth geometric
integrality (`smoothGeometricIntegrality`), reducedness of smooth algebras over
fields, and factoriality of stalks of smooth schemes over a DVR
(`smoothDVR_factorialStalks`). It uses none of
`AbelianFibreAmpleLocusClosedStatement`, `NormalFiniteTypeAbelianAmpleExistenceStatement`,
`NoetherianAffineAbelianGenericAmpleStatement`,
`NormalFiniteTypeAbelianPicardSheafAFSchemeStatement`,
`FiniteTypeAbelianPicardSheafSchemeStatement`,
`FiniteTypeSmoothFamilyAbelianRepresentabilityStatement` or
`SmoothFamilyAbelianRepresentabilityStatement`; an audit of the transitive import
closure found none of these names. No relative or field dual
scheme, Picard algebraic space or Picard stack atlas construction is used.

## Comparison with the source

The statement's Markdown cites Faltings–Chai, *Degeneration of Abelian Varieties*,
Chapter I, Remark 1.10(b) (registered source
`provided-0ecad2ee7ec463aef945e9d85a6d369dd775bbbbbd4e55843b9bfb4aa819da7d`), whose
argument (proof of Theorem 1.9(b), printed p.6) uses Riemann–Roch and
semicontinuity. The implemented route is different: it is Raynaud's
translation-and-affine-open method (Guo, arXiv 2209.02443v1, Corollary 3.6 and
Lemma 5.3) combined with Weil's translation argument (Mumford, *Abelian Varieties*,
Chapter II, §6, proof of Application 1). The source locations are recorded in the
helper modules' Markdown.
