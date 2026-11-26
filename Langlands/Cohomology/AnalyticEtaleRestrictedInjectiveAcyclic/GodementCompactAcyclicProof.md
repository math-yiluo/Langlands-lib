# Compact acyclicity of restricted analytic equivariant Godement terms

Module `Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic.GodementCompactAcyclicProof`,
namespace `Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic`.

The theorem `analyticEtaleGodementCompactAcyclic` proves
`AnalyticEtaleGodementCompactAcyclicStatement L X h R G ρ` (module
`Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic.GodementReduction`).

The parameters are those of the statement: a complete ultrametric normed field `K`, a
normed extension field `L`, an analytic space `X`, point axioms `h` for all its
`L`-valued points, a commutative ring `R` in universe `max u (v + 1) uL`, and a group `G`
acting through `ρ`, with `[IsTopologicalGroup G]`, `[Small.{max u (v + 1) uL} G]` and
admissible refinements of the distinguished lift system. The universes `u`, `v`, `uL`
and `z` are independent. Assume that `|X|` is Hausdorff, that `pointProjection L X` is
surjective and that the action is continuous. Then for every étale `G`-sheaf `F` of
`R`-modules and every `q`, the étale compact cohomology `etaleCompactCohomology L h R (q + 1)`
vanishes on the restriction (`etaleGSheafRestriction`) of the degree-zero equivariant
Godement term `(etaleGodementZeroFunctor L ρ h R).obj F`. No injectivity of `F` is
assumed.

## The ordinary premise

`ordinaryCompactAcyclic_coefficientRestrictedSmoothPointProduct` is the ordinary premise
of the published reduction `analyticEtaleGodementCompactAcyclic_of_correctedLocal_and_ordinary`
(module `Langlands.Cohomology.AnalyticEtaleSmoothPointProductLocalAcyclicCorrected`), in
exactly its displayed form. Under Hausdorffness of `|X|`, surjectivity of
`pointProjection L X` and continuity of the action, for every discrete coefficient
diagram `N` on `ULift` of the `L`-valued points and every `q`, it states that
`underlyingTopologyCompactCohomology X R (q + 1)` vanishes on `etaleUnderlyingSheaf` of
`(etaleCoefficientRestrictedSmoothPointProductFunctor L ρ h R).obj N`. The injectivity of
`N` and the surjectivity of the point projection are hypotheses of that form but are not
used.

The proof applies
`isZero_ordinaryCompactCohomology_coefficientSmoothPointProduct_of_cSoftAcyclicity`
(module `Langlands.Sheaf.Equivariant.AnalyticSmoothPointProductCoefficients`) to the
c-soft acyclicity theorem `Langlands.Cohomology.cSoftAcyclicity`
(module `Langlands.Cohomology.CompactSoft.AcyclicityProof`), instantiated at universe
`max u (v + 1) uL`. That reduction identifies the discrete-coefficient product with
`etaleRestrictedSmoothPointProduct` by a definitional isomorphism. It uses the c-softness
of the ordinary restriction after the canonical universe lift of `|X|`
(`isCSoft_universeLift_etaleRestrictedSmoothPointProduct`, from the compact extension
property of the smooth point product under a continuous action), the local compactness of
a Hausdorff `|X|` (`locallyCompactSpace_localized`), and the natural isomorphism
`underlyingTopologyLiftCompactCohomologyIso` between the point-support derived compact
sections on `|X|` and the native derived compact sections on the lifted space.
Grothendieck's acyclicity of c-soft sheaves for compact supports (Tohoku §3.3;
Kashiwara–Schapira, *Sheaves on Manifolds*, Proposition 2.5.8 and Corollary 2.5.9) then
gives the vanishing.

## The local premise and the main theorem

`analyticEtaleGodementCompactAcyclic_of_correctedLocal` derives the Godement statement
from `AnalyticEtaleSmoothPointProductLocalAcyclicCorrectedStatement` alone, by supplying
the ordinary premise above to `analyticEtaleGodementCompactAcyclic_of_correctedLocal_and_ordinary`.
That theorem passes, through `analyticEtaleGodementCompactAcyclic_of_injectiveCoefficients`,
to injective coefficient diagrams. It then compares étale compact cohomology with
ordinary compact cohomology of the ordinary restriction
(`isZero_etaleCompactCohomology_of_ordinary_directImage_acyclic`); that comparison needs
the vanishing of the positive ordinary higher direct images, which is the local premise.

`analyticEtaleGodementCompactAcyclic` supplies the local premise in two steps:

1. `analyticEtaleGaloisCoinducedLocalAcyclic` (module
   `Langlands.Cohomology.AnalyticEtaleGaloisCoinducedLocalAcyclicProof`) proves
   `AnalyticEtaleGaloisCoinducedLocalAcyclicStatement L X R G ρ`: étale `G`-sheaves with
   coinduced fixed sections over finite Galois data have vanishing positive ordinary
   higher direct images.
2. `analyticEtaleSmoothPointProductLocalAcyclicCorrected_of_galoisCoinduced` (module
   `Langlands.Cohomology.AnalyticEtaleSmoothPointProductGaloisReduction`) shows that the
   restricted smooth point products have coinduced fixed sections, and so turns step 1
   into `AnalyticEtaleSmoothPointProductLocalAcyclicCorrectedStatement L X h R G ρ`.

The proof uses neither `AnalyticEtaleCompactComparisonStatement` nor
`AnalyticEtaleGlobalComparisonStatement`, nor the restricted-injective acyclicity
statements, nor preservation of injectives by restriction. Its only axioms are
`propext`, `Classical.choice` and `Quot.sound`.

## Source

The argument follows Vladimir G. Berkovich, *Étale equivariant sheaves on p-adic
analytic spaces* (manuscript, 1995–1996; the `Equish_1996` manuscript, registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`),
Proposition 1.5.1, printed pp. 10–11. There each term of the equivariant Godement
resolution is shown to be a soft étale sheaf by verifying (1′) the vanishing of the
positive Galois cohomology of its stalks, because over finite Galois neighbourhoods its
sections are products of coinduced Galois modules, and (2′) the softness of its
restriction to the ordinary topology. The Lean proof uses these two facts in ordinary
form: vanishing positive ordinary higher direct images in place of (1′) (the two agree by
Berkovich, *Étale cohomology for non-Archimedean analytic spaces*, 1993, Proposition
4.2.4) and c-softness of the ordinary restriction in place of (2′). It derives the
compact-support vanishing from them through the comparison of étale and ordinary compact
cohomology, without passing through soft étale sheaves.
