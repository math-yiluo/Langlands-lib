# The isometric comparison between variable adjunction and relative series

Author: Worker 474.

`relativeSeriesComparison` proves the entire unchanged published proposition `Langlands.Analytic.PresentedAffinoidAlgebra.Adjoin.RelativeSeriesComparisonStatement`.

The proof constructs an actual reverse bounded algebra homomorphism. Its coefficient map is the existing contractive `baseMap` from the presented algebra A into the enlarged quotient B. Its variable tuple consists of the actual new quotient coordinates. Their coordinate norm bounds and the quotient-unit bound imply the weighted monomial bound, including the empty monomial when B is zero. The new `GeneralizedTateAlgebra.RelativeEvaluation` helper therefore evaluates every relative restricted series in B and proves that this reverse map is contractive.

The reverse-forward composition is the identity on B: precompose with the surjective scalar presentation map and use the scalar bounded-map uniqueness theorem on the two coordinate blocks. For old coordinates the equality is `baseMap_coordinate`; for new coordinates it follows from reverse evaluation of a variable. The forward-reverse composition is the identity on relative series: the two bounded maps agree on every coefficient constant and every new variable, so the convergent monomial expansion gives equality.

These identities give surjectivity. Combining the contractive forward and reverse norm bounds gives exact norm equality, hence isometry. Injectivity, the representative formula for the published forward map, and the presentation map's zero criterion identify the prequotient evaluation kernel with the existing closed ideal of old relations.

This is an internal derived proof for the project's actual quotient and evaluation maps. The source context and conventions remain those documented in the unchanged statement module: Berkovich's 2009 Trieste lectures, Definition 2.1.6(i), define relative weighted series; the comparison and its kernel are derived here. The implemented route uses reverse evaluation, rather than coefficient lifting, and assumes no norm attainment, nontrivial valuation, properness of the ideal, or nonzero quotient. It retains arbitrary positive real radii and empty variable blocks. It makes no claim about presentation independence, further equation quotients, analytic domains, structure sheaves, or etale sites.
