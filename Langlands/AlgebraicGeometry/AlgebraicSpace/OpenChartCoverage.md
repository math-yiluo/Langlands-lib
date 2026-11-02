# Coverage by open scheme charts

This internal helper module derives a gluing coverage criterion from the
imported Library and Mathlib constructions.

`isLocallySurjective_of_covering_section` transfers a covering image sieve
on the universal section of a locally surjective scheme chart to every
section of the target presheaf. It uses pullback stability and transitivity
of the fppf topology.

`covering_section_of_residueField` pulls back every open chart along the
given scheme section. A residue-field lift at each point supplies a point
in one of these represented pullbacks. Their open projections therefore
form a Zariski covering family, hence an fppf covering family. The pullback
identities place this covering sieve in the image sieve of the coproduct
of the charts.

`isLocallySurjective_sigma_of_residueField` combines these results with
local surjectivity of an etale surjective atlas. No sheaf condition on the
target is required. The conclusion is local surjectivity of the presheaf
coproduct map, as required by the Library's open-chart gluing theorem.
