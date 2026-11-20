# Gluing open charts for torus-centralizer families

An actual chart is a locally finite-type scheme with a smooth closed geometrically connected subgroup whose residue fibres are torus centralizers. The chart conditions give injective evaluation and an open locus of lifts after every change of parameter. The coverage condition asks for a lift on an open neighbourhood of each point of each actual test family.

`TorusCentralizerChartGluingStatement` gives a locally finite-type parameter and a universal closed subgroup from these hypotheses. Yoneda takes each chart family to a map into the absolute Zariski sheaf. The open lifting criterion gives a relatively representable open immersion by its pointwise pullback property. The local lifts give local surjectivity of the sum of the chart maps. Gluing the charts represents the absolute sheaf, and passage to the fibre over the parameter's structural morphism gives the relative universal property. The universal closed subgroup comes from the identity section, and literal range equality expresses its property on every test.

This is the chart gluing step in the method of SGA 3, Exposé XV, §5.2–5.5. The construction uses the existing scheme gluing API and the Zariski sheaf of the actual subgroup families. The chart construction and its detection criteria are input to this theorem.
