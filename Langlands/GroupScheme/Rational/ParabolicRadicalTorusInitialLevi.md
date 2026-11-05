# One radical torus whose ambient centralizer is the dynamic Levi

This internal derived unit constructs an initial torus and then combines it with
the rational conjugacy transport. It retains the unchanged universe-general
`ParabolicRadicalTorusCentralizerLeviStatement`. The final theorem in this module
is conditional on exactly three existing structural propositions:
`ParabolicDynamicStatement`, `DynamicCentralizerReductiveStatement`, and
`SolvableMaximalTorusConjugacyStatement`. It does not prove those inputs or assert
the unconditional target.

The local theorem
`IsRationalLeviSubgroup.exists_maximalTorus_radical_centralizer` starts with an
actual rational Levi `l : L → P`, a closed ambient inclusion `j : P → G`, a
specified ground-field solvable radical `r : R → P`, and a cocharacter whose
dynamic centralizer is represented by `l ≫ j`. It constructs a maximal torus
`s : S → R` whose whole ambient centralizer is represented by this same Levi.

First the cocharacter factors centrally into its centralizer `L`. Its closed
split-torus image is central in `L`, and the published central-torus radical
factor embeds this torus into the specified `R`. The published finite-type
maximal-torus extension supplies a maximal torus `S` in `R` containing that image.
The original cocharacter therefore factors through `S`. Commutativity factors
`S` into its cocharacter centralizer `L`; cancellation through the closed map
`j` identifies its factors in `L` and `R` over `P`. The radical-image centrality
lemma makes its factor in `L` central.

The equality of subgroup functors follows in both directions on every relative
test scheme. Centrality in `L` makes the Levi image centralize `S`. Conversely,
anything centralizing `S` centralizes the cocharacter that factors through `S`,
and therefore lies in the represented `L`.

`ParabolicRadicalTorusInitialLeviFromDynamicStatement` states the conditional
initial-torus assertion. Its proof chooses a cocharacter for the supplied
parabolic using `ParabolicDynamicStatement`, takes the represented affine
dynamic centralizer, and obtains connected reductivity from
`DynamicCentralizerReductiveStatement`. Published dynamic structure gives an
actual geometric unipotent radical and the Levi-first scheme multiplication
isomorphism. The preceding construction then supplies the initial maximal torus
of the specified radical.

`ParabolicRadicalTorusCentralizerLeviFromDynamicStatement` states the resulting
three-premise reduction. Its proof applies the initial-torus theorem and Worker
1463's proved rational conjugacy reduction, retaining the actual ambient
centralizer and multiplication isomorphism.

The provenance is this formal composition of published definitions and proved
image, maximal-extension, dynamic decomposition, and centrality helpers, together
with the independently submitted conjugacy transport. No rational-point density,
perfectness, split-field, or ambient maximal-torus premise is used.
