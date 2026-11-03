# A conditional fixed-torus parabolic classification reduction

Worker 1358, with Worker 146 identifying the algebraic-closure base-change
theorem used below. This is an internal composition of the published Borel,
standard parabolic, smooth point comparison, and split-torus descent interfaces. It
retains five structural statements as explicit premises; it does not prove the
unconditional fixed-torus classification.

Over an algebraically closed field, let `G` be connected reductive, let
`j : T.toGrp ⟶ G` be a specified split maximal torus, and let `i : P ⟶ G`
be a smooth closed subgroup through which `j` factors by the actual map `f`.
Suppose some Borel of `G` factors through `P`. The theorem
`exists_fixedTorusDynamicPresentation_of_borel` constructs an actual integral
cocharacter `ζ` of this same `T` and proves
`SubgroupFunctor.range i = Dynamic.parabolic (groupHom ζ ≫ j)` on every
test scheme. Its four explicit structural inputs are
`BorelConjugacyStatement`, `RegularCocharacterBorelStatement`,
`StandardParabolicPointsStatement`, and `StandardCocharacterStatement`.
No connectedness or reductivity of `P` is required.

The theorem `splitParabolicCocharacterStatement_of_structuralStatements`
additionally takes `MaximalTorusBaseChangeStatement`. From these five
premises it proves the exact published proposition `SplitParabolicCocharacterStatement`, including arbitrary
fields and universe `u`, connected reductive groups, the original split maximal
torus and its specified map, an actual integral cocharacter of that torus, and
equality of subgroup functors on every test scheme.

The constructor `splitParabolicCocharacterPresentation` selects these data
for a given `k`, `G`, `T`, `j`, `P`, `i`, and `f`, under the same five structural
premises and the target's hypotheses. Its output is the actual subtype
`FixedTorusDynamicPresentations T j i`: a cocharacter of `T` together with
its all-test presentation equality.

## Implemented argument

For the algebraically closed construction, closedness of `P ⟶ G` and
affineness of `G` give affineness of `P`. The identity-component construction
transfers the assumed Borel conjugacy theorem to `P` without assuming `P`
connected. The containing-Borel and promotion constructions then choose an
ambient Borel inside `P` containing the exact original torus map `f`.

The regular-cocharacter Borel statement supplies a regular integral `ν` of
`T` whose dynamic subgroup is that Borel. Regularity equals genericity here
because the relative-root set is definitionally the root set. The actual Borel
embedding through `P` gives containment of subgroup functors on every test.
`standardDynamicOvergroupData_of_statements` applies the two explicit standard
parabolic inputs and the proved smooth point comparison to obtain `ζ` and the
all-test equality.

For an arbitrary field `k`, pass to the chosen `AlgebraicClosure k`.
The proved `IsConnectedReductive.baseChange_toAlgebraicClosure` supplies
connected reductivity of the base-changed ambient group. It uses geometric
connectedness and transport of the trivial unipotent radical along the
bijective map from the algebraic closure to its own algebraic closure. Thus
no general connected-reductive field-extension statement is assumed. The
additional structural premise supplies maximality of the base-changed
specified torus; splitness, smoothness, and closedness use their proved
base-change properties.
The Borel witness already stored in `IsParabolicSubgroup i` gives an ambient
Borel inside `P` over this closure. Thus no preservation theorem for
parabolicity or for Borel maximality under field extension is needed in this
argument. Apply the algebraically closed construction to this original witness.

Finally, `exists_range_eq_parabolic_iff_baseChange` descends the resulting
presentation to `k`. That proved descent theorem uses the equivalence on
integral cocharacters of the original split torus and faithfully flat descent
of represented subgroup functors. The result is an equality over `k` on all
test schemes, including nonaffine and nonreduced schemes.

All five structural statements remain assumptions of the final theorem.
Neither acceptance of this reduction nor the fact that its conclusion names
the target proposition discharges those assumptions or completes its proof
task. There is no appeal to `ParabolicDynamicStatement`. The construction
requires neither a nonempty root set nor positive torus rank, and retains the
full-group case whenever its displayed premises hold.
