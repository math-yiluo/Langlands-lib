# Conditional assembly of normalized-exponent standard reduction

This internal adapter combines actual simultaneous standard conjugation with
conjugation invariance of the complete normalized-exponent cone condition. It
proves a conditional implication to the exact published
`NormalizedTemperedStandardReductionStatement`; it does not supply its
unconditional proof.

`SatisfiesStandardNormalizedExponentTests` names exactly the admissibility
and standard-test condition on the right of that statement. The ambient
`G` is a connected reductive group scheme; its witness `hG` supplies
smoothness and hence the local finite type needed by the cones. The
canonical rational-point topology, Hausdorff nonarchimedean local field and
explicit locally compact nonarchimedean rational-point group are retained.

`normalizedTempered_iff_standard_of_dynamicRealizations` fixes the actual
maximal split torus map `i` and generic cocharacter `ν` for the entire
standard-testing equivalence. Three structural inputs remain explicit:

- `SmoothMaximalSplitTorusConjugacyStatement`;
- `HasRelativeRootSystem i` for this actual maximal split torus;
- for every specified parabolic map `p` and rational Levi map `l`, one
  cocharacter `z` with `range p = Dynamic.parabolic z` and
  `range (l ≫ p) = Dynamic.centralizer z` on every test scheme.

The forward implication uses the direct restriction of normalized-exponent
temperedness. In the converse, choose the supplied simultaneous dynamic
realization for the given maps. The geometric adapter conjugates it into
the fixed family's dominant chamber and returns one rational point `g`, an
index `J` and a standard cocharacter `ζ` with all four required equalities.
The standard hypothesis applies to `p` postcomposed with `Int(g)`, with the
same source objects `P`, `M`, `A` and the same maps `l` and `a`. The cone
condition conjugation equivalence transports the result back.

That equivalence includes nonempty presentation coverage and the tests over
every compatible presentation, represented geometric unipotent radical,
multiplication isomorphism and normalized Jacquet exponent. Thus the
assembly adds no presentation-choice or exponent-transport premise and
does not treat an empty presentation type as a successful test.

`normalizedTemperedStandardReduction_of_structural_inputs` packages this
argument for all fields and groups. It retains the global relative-root
system statement and the simultaneous-realization input, together with
smooth maximal split torus conjugacy. The minimality assumption in the
published target is available but is not needed by this conditional route.
All characteristic and nonsplit cases and the independent representation
carrier universe remain unchanged.

The provenance is internal: the implemented proof composes the published
standard-reduction statement and actual-map interfaces with the two
conjugation adapters. It introduces no new source translation. The
structural premises, the separate normalized/raw logarithmic source
comparison and the later temperedness consequences remain open obligations.
