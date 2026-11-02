# The first nonpositive interval contradicts the strict scalar cone

The theorem
`Langlands.Classification.orderedIntegralSegmentInductionSquareIntegrableCollapse`
proves exactly
`Langlands.Classification.OrderedIntegralSegmentInductionSquareIntegrableCollapse`.
Worker 320 supplied the main proof draft; Worker 19 checked and prepared this
pair. Its provenance is the internal composition of the published finite
interval, actual induction transport and scalar-cone results described below.
The complete outer parameters are `{p : ℕ} [Fact p.Prime]`, the supplied field
`F : PadicField.{uF} p`, and its supplied topology `T : F.TopologicalData`.
The independent universes `uF,uV` and actual carriers in
`Type (max uF uV)` are retained.

It defines the scalar coordinate of each supplied block as its degree times
the shifted midpoint of its integral endpoints. `blockTensorScalarRealPart`
supplies the actual tensor scalar action and norm formula in any permutation.
`squareIntegrableInductionEmbeddingCone` therefore gives the strict cone for
each actual permuted product into which the source embeds. In the identity
order the coordinate total is zero.

Apply `orderedRunFirstNonpositive` with degree weights and with the common
real shift added to both endpoints. The selected interval has nonpositive
shifted midpoint and contains every preceding interval. In the target's
notation `b` is the lower endpoint and `a` is the upper endpoint. The private support
lemma transfers a support witness between the two integral-coordinate
descriptions using only the endpoint inequalities. It requires no injectivity
or freeness of the twist line.

Support containment excludes linkage. `segmentOccurrenceToFront` uses the
supplied commutation to move this particular original occurrence first by an
actual product isomorphism. Composing the given injective intertwiner with
the isomorphism's equivariant linear equivalence retains an actual embedding.
If there were several blocks, the strict first-prefix inequality would make
the selected scalar coordinate positive. The nonpositive shifted midpoint
and positive degree contradict this. The degree sum at positive ambient rank
separately excludes an empty datum.

The theorem retains the target's explicit actual `TwoSegmentHeadCommutation`
premise and supplied scalar characters and endpoint norm equations. Its source
is an actual nontrivial analytically square-integrable representation with an
actual injective intertwiner into the supplied product. Irreducibility and finite
length are not additional hypotheses. Original positions remain separate
throughout, including repeated equal segments or equal supplied blocks.

The lower cone proof takes the actual nonzero image of normalized first
adjointness and applies the scalar Jacquet-subquotient cone. That cone follows
from admissible central-character detection and the analytic square-integrable
exponent criterion. The occurrence transport uses finite adjacent permutations,
the supplied two-factor commutation, and actual induction regrouping. The
finite interval selection uses only positive weighted sums and a finite minimum.
These routes use no segment classification or exhaustion theorem.

The recursive project import audit contains 456 modules, including this pair
and the four separately owned helper modules. Every imported module has paired
Markdown. The target pair and its 82-module project import closure are unchanged.
The audited Lean sources contain none of the prohibited segment classification,
multisegment exhaustion, ordered strong-head existence, quotient coverage,
tempered block uniqueness, square-integrable classification or exhaustion, and
regular exhaustion declaration families named in the task. The implemented
argument proves the stated conditional collapse; construction of its commutation,
scalar and initial induction inputs remains outside this result.
