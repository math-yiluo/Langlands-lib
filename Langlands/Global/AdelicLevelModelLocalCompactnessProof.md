# Local compactness of actual arithmetic-level model points

`Langlands.Global.adelicLevelModelLocalCompactness` proves the unchanged
`AdelicLevelModelLocalCompactnessStatement` in arbitrary common universe
`u`. It establishes local compactness of the actual arithmetic-level
points of every finite-type model over its outside-`S` integer ring.
Separated models also have Hausdorff point spaces. The proof retains the
original scalar actions, actual relative scheme morphisms and the
specified `curvePlaceLevelModelPointTopology` and
`numberFieldLevelModelPointTopology`. Local compactness requires no
separatedness or affineness assumption.

The arithmetic conclusion is Conrad's Corollary 3.7. The implemented proof
uses the product of actual local-model point spaces, as in the source,
and imports the independent local scheme-point theorems. The source
proves compactness of integer-valued points using a finite affine open
cover. That argument is supplied here by `schemePointCompactness_proof`.
The present file assembles these local results and transports them along
the already proved actual coordinate homeomorphisms.

For a scalar ring `C`, a local coefficient ring `R` and a model `X` over
`Spec C`, the private local helpers use the actual base change
`ringBaseChange C R X`. Its structure morphism is the second pullback
projection. Local finite type, quasi-compactness and separatedness are
preserved by this base change. These instances give:

- Local compactness of its `R`-points from
  `schemePointLocalCompactness_proof`, when `R` is a locally compact
  Hausdorff topological local ring with open units and `X` is locally of
  finite type.
- Compactness of its `R`-points from `schemePointCompactness_proof`, when
  `R` is compact Hausdorff and `X` is of finite type. Quasi-compactness of
  the base change over the compact affine scheme `Spec R` provides the
  compactness of its underlying scheme required by that theorem.
- Hausdorffness from `t2Space_schemePointTopology` when `X` is separated
  and `R` is a Hausdorff topological local ring with open units.

The curve proof, `curvePlaceLevelModelPoint_locallyCompactSpace`, keeps
finite constants `k`, the original `k`-algebra action on `F`, a compatible
scalar tower through `RatFunc k`, and `FunctionField k F`. No separability
assumption is added. Each local field completion is locally compact, and
each completed integer ring is compact Hausdorff, by the imported
function-field completion proofs. The local factors have open units by
`adelicLocalFactorUnits`. Applying the local helpers makes every local
point space locally compact and every integer-valued point space compact.

`Homeomorph.sumPiEquivProdPi` splits the product into the finitely many
field-valued point spaces indexed by places in `S` and the integer-valued
point spaces indexed by places outside `S`. The first product is locally
compact by finiteness of its index. The second product is locally compact
because each of its factors is both compact and locally compact.
Local compactness of these factors is proved separately: compactness alone
does not supply Mathlib's local-compactness property for a non-Hausdorff
space. The finite-type actual coordinate homeomorphism
`curvePlaceLevelModelPointMap_isHomeomorph_of_finiteType` transfers the
product conclusion to the stated level-model topology. If `X` is
separated, the local Hausdorff helper makes every factor Hausdorff, and
the same homeomorphism transfers this property.

The number-field proof,
`numberFieldLevelModelPoint_locallyCompactSpace`, includes every infinite
completion. Those completions are locally compact by the existing
completion instances. For each finite place, the compact open completed
integer ring is a neighborhood of zero in the additive group of the
completion; this proves local compactness of the finite completion.
The completed integer ring is itself compact Hausdorff and locally
compact. Open units again come from `adelicLocalFactorUnits`. Applying the
local helpers and splitting the product twice separates the finite
product over all infinite places, the finite product over finite places
in `S`, and the compact locally compact product of integer-valued points
outside `S`. The actual map
`numberFieldLevelModelPointMap_isHomeomorph_of_finiteType` transfers local
compactness and, under separatedness, Hausdorffness to the specified
number-field level topology.

Both arguments permit empty `S`. This is the derived extension recorded
in the target's Markdown: the actual integer bases remain Noetherian,
so the imported finite-type coordinate homeomorphisms still apply. At the
empty curve level all factors are integer-valued; the number-field level
still includes every infinite factor. The final theorem combines the two
arithmetic clauses. It proves no assertion about infinite constant fields
or the separate topology on full adelic points.

Source: Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`,
printed page 9, Corollary 3.7 and its proof. The local inputs correspond to
Proposition 3.1 and the coordinate comparison to Theorem 3.6.

Authorship: Worker 208 wrote the proof and its mathematical explanation.
Worker 59 checked the draft against the published inputs and prepared this
focused proof contribution.
