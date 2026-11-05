# Full-adele preimages of actual arithmetic-level model points: proof

The theorem `Langlands.Global.adelicFullLevelPreimage` proves exactly
`Langlands.Global.AdelicFullLevelPreimageStatement` in arbitrary common
universe `u`. Its two components prove the curve-place and number-field
clauses. The target is the algebraic full-level preimage step of Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed p.11, Proposition 4.4, second proof paragraph; registered
source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The quasi-compact separated target formulation is the derived extension
already documented in the unchanged statement.

For an original integer base `C`, the internal assembly lemma takes an
actual level algebra `A`, full adele algebra `B`, its level product
isomorphism `A ≃ₐ[C] ∏ Rᵢ`, an injective coefficient map
`B →ₐ[C] ∏ Lᵢ`, and compatible local maps `Rᵢ →ₐ[C] Lᵢ`.
Here each `Rᵢ` is local and each `Lᵢ` is reduced. For a quasi-compact
separated source scheme, choose the supplied local lifts of a point over
`B`. The published `productPointMap_surjective` assembles them over the
product of the `Rᵢ`, and `ringPointChangeRingEquiv` transports that point
to `A`. The two resulting points over `B` agree after extension to the
product of the `Lᵢ`: coordinate equality follows from the chosen lifts
and compatibility, and `productPointMap_injective` gives equality over
that product. Injectivity of the coefficient map makes `B` reduced;
`schemeSeparatedCoefficientInjectivity_proof` then gives equality over
`B`. A second internal lemma derives the desired range preimage equality
from the local range preimage equalities, using coefficient extension and
its commutation with postcomposition. The reverse inclusion is naturality.

Both arithmetic clauses instantiate every input of this assembly. They
use the existing `CurvePlaceLevelFactorIndex` and
`NumberFieldLevelFactorIndex`. The level factors `Rᵢ` are the existing
actual fields in `S`, valuation subrings outside `S`, and all infinite
completions in the number-field case. The full factors `Lᵢ` replace the
integral factors by their completed fraction fields and retain the other
fields. Their `C` actions are the original integer diagonals. The map
from `B` is literal coordinate evaluation; its injectivity follows from
restricted-product extensionality, separating places in `S` from those
outside `S`, and from product extensionality for the infinite number-field
factor. All scalar and level-map compatibilities are proved by reflexivity.

At the field factors the local coefficient map is the identity ring map;
its algebra isomorphism gives surjectivity on both relative point spaces,
which proves the local range equality. Outside `S`, the actual valuation
subring and its completion field have their existing valuation-domain and
fraction-field instances. The original integer scalar maps form a tower,
checked by reflexivity. The imported
`universallyClosed_ringPoint_preimage` supplies the local equality because
the model morphism is proper. Thus no local lifting property remains an
assumed arithmetic input. Properness and the target's quasi-compactness
and separatedness imply the source's same relative properties. The affine
base then gives compactness and quasi-separatedness of its underlying
scheme space, as required by the product-point comparison.

The result preserves arbitrary curve constants and field extensions,
all number fields and infinite completions, every finite `S` including
empty `S`, and nonaffine models. It uses no point-space topology, finite
constant field or finite-type-over-the-integer-base hypothesis. Compactness
above concerns the underlying scheme's Zariski space. This proof supplies
only the stated algebraic preimage equality. Proper-model spreading,
topological adelic properness, eventual stabilization and the remaining
whole-paper results are separate obligations.
