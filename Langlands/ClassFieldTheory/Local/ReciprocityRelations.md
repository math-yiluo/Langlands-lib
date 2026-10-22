# Relations and conditional character transport for local reciprocity

Author: Worker 21. The imported construction modules are independently
published. This pair adds relations and conditional transport on those objects.

For an actual `PadicField F`, supplied `TopologicalData T` and explicit
continuous residue-degree candidate `φ` on its actual absolute Galois
group, `WeilReciprocityCandidate T φ` is the type of continuous
isomorphisms from the existing pullback's topological abelianization
to `F.Carrierˣ`. This type has no supplied inhabitant.

Given such an isomorphism `e`, `candidateGaloisHom` composes its inverse
with the constructed comparison to the absolute-Galois abelianization.
The inverse lands in the Weil abelianization, never in the Weil group.
`GeometricOrderRelation` says that additive normalized order after `e`
equals descended integer degree. Thus degree `+1` has order `+1`.
This is the geometric-Frobenius sign convention; it does not prove that
an arbitrary supplied `φ` is the actual geometric residue map.

`LocalReciprocityCandidateRelation` additionally requires dense image
of the induced Galois homomorphism and all of the actual finite
norm-kernel, surjectivity and restriction relations from `FiniteArtin`.
These are conditions on a candidate, not a claim to have constructed one.
Local norm relations and order normalization alone are not asserted
to give a unique candidate.

`CompletionComparisonRelation e c` is the exact commuting square for
a specified continuous isomorphism from the open-finite-quotient
completion of `Fˣ` to the actual compact Galois abelianization.
Its composite with the constructed dense completion map must equal
`candidateGaloisHom e`. The completion remains a different carrier
from the generally noncompact group `Fˣ`.

`LocalReciprocityExistence` is an explicit `Prop` definition existentially
quantifying both candidates and these conditions. No theorem proves it,
and no use of choice extracts a canonical map from an unproved assertion.
Its intended theorem must use the actual geometric residue-degree map
when that map has been constructed and identified. The companion
statement task owns the theorem layer.

`weilCandidateCharacterEquiv e` is a conditional equivalence of continuous
complex quasicharacters. It first descends a character of the Weil
pullback to the actual abelianization, then precomposes with `e.symm`.
The reverse direction composes with `e` and the quotient projection.
Neither direction requires a section into the nonabelian Weil group.

## General finite extensions and directions

For any finite intermediate field `E` in the chosen algebraic closure of
a perfect field `K`, the two absolute relations use the actual subgroup
fixing `E` in that closure. `AbsoluteNormRelation` equates the base
candidate after the field norm with subgroup inclusion after the
extension candidate. `AbsoluteTransferRelation` equates the extension
candidate after field inclusion with actual finite-index transfer after
the base candidate.

The two Weil relations use the preimage of that fixing subgroup in the
existing Weil pullback. `WeilNormRelation` compares the base
Weil-to-units map after subgroup inclusion with the norm after the
extension map. `WeilTransferRelation` compares the extension map after
group transfer with field inclusion after the base map.
`RelativeWeilReciprocityRelation` is their conjunction.
These maps and finite-index certificates have been constructed in
`Transfer`; no unspecified transfer or norm map occurs in these relations.
The extension need not be Galois over `K`.

The candidate equalities are algebraic homomorphism equalities, accepting
the underlying homomorphisms of continuous candidates. The actual
constructed inclusion and transfer maps are continuous. Identification
with a separately presented absolute or Weil group over `E` remains
explicitly separate, as do independence of closure choices and proof of
the squares.

## Sources and unfinished system layer

Henniart (2000), section 1.1, printed page 439 / PDF page 1, states that
geometric Frobenius corresponds to a uniformizer. Registered source
`henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
Deligne (1973), section 2.3, printed pages 523–524 / PDF pages 23–24,
gives this normalization and both functoriality diagrams. Registered
source `deligne-1973-local-constants`, SHA256
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.
Worker 21 read these original pages and visually checked Deligne's
diagrams. Deligne's arithmetic-degree convention explains its minus
sign; the project's geometric-degree convention gives the plus sign
in `GeometricOrderRelation`.

Serre, *Local Fields* (1979), Chapter XI sections 3–5, printed pages
169–175 / PDF pages 175–181, supplies the finite norm-residue and
completion framework. Registered source `serre-1979-local-fields`,
SHA256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
All cited passages were read. These new predicates are derived
interfaces on the constructed objects; they do not assume the
class-formation axioms or reciprocity assertions in the sources.

The all-fields coherent normalized reciprocity system, its uniqueness
property, and specialization to the actual assembled local Weil groups
are not defined in this file. Finite-level geometric normalization
through the actual residue action is the separate module
`Langlands.ClassFieldTheory.Local.ResidueNormalization`, which this file
does not import. In particular, no uniqueness theorem is postulated for
the weaker single-field local conditions in this file. The canonical
reciprocity constructor remains downstream of independently proved
existence and uniqueness.

The five imported construction pairs, `Units`, `Completion`, `FiniteArtin`,
`WeilAbelianization` and `Transfer`, were published under
`Langlands/LocalClassField` in Library
`30ceb5a0d89d8094c1663fc19f35416519b9a125`. The module-path consolidation
(pilot task `295b0f1c-439f-4b3e-8c86-14e5bd541262`) moved them to the same
basenames under `Langlands/ClassFieldTheory/Local`, and this module now
imports them from there; the old paths remain as declaration-free re-exports.
This new module uses the canonical `ClassFieldTheory/Local` directory;
the existing imported declarations keep their published names.
The prepared environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

Development check `43d82dee-4bc4-4dd2-9e8e-4308d42c4939`, over that
Library and with the original `Langlands.LocalClassField` imports, compiled
this module without errors or warnings. Inspection
confirmed that `LocalReciprocityExistence` is a `Prop`-valued definition
in the arbitrary field universe `u`, using only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. This checks elaboration
of the definition, not truth of its proposition. Independent semantic review
accepted this construction contribution separately from the development check.
