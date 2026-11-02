# Topology families on actual finite-type affine scheme points

Author: Worker 105.

This is derived infrastructure for Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Proposition 2.1 and its
proof, printed pages 2–3. Registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

`affineCoordinate_finiteType_iff` identifies finite type of the actual
global-section algebra with local finite type of the structure morphism
of an arbitrary affine scheme over `Spec R`. The canonical affine
isomorphism respects the specified base map, and Mathlib identifies the
local finite-type property of a spectrum map with finite type of its ring
map. The isomorphism cancels on the source. The converse spectrum statement
`ringTest_locallyOfFiniteType_iff` uses the actual given algebra structure.
Both useful directions are installed as instances. For these affine schemes
the structure map is automatically quasi-compact, recorded in
`affineStructure_quasiCompact`. Thus the family below has full finite-type
scope; local finite type is not being substituted for full finite type on
nonaffine schemes.

`spectrumAlgebraPointEquiv` is the direct equivalence between actual relative
spectrum morphisms and actual algebra maps. Its bundled homeomorphism
`spectrumAlgebraPointHomeomorph` compares the independently constructed
global-section evaluation topology with the original algebra evaluation
topology. The proof composes the canonical global-section homeomorphism
with the actual `ΓSpecIso` algebra comparison, and checks equality with the
direct point map using the proved spectrum comparison formula.

`AffineSchemeTopologyFamily` assigns arbitrary topologies to the actual
relative morphism sets for every finite-type affine scheme over `Spec R`.
It imposes no functoriality, invariance under presentations or source axioms.
`evaluationAffineSchemeTopologyFamily` is the existing evaluation assignment.
`algebraTopologyFamilyToSchemes` transports any algebra-point topology family
along the actual global-section point equivalence.
`schemeTopologyFamilyToAlgebras` restricts any scheme-point topology family
to spectra and transports it along the direct point equivalence. The
finite-type conditions required in both constructions are proved above.
These two constructions are not claimed to be inverse for arbitrary
assignments: such an assertion needs the appropriate functoriality axioms.

The coefficient and value rings are arbitrary commutative rings in the
same universe as the schemes. Only the homeomorphism and evaluation family
need a topology on the value ring. No continuity of ring operations,
Hausdorffness, locality or finite presentation is assumed here.
The actual four scheme axioms, their correspondence with the algebra axioms,
and the characterization theorem remain separate obligations.
