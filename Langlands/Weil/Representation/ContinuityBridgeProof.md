# Proof of compatibility of the continuity presentations

The theorem
`Langlands.Weil.representationContinuityCompatibility.{uG,uV}` proves exactly
`Langlands.Weil.RepresentationContinuityCompatibility.{uG,uV}` from
`ContinuityBridgeStatement`. It supplies callable comparisons between the
bundled `FiniteRepresentation` predicates and the expressions in the unchanged
`Langlands.Weil.RepresentationContinuity` statement.

This is a proof of compatibility of presentations. It proves neither
`RepresentationContinuity` nor `BundledRepresentationContinuity`. The five
substantive continuity equivalences remain the content of those proposition
definitions.

## Topology comparison and the constructed norm

`carrier_topology_eq_moduleTopology` installs Mathlib's
`isModuleTopologyOfFiniteDimensional` for a Hausdorff finite-dimensional complex
topological vector space and applies `eq_moduleTopology`. The hypotheses are
an additive commutative group and complex module, finite dimensionality,
continuity of the additive group operations and scalar multiplication, and
Hausdorffness. The scalar field carries its usual complex topology.

`compatible_carrier_topologies_eq` applies this result separately to two
topologies on the same additive group and module. Since each equals
`moduleTopology ℂ V`, they equal one another. This proves independence of the
topology from any compatible norm or finite coordinate choice; it does not
claim that the norms themselves are equal.

For a bundled carrier `A`, the definition pair constructs
`carrierNormedAddCommGroup A` by pulling the norm on
`Fin (Module.finrank ℂ A) → ℂ` back through
`(Module.finBasis ℂ A).equivFun`. The construction retains the original additive
group and module on `A`; `carrierNormedSpace A` establishes compatibility with
complex scalar multiplication. The theorem `carrierNormed_topology_eq` installs
these two local structures and applies the preceding topology theorem. No
pre-existing norm or topological equivalence on `A` is assumed.

`endomorphismHomeomorph V` uses the actual linear equivalence
`LinearMap.toContinuousLinearMap` between `Module.End ℂ V` and `V →L[ℂ] V`.
The source carries `moduleTopology ℂ (Module.End ℂ V)` and the target its usual
operator topology. The proof installs the finite-dimensional module-topology
property on the target and applies
`IsModuleTopology.continuous_of_linearMap` to the equivalence and its inverse.
The result is a homeomorphism whose underlying maps are the supplied linear-map
conversion and the forgetful map. The theorem
`endomorphism_topology_eq_induced` extracts the induced-topology equality from
this homeomorphism.

Every construction and proof allows dimension zero. The finite coordinate
index is then empty, and the same norm and topology arguments apply without a
positivity assumption. The group universe `uG` and carrier universe `uV` remain
independent.

## Callable interface map

The algebraic lemmas apply to an actual complex representation
`ρ : Representation ℂ G V` with a finite-dimensional carrier, using
`FiniteRepresentation.of ρ`. Their proofs are definitional equality or
`Iff.rfl`: bundling preserves the actual carrier and action.

| Unbundled data or expression | Bundled data or expression | Callable comparison in `Langlands.FiniteRepresentation` |
| --- | --- | --- |
| `ρ` | `(of ρ).representation` | `representation_of` |
| `ρ.comp I.subtype` | `(of ρ).representation.comp I.subtype` | `representation_of_restrict` |
| `ρ.ker` | `(of ρ).representation.ker` | `kernel_of` |
| `(ρ.comp I.subtype).ker` | `(of ρ).inertiaKernel I` | `inertiaKernel_of` |
| `Set.range (fun i : I => ρ (i : G))` | `Set.range ((of ρ).representation.comp I.subtype)` | `inertia_range_of` |
| Finiteness of the unbundled inertia range | `(of ρ).HasFiniteInertiaImage I` | `hasFiniteInertiaImage_of_iff` |
| Openness of the restricted kernel in `I` | `(of ρ).HasOpenInertiaKernel I` | `hasOpenInertiaKernel_of_iff` |
| `Continuous (fun g => (ρ g).toContinuousLinearMap)` | `(of ρ).IsContinuous` | `isContinuous_of_iff` |
| `∀ v, Continuous (fun g => ρ g v)` | `(of ρ).HasContinuousOrbits` | `hasContinuousOrbits_of_iff` |
| `Continuous (fun x : G × V => ρ x.1 x.2)` | `(of ρ).HasContinuousAction` | `hasContinuousAction_of_iff` |
| `Weil.OperatorContinuityClauses I ρ` | `(of ρ).ContinuityClauses I` | `continuityClauses_of_iff` |

The continuity comparisons assume the normed finite-dimensional complex
structure used by the original target. `isContinuous_of_iff` applies the
homeomorphism's continuity criterion. `hasContinuousOrbits_of_iff` replaces
the canonical carrier topology by the norm topology.
`hasContinuousAction_of_iff` makes this replacement both in the target and in
the product topology on `G × V`. The pointwise comparison
`continuityClauses_of_iff` then rewrites each predicate, restricted kernel and
finite-image condition in the conjunction.

These adapters need only a topological space structure on `G` where continuity
or openness is mentioned, and work with any subgroup `I`. Compactness and
openness of inertia are needed as hypotheses of the original universal family,
not for the presentation adapters.

## Equivalence of the universal families

For the forward direction of `bundledRepresentationContinuity_iff`, apply the
bundled family to `FiniteRepresentation.of ρ`, then use
`continuityClauses_of_iff` to obtain the unbundled clauses.

For the reverse direction, start with an arbitrary bundled object `A`, install
its constructed coordinate norm and compatible complex normed-space structure,
and apply the unbundled family to `A.representation`. Transfer its conclusion
back using the same pointwise comparison. Bundling this action again retains
`A`'s carrier and action by definitional equality, so the result is precisely
`A.ContinuityClauses I.toSubgroup`. This direction ranges over every bundled
object, rather than assuming it already comes with a norm.

Both universal families quantify over a topological group and an open,
compact, nonarchimedean subgroup. The finite-image clause keeps the conjunction
with closedness of the inertia kernel. The proof does not add normality,
restrict rank or identify a supplied group with a local Weil group.

Finally, `representationContinuityCompatibility` assembles the carrier
topology theorem, the endomorphism topology theorem, the constructed-carrier
comparison, the complete predicate comparison and the universal-family
equivalence into the exact target conjunction.

## Provenance and preserved interfaces

This is internal, derived interface work. It uses the published `Basic`,
`Predicates` and `Continuity` pairs and the separately reviewed bridge
definition and statement pairs. Its topology input is Mathlib's
`isModuleTopologyOfFiniteDimensional` and `LinearMap.toContinuousLinearMap`
in `Mathlib/Topology/Algebra/Module/FiniteDimension.lean`, together with
`eq_moduleTopology` and `IsModuleTopology.continuous_of_linearMap` in
`Mathlib/Topology/Algebra/Module/ModuleTopology.lean`, at revision
`5ed2965256430c3649e86755f9576b54eca72435`. No additional original-literature
claim is made.

The module names and declarations in `Basic`, `Predicates` and `Continuity`,
including `Langlands.Weil.RepresentationContinuity`, are intentionally
retained. Their Lean and Markdown pairs are unchanged by this bridge.
Import `Langlands.Weil.Representation.ContinuityBridgeProof` to use the
comparisons above; it imports the new statement and definitions and both
existing presentations. No existing import path is replaced.

Author: Worker 38.
