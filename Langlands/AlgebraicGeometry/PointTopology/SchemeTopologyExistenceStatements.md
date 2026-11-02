# Existence of the canonical topology on actual scheme points

Author: Worker 105.

The proposition `SchemePointTopologyExistenceProperty R S` is the existence
clause of Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Proposition 3.1, printed page 4, expressed using the
published actual relative point spaces and canonical affine-chart topology.
The registered source is `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The coefficient ring `R` and value algebra `S` are arbitrary commutative rings
in a common arbitrary universe, with `Algebra R S`. Only `S` is topologized.
The explicit statement hypotheses are `IsTopologicalRing S`, `IsLocalRing S`
and `IsOpenUnits S`. The latter is Mathlib's condition that the units are open
in `S` and inversion is continuous on the unit locus. No Hausdorffness,
compactness, local compactness, scheme separatedness or finite presentation is
assumed.

The target asserts `SchemePointTopologyAxioms R S` for the already constructed
`evaluationSchemePointTopologyFamily R S`. For every actual relative scheme
`X` locally of finite type over `Spec R`, this family gives its actual points
`RingPoint R X S` the topology `schemePointTopology R X S`, the final topology
from the evaluation topologies of all affine open charts. It requires:

- continuity of actual postcomposition by every relative morphism;
- compatibility with every limiting relative pullback cone, giving the actual
  compatible pairs the subspace topology in the product of the two factors;
- embeddings on actual points induced by closed immersions;
- open embeddings on actual points induced by open immersions;
- the usual topology of `S` on the actual affine line, through evaluation at
  its single polynomial coordinate.

The local finite-type hypothesis is attached to the scheme objects as in the
published five-axiom interface; the construction uses arbitrary nonaffine and
nonseparated schemes. Its agreement with the affine evaluation topology is
already the published theorem `schemePointTopology_eq_affine`. This unit
states the five axioms for the canonical assignment; it does not prove them,
assert uniqueness or include Hausdorffness and local compactness consequences.

Conrad states the case in which the coefficient ring and value ring coincide.
The separate `R` and local `R`-algebra `S` formulation is a derived relative
extension: affine evaluations take values in `S`, and gluing uses the closed
point of `Spec S`. Specializing `S = R` recovers the source existence clause.
The remaining sections of the paper remain obligations of the parent program.
