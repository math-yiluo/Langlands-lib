# Escaping opposite Iwahori bases in the actual norm kernel

This internal geometric bridge combines the integral Weyl correction,
character detection of compact escape, and the published dynamic open-cell
and uniform contraction arguments. It follows the explicit cocharacter
construction in `RationalOppositeIwahoriBasisProof`, with the cocharacter
value retained throughout the argument. Worker 485 supplied the norm-kernel
and positive-character route.

The structure `NormKernelEscapingOppositeIwahoriData` bundles a standard
cocharacter, an actual kernel element, its Levi commutation, its ambient
opposite Iwahori basis and its escape in the inherited kernel topology.
The final theorem packages the constructed witnesses as a nonempty instance
of this structure.

The first theorem fixes a standard cocharacter `ζ` and a field unit `t`
whose powers tend to zero. Under the same connected reductive, maximal split
torus, canonical point topology, local compactness, nonarchimedean group,
standard-cocharacter comparison and closed-radical hypotheses as the
published opposite-basis construction, its particular value `ζ(t)` commutes
with the standard Levi and admits an ambient cofinal compact open basis of
Iwahori contractions in both orders. No existential contracting element is
substituted for that value.

The standard subgroup comparisons identify the Levi and both radicals with
the dynamic subgroups of `ζ`. The cocharacter value is in the dynamic Levi
and commutes with it. Polynomial contraction proves uniform contraction
on compact subsets in both directions. The published unique factorization,
open-cell neighborhood theorem, and abstract opposite-basis construction
then give the claimed basis for this exact value.

The second theorem retains the actual relative-root-system premise.
For an actual finite simple-root subset omitting a simple root, it chooses
a standard cocharacter and replaces it by its integral Weyl correction.
The correction preserves all standard root signs and annihilates every
ambient rational character. Evaluating it at a unit with powers tending
to zero therefore gives a point in the actual common rational norm kernel.
The omitted simple root has positive pairing with the correction, so its
character detects escape from every ambient compact set. Continuity of the
actual subgroup inclusion gives escape in the norm kernel itself. The first
theorem supplies an opposite Iwahori basis for this same point.

Properness is expressed by the existence of an omitted actual simple root.
Thus no nonempty-root or positive-rank assumption is imposed on the ambient
group: when there are no proper subsets the assertion has no instances.
The basis remains a basis of ambient compact open subgroups. Transport of
Iwahori data to the norm-kernel subgroup, Jacquet vanishing, fixed-level
uniform coefficient support and the whole host proposition are subsequent
obligations.
