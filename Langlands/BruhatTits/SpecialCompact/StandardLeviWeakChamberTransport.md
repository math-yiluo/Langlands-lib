# Weak chambers and complete basis members inside a standard Levi

This internal module proves that the complete standard-parabolic basis-member
property passes from the ambient group to the canonical outer standard Levi,
for nested root subsets and the same compatible split component. It composes
published algebraic and contraction results and introduces no new
original-literature assertion.

The generic `WeakChamberContraction.comap_of_conjugationLifts` takes a group
homomorphism and exact preimages of the original subgroup and both radicals.
It transfers weak-chamber preservation if every source chamber conjugation
on the source group is realized by an original chamber point on its image.
The inverse-conjugation identity follows from the forward one by applying it
to the inverse conjugate. No injectivity or topology is needed for this
generic implication.

`IsCompatibleStandardSplitComponent.exists_cocharacter_lift_of_annihilates`
extends the existing integral component-lifting API from strictly standard
cocharacters to every integral cocharacter annihilating the selected roots.
It assumes a maximal split torus and standard-cocharacter existence for the
face. The published annihilator-centrality theorem makes that cocharacter
central in the same represented Levi; the actual split-component universal
property factors it integrally through the original component. Cancellation
against the maximal torus embedding gives the same original map `q`. There
is no isogeny denominator or valuation-index premise.

`standardLeviWeakChamberShift` is the sum of the absolute integral pairings
of the original component cocharacter against all ambient simple roots.
Its bound theorem controls each absolute pairing, including when the
simple-root type is empty.

For an outer face `J` and inner face `R` contained in `J`,
`exists_ambientWeakChamber_conjugation` treats the whole intrinsic weak
chamber for `R`. Its inequalities involve only `J` minus `R`, whereas the
ambient chamber involves all ambient simple roots outside `R`. The proof
chooses a standard cocharacter for the outer face and lifts it to the same
inner compatible component. It adds the finite nonnegative shift times this
lift to the original component cocharacter. On roots in `J`, the adjustment
pairs to zero and preserves the original inequalities. Outside `J`, its
positive integral pairing is at least one; the chosen absolute-pairing sum
offsets any negative original pairing. The common-uniformizer character
formula therefore puts the adjusted point in the original ambient weak
chamber, with its original norm normalization.

The adjusting cocharacter is central in the outer Levi. Its uniformizer
value, and every integral power, act trivially there by conjugation. Exact
naturality of common-uniformizer evaluation and the original Levi factor
identity show that the adjusted ambient point is the original intrinsic
point times this central power, read through the actual embedding. Thus it
induces precisely the same conjugation on every outer-Levi point. The proof
does not identify the two unequal chambers or assume extra inequalities on
the original intrinsic parameter.

`standardLeviRadicalPreimages` proves the exact preimage identities for both
the intrinsic standard radical and its opposite, using a nested standard
cocharacter and the published dynamic comap and reversal comparisons.
`weakChamberContraction_leviScheme` combines these identities and the proved
central adjustment with the generic conjugation-lift implication. It retains
the same original subgroup, compatible component and root subsets.

`StandardParabolicBasisMember.leviScheme` takes an original compact open
basis member and concludes its full intrinsic basis-member property at
`leviSchemeCompact` of that same subgroup, with the same component `A,q`.
It obtains Iwahori factorization from `StandardLeviIwahoriTransport`, component
compatibility from `StandardLeviComponentTransport`, and weak preservation
from this module. The published
`IsCompatibleStandardSplitComponent.contractionAndCofinality_of_weak` then
supplies Levi-intersection normalization, strict-chamber exhaustion, compact
containment, power-neighborhood bases and uniform compact-open cofinality.
Only weak preservation had to be transferred to the enlarged intrinsic
chamber; these other conclusions follow from the published actual-point
contraction theory and the proved compact openness of the inherited subgroup.

The field and group are arbitrary nonarchimedean local-field and connected
reductive data, with no characteristic, splitness or quasisplitness
restriction. The original compact open subgroup and original component are
not replaced by unrelated choices. The finite simple-root enumeration is
chosen only inside the conjugation-adjustment proof.

This module does not assemble a complete simultaneous standard basis: the
common inherited compact-open normal neighborhood family remains a separate
input to that assembly. It also proves no source-Levi Iwasawa factorization
at an arbitrary original ambient compact subgroup, no analytic coefficient
bound, and no wave-packet Schwartz or continuity target.
