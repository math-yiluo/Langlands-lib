# Unique-place supercuspidality from the Rankin–Selberg self-pair comparison

`CyclicWeakInductionSelfPairGammaOrderAtUniquePlaceStatement` specifies a
local comparison for the supplied weak induction `S` of `T`. For actual
presentations and the full arithmetic orbit of `T`, it asks for certified
local Rankin–Selberg gamma factors at the distinguished completions. At
each real spectral point, the order of the self-pair gamma factor of the
downstairs action must be the sum of the orders of the upstairs pair
factors. The upstairs factors pair the original component of `T` with
the actual smooth contragredient of each conjugate component. The
identity conjugate occurs once in the indexing family.

`CyclicWeakInductionSelfPairGammaOrderAtUniquePlace F E` expresses the comparison for
specified number fields `F` and `E`. `cyclicWeakInductionSupercuspidalAt_of_gammaOrder`
uses this comparison at the specified Galois extension to prove its supercuspidality
conclusion. Universal quantification over the fields gives the unrestricted reduction.

The comparison is modeled on Henniart–Herb (1995), Lemma 8.13 and
§§8.16–8.17, printed pp. 179–184 (PDF pp. 49–54). Their cofinite pair
Euler identity and functional-equation localization lead to a comparison
at the chosen place. The Lean premise retains only the meromorphic
orders needed here. It applies to the supplied weak induction and leaves
the functional-equation localization as a proof obligation.

`cyclicWeakInductionSupercuspidal_of_gammaOrder` assembles the upper
orbit from the given witnesses and uses the original component at the
identity index. The weak Euler identity supplies unitarity of the
downstairs central character. A genuine irreducible admissible finite
slice supplies its presentation in the required carrier universe.
The actual upper conjugate actions are unitarizable because arithmetic
transport identifies them with automorphism pullbacks of the original
upper action. The equivalence uses the extension of the arithmetic
automorphism to the unique completion upstairs.

Every upper gamma order is nonpositive at nonzero real points by
`unitarySupercuspidalPairGammaOrder`. At zero the same result gives one
precisely when the two upper actions before dualizing have equal smooth
class, by admissible biduality. The only such index is the identity.
Consequently the downstairs gamma factor has a simple zero at zero
and no other real zeros. The local criterion in `PairGammaOrder`
then makes the actual component of `S` supercuspidal. The conditional
unrestricted theorem and its totally complex specialization preserve
the positive ranks and all four independent universes.
