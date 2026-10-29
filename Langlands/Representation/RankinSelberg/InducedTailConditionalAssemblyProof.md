# Conditional assembly of induced tail divisibility

Implementation and proof explanation: Worker 53. Preparation and validation
for this contribution: Worker 356.

The theorem `Langlands.RankinSelberg.inducedTailConditionalAssembly` proves
exactly the separate
[conditional assembly statement](InducedTailConditionalAssemblyStatement.md).
Its six premises are the three-span conjunction, normalized product full
Whittaker type, symmetric L-polynomial existence, opposite two-block
L-divisibility, the exact heterogeneous triple associator, and scalar-carrier
high-ramification vanishing. This proof discharges none of those premises and
does not prove the closed `InducedTailLFactorStatement` of the parent task.

First, `inducedTailLFactor_of_commonUniverse` transports the parent conclusion
from the common carrier universe containing the field and all three original
carriers. It uses actual universe-lift representation equivalences and the
published heterogeneous-pair comparison. Both polynomial certificates retain
their polynomials, and divisibility is unchanged. The four independent
universes and literal carrier conjugations of the parent conclusion remain.

A successor-family adapter packages an ordered positive rank function and
its dependent representation family in a Sigma type. Equality of the two
packages identifies the finite-family interfaces with the actual
`Shahidi.twoBlocks` and `Shahidi.pairFamily`. The induced representation
equivalence does not reorder the blocks. From it, the assumed normalized
product full-type proposition gives full Whittaker type of the actual
heterogeneous pair. The opposite-divisibility adapter applies the supplied
two-block theorem to certified polynomials already chosen by the proof.
Actual equivalences, symmetric-certificate exchange and uniqueness retain
those polynomials. Unequal-rank exchange is definitional; equal-rank exchange
uses the published `isPadicPairLPolynomial_swap_equalRank`.

The rank transport helper eliminates equality of successor-rank indices and
proves that precomposition by the coordinate-preserving `GeneralLinear.reindex`
along `finCongr` retains the certificate. A generic associator helper unfolds
only the heterogeneous-pair definitions with abstract carriers. It specializes
the supplied literal three-block associator to nested heterogeneous pairs,
retaining its exact ambient rank cast. This separates the type identification
from the later concrete induction.

The character selector applies the high-ramification premise to the trivial
rank-one character against the fixed test representation. The published
`padicQuasicharacterUnboundedConductor` supplies an actually continuous
quasicharacter above the threshold. An elementary action identity identifies
the determinant twist of the trivial scalar character with that character's
rank-one representation. Its symmetric L-polynomial certificate `1` is then
transported to the actual universe lift. Full type of this lifted rank-one
representation uses the published `rankOneWhittakerType` and equivalence
transport.

The main theorem `inducedTailLFactor_of_inputs_commonUniverse` works in a
carrier universe `max uF u`, closed under actual normalized induction. It
fixes the original second block, the test representation, and a certified
tail polynomial obtained from the existence premise. It inducts on an upper
bound for `t + 1 - (c + 1 + b)`, quantifying over every possible first-block
carrier, action, full-type certificate, and certified full polynomial.

When test rank is below full rank, the separate
[direct assembly](InducedTailDirectAssembly.md) applies one of the three
assumed actual Laurent-span comparisons. In the remaining range, prepend one
ramified scalar character `mu`. Write `xi = rho × pi2`,
`tau = mu × rho`, and `eta = mu × xi` for the actual heterogeneous inductions.
The full-type and existence premises supply a certified polynomial `Peta`.
The exact associator, with its ambient rank cast, compares `eta` to
`tau × pi2`. The induction hypothesis applies to this first block of rank
one greater, with deficit decreased by one, and gives `Ptail ∣ Peta`.

The opposite-divisibility input applies instead to `eta = mu × xi`. Since
the character-versus-test certificate is `1`, it gives
`X^k * P = Q * Peta` for the previously supplied full polynomial `P`.
Hence `Ptail` divides `X^k * P`. Every certified tail polynomial has constant
coefficient one. An explicit Bezout identity with `X` shows that it is
coprime to `X`, so the extra power can be removed and `Ptail ∣ P` follows.
Finally, the existence premise supplies the original full polynomial and
the induction is applied to it. The exported theorem combines this result
with the four-universe transport and has exactly the conditional statement
as its type.

Provenance is internal derived infrastructure over the published actual
induction and certified-factor definitions. The ramified-enlargement route
implements the use of successive scalar characters described by the parent
interface's interpretation of JPSS (1983), Section 9.3. The analytic source
interpretations remain in the imported statement pairs; no new translation
of a literature theorem is asserted here. All six prerequisites retain their
own proof and publication obligations. In particular, this conditional proof
does not use the section-9.3 parent conclusion to establish the opposite
section-7 bound or its restricted-section-5.5 prerequisite, and it proves no
high-ramification result using full multiplicativity.
