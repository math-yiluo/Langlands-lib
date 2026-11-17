# Source-normalized standard-Levi packet central control

This module is an internal specialization of `OrbitSectionLevelCentralDecay`
and `StandardLeviSquareIntegrableCoefficientBound` to the source-normalized
packet of the unchanged `StandardLeviPlancherelWavePacketSchwartz` targets.
It is derived from existing constructions and proved comparison laws; no new
original-literature statement or new topology is introduced. All declarations
are in `Langlands.HarishChandraSchwartz`.

All original source-normalized packet data are retained: an arbitrary
nonarchimedean local field, a general connected reductive group and actual
standard Levi, the original irreducible admissible representation on the
literal Levi, the actual split component and its finite-index valuation-image
premise, the displayed central quotient Haar measure and square integrability,
and the conditional continuation, generic irreducibility and unitary regularity
data defining the actual Plancherel weight. The scalar construction's `Ks` and
the packet's `K` remain separate. The field and representation-carrier universes
are independent. The matrix representation is the original arbitrary `ρ`.

This internal central estimate additionally retains explicit intermediate
structural data: the Levi Iwasawa pair for `K ∩ M_I(F)` and a compact subgroup
of the intrinsic Levi group with its simultaneous standard basis and finite
Cartan covering. It assumes no coefficient Xi bound. Instead,
`hasXiBoundedCoefficients_standardLeviSquareIntegrable` derives that bound from
the original square integrability, exact transported central quotient Haar,
finite-index valuation premise and these structural inputs. Their existence
remains to be supplied for the final target, which has no such extra premises.

For every open subgroup `H ≤ K` and real order `r`,
`standardLeviPlancherelPacketCentralControl H hHK r` is a seminorm on the
original `OrbitSectionLevel ... H`. It is the generic central-control seminorm
specialized to the original actual source-normalized character measure
`standardLeviUnitaryUnramifiedCharacterHaar` and original
`standardLeviPlancherelWeight`. The actual finite stabilizer instance is derived
from the split component and its finite-index premise. The construction is a
nonnegative multiple of a finite supremum of the original input derivative
seminorms, with choices independent of the varying section and group point.

`norm_standardLeviPlancherelPacket_le_centralControl` proves, for every section
`q` at that same prescribed subgroup and every actual group point `g`,

`norm (packet (includeLevel H q) g)
  ≤ standardLeviPlancherelPacketCentralControl ... H hHK r q
      * rationalXi hKc hPK g
      * (1 + norm (rationalValuationCoordinates G hG g))^(-r)`.

The left side is the literal packet from the original target. It is not a
newly normalized integral. The generic proof retains the actual character
measure mass and stabilizer divisor; the auxiliary central-torus probability
measure is used only inside the Fourier averaging proof.

The specialization supplies the required Laurent coordinates and their
continuity, the smoothness of the actual Plancherel weight, the actual
`rationalValuationCoordinatesHom`, the integer Levi restriction matrix, its
character restriction identity, and triviality on the compact subgroup and
unipotent radical from their published theorems. The actual Levi and modulus
comparison theorems provide the generic Iwasawa/Levi data, and compact-open
cofinality of the actual Levi is proved by the published
`compactOpenCofinal_standardLevi`. The generic Xi function is definitionally
the same actual `rationalXi`. The compactness and local compactness instances
are supplied from the actual subgroup theorems; no extra topological premises
are introduced.

`continuous_standardLeviPlancherelPacketCentralControl` specializes the
continuity of the generic control to the existing section-level topology.
This is continuity of the real-valued input seminorm. It is not a proof of a
Schwartz-valued packet map or a comparison with the independently constructed
finite-product tensor topology.

The output decay concerns the actual central valuation coordinates alone.
It supplies no full `rationalHeight ρ` decay estimate. Structural existence,
the lower-Levi weak packet expansion, the positive-part estimate and the
full-height rank induction remain obligations. The original membership,
continuity and joint VI.3.1 propositions are unchanged and remain unproved.
