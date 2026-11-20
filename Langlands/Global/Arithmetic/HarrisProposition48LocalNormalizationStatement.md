# Actual rank-one components and integral determinant twists

`RankOneWeakInductionLocalStatement` is a degree-one specialization of the
unramified characterization in Harris (1998), Definition 1.3(b), printed
p. 186. Its antecedent uses the numerical spectrum of the supplied actual
presentation. Its conclusion identifies the global central action with the
arithmetic pullback of the inducing Hecke character and gives the scalar action
on each embedded local component of the same presentation. In degree one the
Euler product has one factor of residue degree one. Its linear coefficient
gives the uniformizer value in the top-elementary-coefficient criterion
`CuspidalOperatorRealization.hasCentralCharacter_of_eventually_elementaryCoefficient`.
The local center in rank one is the full group, so the central action gives the
determinant scalar even at the auxiliary place. Harris uses class field theory
in rank one at the beginning of the proof of Proposition 4.8, printed p. 202,
and compares the local characters in the prime orbit on p. 203. Geometric
reciprocity will be used when comparing the corresponding Weil characters.

`IntegralDeterminantTwistRegularAlgebraicStatement` is the integral determinant
shift of the highest weights in Clozel (1990), Définitions 1.8 and 3.12, as
used for Harris's `Reg(n,E)` in §1, printed p. 185. On the actual operator
algebra the determinant multiplier conjugates the enveloping action by
`heckeEnvelopingShift`. In each complex embedding the shift adds the same
integer to every entry of the highest weight. This preserves dominance and
integrality and yields the infinitesimal character for the multiplied
operator realization. In Proposition 4.8 this permits the common parity
correction to replace the individually transported correction after an
integral determinant twist. The parity convention appears in Harris (1998),
printed p. 195, and the orbit comparison is on p. 203.

`Proposition48LocalNormalizationStatement` groups these two inputs. The base
field, inducing field and spectral carrier universes are independent.
