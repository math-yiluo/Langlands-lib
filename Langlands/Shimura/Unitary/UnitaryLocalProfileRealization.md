# Global realization of unitary local profiles

`unitaryLocalProfileRealization` proves
`Langlands.Shimura.FiniteUnitary.UnitaryLocalProfileRealizationStatement`
over the supplied CM extension. The base field and CM field are
quantified in independent universes. The witness carries the required
real signature charts, the maximal-Witt charts at finite places outside
the support, and the specified signed Brauer invariants at both upper
places above each place in the support. The theorem applies to any
compatible profile, including empty support and nonprimitive residues.

In odd degree, `realizeOddUnitaryLocalProfile` constructs the signed
Brauer algebra and involution, sets the real signatures by a symmetric
twist, and uses the odd-dimensional local Hermitian decomposition at
the nonsplit finite places. In even degree, `initialUnitaryProfile`
sets the same signed Brauer data and prescribed real signatures.
`unitaryProfileDiscriminantValues` computes the localizations of the
initial unitary discriminant in the actual completions. Brauer
reciprocity and the profile compatibility equation make the finite
set of nonsplit signed-determinant norm defects even.
`realizeEvenUnitaryLocalProfileOfDiscriminant` chooses one positive
symmetric twist that corrects those defects and preserves the real
signatures and the underlying Brauer algebra. The two branches yield
the same witness type, whose fields supply the exact existential
conclusion.

Clozel’s localization criterion and the split and real obstruction
computations give the parity condition. The split contribution in even
rank is the reduction of the residue modulo two. At a real place the
contribution \(m+(2m-r)\) is congruent to \(r-m\) modulo two.
[Clozel 1991, §2.1, (2.2)–(2.3) and Lemmas 2.1–2.2, printed pp. 102–105](https://www.numdam.org/item/PMIHES_1991__73__97_0/)

The proof computes the discriminant via the determinant factor set from
middle exterior power descent. The restriction to the center gives
the half-degree Brauer multiple, and the comparison with a Hermitian
chart gives the signed determinant norm criterion. These are the
discriminant formulas in Knus, Merkurjev, Rost and Tignol, *The Book
of Involutions* (1998), §10.E, (10.28) and (10.30), and §10.F, (10.35).
