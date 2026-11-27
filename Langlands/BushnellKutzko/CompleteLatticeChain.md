# The complete lattice chain of an ordered basis

In the lattice-chain description of Bushnell–Kutzko (1993), (1.1.1),
the complete chain in \(F^d\) multiplies one coordinate by the
uniformizer at each step and repeats the pattern every \(d\) steps.
It models the chains used for minimal relative orders in (5.1.12)
and (5.2.3).

At position \(i\), the lattice is a diagonal image of the standard
integer lattice. The diagonal entry at coordinate \(j\) is the
uniformizer to the power \(-\lfloor(j-i)/d\rfloor\).
For a nonzero coordinate \(v_j\), the corresponding membership
inequality is \(i\le j+d\,\operatorname{ord}(v_j)\). At each position
the basis vector at the residue class of \(i\) modulo \(d\), scaled
by the uniformizer to the quotient power, lies in that lattice and
leaves at the next step. The same inequalities give periodicity
after multiplication by the uniformizer.
