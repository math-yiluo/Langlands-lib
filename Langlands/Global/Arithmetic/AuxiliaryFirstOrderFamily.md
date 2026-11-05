# A family of finite first-order local characters

Worker 84 implements a family-construction lemma used by the final assembly.
It imports the separate deep-unit character and principal-unit extension
theorems by Lean name. The exact proof task records their independent
prerequisites; their original authorship remains in those separate pairs.

For each supplied topology T and nontrivial continuous unitary additive character
psi, choose the fixed natural offset C=max(0,-conductor(psi)). Since the positive
integer e=ord(p) is at least one, -C*e is at most the conductor. At every natural
k put c=p^(C-2k) and n=k*ramificationIndex. The exact prime-power valuation law
v(p^z)=exp(-z*e) identifies n with k*e and the quadratic bound
v(c)*exp(-2n)=exp(-C*e)<=exp(conductor(psi)).

The prescribed deep-unit character therefore exists. Composing its Circle
values with the continuous inclusion into complex units and applying the
principal-unit extension theorem gives a continuous character chi on all field
units with one positive finite annihilating exponent and the exact first-order
formula on principalUnits n. The same valuation law proves that
v(c)*v(p^k)^2 is within the conductor bound, that v(p^k)=exp(-n), and that this
value is strictly less than one when k>0. These are precisely the scalar bounds
needed by the norm-trace character comparison.

Every prime including two and every natural k including zero is retained. The
lemma imposes no nontriviality requirement on a fixed member. As k increases,
the linear coefficient c*p^k=p^(C-k) is available for simultaneous detection;
the other helper modules and AuxiliaryCharacterFirstOrderProof implement the
identity, depth witnesses, topology comparison and final exact stabilizer. This
file itself proves only the stated family and scalar bounds.
