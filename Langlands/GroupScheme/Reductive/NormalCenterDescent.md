# Descent of full-centre containment for normal reductive subgroups

This internal deduction extends the published algebraically closed conditional
centre-containment theorem to every field. The ambient full centre has its
published closed representative. Pulling that representative back to the source
group represents the preimage of the ambient centre. Fpqc reflection of
containment in a represented subgroup, together with arbitrary-base-change
compatibility of the full centre and subgroup preimages, descends containment
from the new base to the original base.

The algebraic closure of the ground field gives the fpqc cover. Both connected
reductive groups remain connected reductive there, the given closed subgroup
inclusion remains closed, and its all-test normality persists under base change.
The published conditional algebraically closed theorem therefore applies. This
proves `NormalReductiveCenterStatement` from the explicit premise
`FixedCenterContainingTorusStatement`, in arbitrary universe. The fixed-torus
premise and the host semigroup comparison remain separate obligations.

Under `NormalReductiveCenterStatement`, `normalCenterMap` is the actual group
scheme homomorphism between supplied full-centre representatives of a closed
normal inclusion of connected reductive groups. It factors the source-centre
inclusion followed by the given inclusion through the ambient-centre inclusion.
Its composite with that inclusion is the original composite, this property
characterizes it uniquely, and it is a closed immersion. The construction uses
the represented-subgroup factorization; closedness follows because the composite
and the ambient-centre inclusion are closed immersions. The conditional theorem
above supplies its centre-containment premise from the fixed-torus proposition.
No centre or test scheme is required to be smooth or reduced.
