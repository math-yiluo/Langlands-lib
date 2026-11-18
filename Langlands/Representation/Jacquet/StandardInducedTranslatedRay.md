# Common thresholds for fixed Levi translates of the actual induced ray

`HasStandardConstantTermEqualityAt` states equality of the ambient value at
a specified Levi point with its chosen normalized standard constant term
times the standard radical half-modulus. The ray theorem obtains this
equality after a fixed Levi translation. A family sharing a bi-invariance
subgroup has a shared bi-invariance subgroup after that translation, given
by the intersection of the original subgroup with its conjugate. At an
original standard basis level contained in the intersection, the untwisted
induced fixed dimension bounds the ray threshold for all translated
coefficient tensors in the family.

The implemented translated ray identity uses the actual coefficient-tensor
action and the existing chosen constant-term translation theorem, including
its original half-modulus factor. It retains all unramified twists and
arbitrary coefficient tensors, with no continuity assumption on the chosen
constant term or the tensor representatives.

The contextual original source is Waldspurger, *La formule de Plancherel pour
les groupes p-adiques, d'après Harish-Chandra* (2003), Proposition I.6.2,
printed pp.249–250, and VI.2.3, printed pp.299–300, source
`waldspurger-2003-plancherel`. The explicit dimension threshold and recurrence
route are derived project content.
