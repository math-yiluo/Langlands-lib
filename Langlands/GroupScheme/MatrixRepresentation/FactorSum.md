# The finite map supplied by actual simple factors

This internal construction implements the finite-map reduction in KP
Lemma 2.2.11 (printed pp.72–73, PDF pp.103–104, *Bruhat–Tits theory: a new
approach*, 2023).

`factorSum` is the actual finite direct sum of a `SimpleFactorFamily`. Its
all-test kernel is exactly the common kernel of the factors. The recorded
nilpotent-power identity of the family therefore proves that the original
quotient representation acts unipotently on every subgroup killed by this
sum, on every scheme test.

Over an algebraically closed field, let the original representation be
closed and faithful, with smooth affine source and trivial unipotent
radical. The sum factors through its actual schematic image, whose projection
is faithfully flat and quasi-compact and whose inclusion is closed. Its full
kernel acts unipotently in the original faithful representation. The finite
normal-subgroup criterion proves this kernel finite, including nilpotents.
The fpqc finite-kernel theorem makes the projection finite, and composition
with the closed image inclusion makes the original factor-sum map finite.

No complete reducibility of the original representation or smoothness of the
kernel is assumed. Empty factor families and zero original dimension remain
included. Boundedness of the factor images and descent to the local base field
are separate obligations.
