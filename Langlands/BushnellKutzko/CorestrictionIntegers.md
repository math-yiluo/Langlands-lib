# Integer rings for the tame-corestriction argument

The ring `subfieldIntegers F E` is the integral closure used for
\(\mathfrak o_E\) by Bushnell–Kutzko 1993, §1.2, printed pp. 24–25
(`bushnell-kutzko-1993-admissible-dual-gln`). For a finite extension of a
nonarchimedean local field the module identifies this ring with the integer
ring for the spectral valuation. This gives its discrete valuation ring
structure and identifies its fraction field with \(E\).

For finiteness over the base integer ring, the proof bounds all coordinates
of the spectral unit ball in a finite basis of \(E/F\). After rescaling
these coordinates by a common scalar, they give an injection into a
finite free module over \(\mathfrak o_F\). The base integer ring is
Noetherian, so the integer ring of the extension is finite over it.
A nonzero base scalar can also move any given element of \(E\) into
\(\mathfrak o_E\), by choosing a scalar of sufficiently small norm.

The integral-closure equivalence and the two integer-ring instances use the arithmetic of the same extension. [Subfield integer arithmetic](SubfieldIntegerArithmetic.md)
