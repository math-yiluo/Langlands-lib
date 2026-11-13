# Normalized valuations of the finite splitting fields

This is an auxiliary construction for Kaletha–Prasad, §11.1, Proposition 11.1.1
(printed pp. 420–421; PDF pp. 451–452), in *Bruhat–Tits theory: a new approach*
(2023), source `kaletha-prasad-2023-bruhat-tits-new-approach`. The 2024 corrections
do not change this proposition. The book uses the valuation on the finite
splitting field `L/K` normalized to have value group `ℤ`. Here `K` is the
Library's actual `UnramifiedClosure F` in `SeparableClosure F`, and `L` is an
intermediate field of that extension. A finite extension of `K` need not be a
local field.

`IsNormalizedIntermediateValuation F L v` says that the integer-valued
multiplicative valuation `v` has exactly the ordering of the Library's restricted
spectral valuation `intermediateValuation F L`, and that `v` is surjective onto
`WithZero (Multiplicative ℤ)`. The ordering condition fixes the valuation ring
and the orientation; surjectivity fixes its scale. The source-positive additive
order is `IntegerValuation.orderUnits v`, which is the negative of the logarithm
in the multiplicative value group. Thus a uniformizer has additive order one.

`normalizedIntermediateValuation` selects a valuation by this characterization,
using classical epsilon. The separately stated, unconditional
`NormalizedIntermediateValuationStatement` requires existence and uniqueness for
every finite `L/K` and every nonarchimedean local field `F`, in either
characteristic. No proof of that statement is asserted here.
`normalizedIntermediateValuation_spec` is only the elementary epsilon implication
from existence to the selected valuation's law; it does not prove existence.
The trivial valuation supplies the nonempty ambient type for epsilon and does
not supply the required normalization law.

The auxiliary characterization is a derived implementation of the integer
normalization required in KP 11.1.1, rather than a separately numbered result in
the book. Subsequent Kottwitz targets must retain its unconditional existence
obligation rather than assuming normalization as an extra field hypothesis.
