# Actual rational coherence of direct and successive formal refinement

This internal module defines `orderCompQuasi` by rationalizing and
evaluating the existing specified actual `orderCompIso`. Its
source is the tested chart of the direct composite refinement;
its target is the tested chart of the successive refinement.

`orderCompQuasi_chart` follows that actual comparison by the
successive refined-chart identifications, first to the
intermediate chart and then to the original chart. The result
equals the direct refined-chart identification, as an entire
actual full-order quasi-isogeny.

The proof compares forward rational maps, uses the actual tensor
composition equations, and reduces the resulting integral
formal-map equality to compositions of identity coordinate
series. The uniquely determined inverse maps therefore also
agree.

The scalar ring is a commutative domain with specified fraction
field, the coefficient ring is any commutative scalar algebra,
the acting order is any algebra ring, and coordinates are finite.
The successive principal covers may be infinite, and test
algebras use the coefficient-ring universe.

The supporting `symm_trans_of_trans_eq` derives
`h⁻¹` followed by `f` equals `g⁻¹` from an actual
factorization `f` followed by `g` equals `h`; it uses
associativity and the stored actual inverse equations.

The provenance is internal from actual formal refinement
composition, chart identifications and tensor composition. No
point-evaluation faithfulness, height, moduli or representability
assertion is assumed.
