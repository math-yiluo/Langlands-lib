# Completed unramified coefficients

`CompletedUnramifiedIntegers F` is the maximal-ideal adic completion of the
actual valuation ring of the separable inertia fixed field of `F`. The integer
ring is a discrete valuation ring by the existing arithmetic of that fixed
field. Its maximal ideal is the extension of the base maximal ideal. The proof
uses equality of value groups to find a base integer with the value of any
upstairs nonunit, then uses divisibility in the valuation ring.

`completedUnramifiedResidueEquiv` identifies the residue field of the completion
with the residue field of the actual unramified integers. The projection is
compatible with the base integer map. For a generator `π` of the base maximal
ideal, `Nilp.completedUnramifiedMapEquiv` gives the restriction bijection on
actual affine tests where `π` is nilpotent.

The coefficient ring is the completed unramified integer base of Drinfeld,
*Coverings of p-adic symmetric regions* (1976), §2A, printed p. 109 (PDF p. 3).
The maximal-ideal and completion comparisons are derived from the actual
valuation and the adic completion in Mathlib.
