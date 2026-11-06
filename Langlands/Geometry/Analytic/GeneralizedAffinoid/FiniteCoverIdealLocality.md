# Global ideal membership on a finite full-domain cover

This is derived internal infrastructure for finite-cover closed-ideal
effectiveness. It proves that closed extension followed by contraction is the
identity on global ideals. It does not assert that every compatible family of
local ideals is effective.

`relativeCover` views an arbitrary finite cover of a full domain `U` as a cover
of the whole spectrum of `U.algebra`. Its component algebras and actual
restriction maps are unchanged. The proved relative-domain locus identity
transfers the coverage condition.

For a global ideal `J`, `quotientCover` pulls this relative cover back to the
actual presented closed quotient by `J`. Closedness is supplied by the general
affinoid ideal-closedness theorem in `Noetherian`. Each component is the actual
affinoid pushout of the quotient map with the original cover restriction.

If every restriction of an element `a` lies in the corresponding closed
extension of `J`, then its image in every component of the quotient cover is
zero. The actual pushout square and the kernel calculation in
`ClosedQuotientBaseChange` establish this vanishing. Scalar separation for
finite full-domain covers then makes the image of `a` zero in the global
quotient, hence `a` belongs to `J`. The converse is immediate from membership
of an ideal image in its closed extension.

Consequently, contracting all the closed local extensions recovers `J`,
and componentwise inclusion of extensions detects inclusion of global ideals.
`idealExtensionOrderEmbedding` packages the resulting embedding into the
product of the actual component ideal lattices.

The proof uses no module descent or ideal effectiveness theorem. It retains
arbitrary positive radii, trivial coefficient valuations, nonreduced and zero
algebras, empty spectra and empty finite covers. Its provenance is the
composition of the Library's actual closed quotient base change, full-domain
base change, scalar finite-cover separation, and the derived general
Noetherianity and ideal-closedness results.
