# Actual standard-block vanishing functions and the original GL cuspidal space

This derived construction works over an arbitrary number field `F` and in every
natural rank `n`. It retains the explicit instance `CompactSpace (AdeleQuotient F)`
used by the original normalized constant terms. No original GL function or
constant-term definition is changed.

`generalLinearStandardMaximalBlockIndex n` consists of pairs `(a,b)` with
`a+b=n`, `a>0` and `b>0`. For each index the subgroup is the actual two-block
subgroup functor, its rational quotient uses the Borel sigma algebra, and its
measure is `GeneralLinearBlockUnipotent.rationalQuotientMeasure`. This is the
measure already proved to correspond exactly to the original normalized matrix
Haar probability measure.

`generalLinearStandardBlockVanishingSubrepresentation` specializes
`familyVanishingConstantTermSubrepresentation` to precisely that family. Thus its
membership condition includes both absolute convergence and zero constant term
at every actual ambient adelic point for every positive two-block split. The
family construction proves complex linearity and stability under positive right
translation. Convergence is supplied by the previously proved actual block
convergence theorem, independently of whether the integral vanishes.

`mem_generalLinearStandardBlockVanishingSubrepresentation_iff` identifies this
membership condition with the original `Langlands.Automorphic.IsCuspidal` after
applying the existing `continuousGeneralLinearEquiv`. Its proof expands family
membership, applies the exact block vanishing comparison, and converts the
subtype indices into the original quantifiers over `a,b,h,a>0,b>0` in both
directions.

`GeneralLinearStandardBlockVanishingFunctions` is the carrier of that actual
subrepresentation, and `generalLinearStandardBlockVanishingRightAction` is its
restricted positive right action. `generalLinearCuspidalEquiv` restricts the
original ambient complex linear equivalence to this carrier and the original
`Langlands.Automorphic.cuspidalSubrepresentation`. Its forward and inverse maps
are exactly the ambient maps, as recorded by the two coercion lemmas. The inverse
membership proof uses the membership equivalence and the ambient inverse law;
the linear and inverse laws are inherited by subtype extensionality.

`generalLinearCuspidalEquiv_rightAction` proves compatibility with the original
cuspidal right action through the actual adelic point homeomorphism. Both actions
use `R(g)f(x)=f(x*g)`, with no inversion. The proof reduces by subtype
extensionality to `continuousGeneralLinearEquiv_rightAction`.

The final theorem proves that this subrepresentation is the full ambient
representation when `n≤1`: positivity of both blocks contradicts `a+b=n`.
The construction and equivalence therefore include ranks zero and one without
additional hypotheses or artificial nonempty indices.

This is an internal comparison derived from the existing actual subgroup,
quotient, measure and constant-term comparisons and the original continuous GL
cuspidal definition. It invokes no new external theorem. The supplied standard
maximal two-block family is not proved here to enumerate all proper rational
parabolics. This construction does not identify the full general reductive cusp
space or establish smoothness, growth, finite volume, square integrability or a
Hilbert realization. Those broader host-task obligations remain separate.
