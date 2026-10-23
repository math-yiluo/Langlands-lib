# Compact-volume conditions in Shahidi's normalization

This derived prerequisite implements the two compact-volume equations in
measure items 2 and 3 of Shahidi, *Fourier transforms of intertwining operators
and Plancherel measures for GL(n)* (1984), printed page 76. The original is
registered as `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.
It supplies actual integration sets and relations on supplied measures.
It does not prove the existence of suitable measures or the comparison theorem.

The rank in Lean is n+1, so the smaller general linear group has rank n.
For a subring O of a field F, `idealFieldSet O I` is the image in F of the
ideal I of O. `compactNormalizationSet O n I` consists of actual invertible
(n+1)-by-(n+1) matrices with the displayed source block conditions:

- The upper-left n-by-n block belongs to GL_n(O).
- The upper-right column has entries in O.
- The lower-left row has entries in the image of I in F.
- The bottom-right entry belongs to O's unit group inside F's units.

The upper-left block has no congruence restriction. In particular this is
not the newvector subgroup requiring the final diagonal entry to be one
modulo I. The definition uses the published
`GeneralLinearGroup.integralSubgroup`, whose elements and inverses have
entries in O, and `RankinSelberg.integralUnits`, the actual image of O's
unit group. The set contains the identity and grows when I grows; both
facts are proved directly from these coordinate conditions.

`compactNormalizationTest` is the inverse image of this set in the actual
integral subgroup K_(n+1), so a supplied measure on K can evaluate it.
This definition is meaningful for arbitrary ideals. The module does not
assert that the ambient block set is contained in K for arbitrary ideals,
or prove compactness, openness or subgroup closure of the block set.
For the intended local-field specialization, O is the integer ring and
I is a positive power of its maximal ideal, exactly as on page 76.
The test sets decrease as the power increases, by monotonicity of ideal
powers and inverse images. None of these constructions selects a measure.

`centralCompactProductMeasure` is the actual product
(d*a × dn₂) × d*z on (GL_n(F) × F^n) × Fˣ. The vector coordinate identifies
the last-column unipotent group with F^n; transporting an actual unipotent
measure to this coordinate space is a separate requirement. Its designated
integration set `centralCompactProductSet` is
(GL_n(O) × O^n) × Oˣ. `IsCentralCompactNormalized` requires this set to have
mass one, preserving the source's single product condition. Under
s-finiteness of dn₂ and d*z, two applications of the product rectangle
formula give `centralCompactProductMeasure_mass` and the equivalent scalar
mass equation `isCentralCompactNormalized_iff`. There is no requirement
that any of the three factor masses separately equal one.

For a local ring O, `IsCompactBlockNormalizedAt O n dk dx r` requires
r ≥ 1 and the actual equation

    dk(Ktilde_(n+1,r)) = product over i : Fin n of dx_(i+1)(P^r).

Here the whole row has coordinates indexed by `Fin (n+1)`; `i.succ`
selects every coordinate except the first. This is the source's product
of dx₂ through dx_(n+1). Each scalar measure is supplied independently.
`IsCompactBlockNormalizedAt.rowMass` identifies the right side with the
actual product measure of the ideal box, assuming sigma-finiteness of the
scalar measures. It uses the published row-product box formula.

`IsCompactVolumeCompatible` conjoins the central product condition with
existence of a positive level satisfying the block mass equation. The
source says the equation can be imposed at some positive level and then
holds at every such level. This unit records the first condition and
does not claim the second assertion as a proved fact or an assumed field.

The bare relations use unbundled measures on the smaller general linear
group, the last-column coordinates, the field units, and K, and bundled
scalar additive Haar measures. Haar and regularity properties of the
unbundled measures, local-field and absolute-value normalization,
the pairing/quotient construction of item 1, the coordinate/Fourier
conditions, Iwasawa compatibility of item 4 and radical transport remain
requirements of a later full measure system. The formulas allow rank one
using the empty coordinate product and GL_0; this is the natural algebraic
interpretation of the formulas, not a new analytic existence result.
