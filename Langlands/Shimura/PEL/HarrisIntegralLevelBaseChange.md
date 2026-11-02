# Fixed-isomorphism integral level comparison under Harris pullback

This internal result concerns the existing actual `levelDataBaseChange` on
positive polarized Harris representatives at an original Harris transporter
level. All tensor, Picard, dual geometry, finite-fibre, torsion and adelic
comparison inputs remain explicit. Both ordered-pair dual-additivity inputs
are supplied. The same positive auxiliary left involution and opposite-group
level conventions are those of the imported constructions.

`levelDataBaseChange_levelIso_iff` fixes an original rational action isomorphism
and rational unit multiplier. Given the existing geometric polarization equation
on both endpoints, its equation on geometrically fixed compatible right level
orbits holds before pointed base change if and only if it holds after base
change with the image of that same isomorphism and the same multiplier.
The proof applies the published actual Weil base-change/isogeny square.
Preservation follows by mapping the original orbit equation. Reflection uses
injectivity of the pointed level pullback, whose underlying orbit map is the
inverse frame-orbit equivalence. It requires no surjectivity statement about
the fundamental-group map.

`levelDataIntegralPolarizedMultiple_levelIso_baseChange_iff` applies that
criterion with the rational polarization equations recovered from the supplied
exact integral witnesses. The changed integral proposition is proved by the
existing supplied-data transport constructor; it uses the mapped original
isomorphism, original multiplier, unchanged integral denominators and unchanged
cross-multiple integers. The original rational action and its integral
restriction remain on the same actual abelian schemes, with the target the
actual pullback. No unrelated isomorphism or multiplier is selected.

`integralPolarizedLevelWitnessBaseChangeEquiv` constructs an equivalence
between two subtypes of original multiplier/isomorphism pairs. The first
requires original integral witnesses and the source orbit equation; the second
requires original integral witnesses and the target orbit equation for their
transport. The equivalence and its inverse act as the identity on the pair.
The proof applies the fixed-isomorphism criterion under the existential over
the proof of the integral multiple, then uses `Equiv.subtypeEquivRight`.
Thus the defined comparison retains the original multiplier and original
isomorphism as data on both sides, while its target equation uses their image.

The result reflects only the fixed-orbit equation under the displayed
fixed isomorphism and supplied polarization data. It does not reflect arbitrary
rational action isomorphisms, prove integral restriction existence, or identify
independently chosen geometric points. It constructs no representing scheme
and proves no admissibility or projectivity. Provenance is the internal
combination of the imported Weil naturality square, pointed level injectivity,
rational/integral polarization comparison and actual integral-data transport.
