# Compact-cell volume bounds for the compatible split-central quotient

This internal finite-coset argument supplies a volume ingredient for the
actual split-central quotient form of Waldspurger's Corollary VIII.3.2.
The source is *La formule de Plancherel pour les groupes p-adiques* (2003),
registered as `waldspurger-2003-plancherel`, printed pp.326–327 (PDF pp.92–93).
The proof on printed p.327 uses an inverse-modulus bound for cells represented
by `K a Γ K`. The finite-index bound for the same supplied compatible measure
is an internal derivation from the Library's quotient invariance and
double-coset API.

Let `G` be a locally compact Hausdorff topological group with its Borel
measurable structure, and let `A` be a closed central normal subgroup with its
Borel structure. Let `muG` be left invariant, `muA` a regular right-invariant
Haar measure, and `muQ` the supplied compatible measure on the left quotient
`LeftQuotient A`, with its displayed Borel structure. Write
`q = leftQuotientMap A`.

`IsCompatible.measure_image_quotientLeftTranslate` proves that images of
arbitrary sets under quotient left translations have the same `muQ` mass.
It uses the published
`IsCompatible.map_quotientLeftTranslate` and the measurable embedding of the
translation homeomorphism. `leftQuotientMap_image_smul` identifies the image
of a left translate in `G` with this quotient translate.

For any compact open subgroup `K` and `g : G`,
`IsCompatible.measure_image_doubleCoset_le` proves

`muQ (q '' (K g K)) ≤ doubleCosetIndex K g * muQ (q '' K)`.

Compact openness makes the original double-coset index finite. The published
finite left-coset decomposition of `K g K`, countable subadditivity and
quotient left invariance give the inequality for the supplied `muQ`.

For a compact subset `Y` of `G`,
`IsCompatible.exists_measure_compact_cell_le_index` proves that some positive
real `C`, independent of `g`, satisfies

`muQ (q '' (K * {g} * Y)) ≤ ENNReal.ofReal (C * doubleCosetIndex K g)`.

Cover `Y` by finitely many left `K` cosets `c K`. Each cell lies in the finite
union of double cosets `K (g c) K`. Submultiplicativity of the double-coset
index bounds its mass by `index(K,g)` times a finite sum of `index(K,c)`.
The identity compact-open orbit has finite mass by the published compatibility
mass theorem. The proof converts that finite mass to a real constant and adds
one to ensure positivity, also when the compact set is empty. The estimates
use outer measure and apply to arbitrary cells of the displayed form.

`RationalSplitCentralCellIndexBound s muQ K Y` records the last inequality
with a single positive real `C` for all `g ∈ G(F)`. It is a proposition for
a morphism `s : T.toGrp ⟶ G`, an open subgroup `K`, a set `Y`, and a measure
`muQ` on `LeftQuotient (rationalPoints.map s).range`.

`exists_rationalSplitCentralQuotient_measure_compact_cell_le_index` proves
this proposition when `s` is an actual split component over a nonarchimedean
local field in arbitrary universe `u` and `G` is affine and locally of finite
type. The theorem takes compactness of `K` and `Y`, the displayed Borel
structures, the supplied left-invariant `muG`, the supplied right-invariant
central Haar measure `muA`, and compatibility of the original `muQ`.
A split component is a central closed split-subtorus embedding. Its
rational-point image is closed by `isClosedEmbedding_rationalPointMap`,
so the subgroup is locally compact. The second-countability theorem for
affine rational points transfers to the subgroup, and the Borel locally finite
measure instances then give regularity of `muA`. The generic compact-cell
bound applies with these instances.
