# Haar scaling on a rational dynamic unipotent subgroup

Author: Worker 184.

This internal assembly proves the unchanged published proposition
`Langlands.Aubert.General.RationalPointFamily.DynamicUnipotentHaarDeterminantStatement`
as `dynamicUnipotentHaarDeterminant`, without additional theorem parameters.
It retains arbitrary nonarchimedean local fields, including positive characteristic,
arbitrary connected reductive groups, arbitrary cocharacters, the canonical evaluation
topology and all displayed topology, representability and coordinate premises.

The proof obtains the finite rational vector filtration from the published
`dynamicUnipotentVectorFiltration`. Every element of the actual dynamic unipotent
point subgroup lies in a compact open subgroup: apply the published
`BruhatTits.dynamicUnipotentCompactOpenContainment` to its singleton. The published
`HaarModulus.VectorFiltration.vectorFiltrationHaarModulus` then expresses the
forward conjugation modulus as the product of the Haar scaling factors of the
graded determinants. Multiplicativity of `MeasureTheory.distribHaarChar k`
identifies this product with its value at the product of those determinants.
The filtration theorem identifies that product, in `kˣ`, with evaluation of the
actual centralizer adjoint determinant character in the supplied Lie coordinates.

Both sides use forward conjugation `u ↦ m u m⁻¹`; no inverse modulus is inserted.
The empty filtration and zero-dimensional graded quotients are covered by the
two existing filtration theorems.

This is a declaration-level assembly of published results. Its direct mathematical
dependencies are the three theorems named above and monoid-homomorphism
multiplicativity. The filtration proof supplies the actual algebraic coordinates,
Lie determinant and topology comparisons; the analytic filtration proof supplies
normal-subgroup Haar disintegration, vector-space determinant change of variables
and compact-open-cover unimodularity. No geometric lemma, adjointness, cuspidal
support, character independence or Langlands classification theorem is used by
this assembly. Representation constructions in imported-module closure do not
provide premises for its proof. The original provenance and conventions of the
unchanged target and the two filtration theorems remain in their paired Markdown.

This prerequisite alone does not prove opposite-radical reciprocity, the
common-Levi squared-modulus comparison, or the rational geometric exact-K0 expansion.
