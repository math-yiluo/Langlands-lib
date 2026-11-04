# Explicit local Haar normalization on a complementary subgroup

This internal construction extends the complementary-subgroup measure
comparison in `QuotientFactorizationHaar`. Its application is the actual
quotient and ordered unipotent integration in Waldspurger (2003), IV.1,
printed p.279 (PDF p.45), and the composition assertion IV.1(12),
printed p.283 (PDF p.49). It does not assert their general reductive
geometric realization.

Let `H` and `K` be subgroups of a topological group `G`. For an ambient
open subgroup `S`, an open subgroup `B` of `K`, and measures `μG`, `μH`,
`μK`, the definition `compactOpenFactorScalar` is

`(μG S).toNNReal / ((μH {h : H | h.val ∈ S}).toNNReal * (μK B).toNNReal)`.

The definition `compactOpenFactorMeasure` scales `μK` by this scalar.
It uses only the three measures and the compact-open subgroup choices.
In particular, a quotient measure or full ambient product identity is
not an input to this definition.

Assume `G` is Hausdorff, `H` is closed, `S` and `B` are compact, and
the three measures are Haar. The intersection `H ∩ S` is compact and
open in `H`. All three masses are therefore finite and positive.
`compactOpenFactorScalar_pos` proves positivity of the displayed
nonnegative real scalar. `compactOpenFactorMeasure_mass` proves

`μG S = μH(H ∩ S) * compactOpenFactorMeasure B`.

The proof first cancels the denominator in nonnegative real numbers and
then restores extended nonnegative masses using finiteness. Thus the
local mass normalization is proved from the explicit definition.
The scaled measure is Haar and inherits regularity, right invariance
and S-finiteness from `μK`.

For the quotient comparison, assume additionally local compactness of
`G`, Borel structures on `G`, `H`, `K` and the actual left quotient,
regularity of the three Haar measures, right invariance on `H` and `K`,
and an actual compatible Weil measure `ν`. Supply a homeomorphism
`m : H × K ≃ₜ G` given by literal ordered multiplication and write
`c = factorQuotientHomeomorph H Subtype.val m hm`. The remaining local
geometric input is `c '' B = leftQuotientMap H '' S`.

`IsCompatible.measurePreserving_compactOpenFactorMeasure` applies the
compact-open comparison to the constructed measure and its proved
normalization. `IsCompatible.map_symm_eq_compactOpenFactorMeasure`
identifies this explicit measure with `Measure.map c.symm ν`.
No second-countability assumption is used.

The literal product coordinates, compatible measure and compact-open
orbit set identity remain application obligations. The construction
chooses the complement Haar normalization prescribed by the ambient
and intersection measures; comparison with a separately specified
source normalization still requires proof. Root-distance geometry,
analytic convergence, rational continuation and Plancherel remain open.
