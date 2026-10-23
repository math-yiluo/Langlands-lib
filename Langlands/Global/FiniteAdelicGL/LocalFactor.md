# Finite local factors of adelic general linear groups

For a number field `K`, natural rank `n` (including zero), and finite place `v`,
`FiniteLocalGL K n v` is the matrix unit group over the actual adic completion.
`localProjection` evaluates every entry of an adelic matrix and its inverse at
`v`. `localInclusion` inserts a local matrix and its inverse at `v`, using identity
matrices at every other finite place.

The private `singleMatrix` uses `Pi.mulSingle` on the family of matrix rings,
so its values away from `v` are identity matrices, including zero off-diagonal
entries. It is a multiplicative map; no additive map of rings is asserted.
Each entry defines an actual finite adele because the identity matrix is integral
outside the singleton `{v}`. Matrix multiplication is checked by applying the
entrywise evaluation ring homomorphisms at every finite place. Continuity of
insertion is proved by factoring each entry through the restricted-product stage
integral outside `{v}`. Passing to units tracks both forward and inverse matrices
with the actual units topology. Projection is continuous by continuity of
restricted-product evaluation and its induced general-linear-group map.

Inclusion followed by projection is the identity on the local group; projections
at other places are trivial. Consequently inclusion is injective and projection
is surjective. The continuous retraction also proves that inclusion is a closed
embedding, using the Hausdorff topology of the actual finite adele ring. Local
projections jointly distinguish finite adelic matrices. Applying those
projections proves that the images of inclusions at distinct places commute.

`localIntegral` is the actual open subgroup whose matrix and inverse matrix
both have entries in the local valuation ring. Its compactness follows from the
published compactness of the completed integer ring and the generic compactness
theorem for integral matrix subgroups. `mem_standardIntegral_iff_local`
identifies the existing standard integral finite adelic subgroup with the
condition that every local projection lies in its local integral subgroup.
`localInclusion_mem_standardIntegral` and
`comap_standardIntegral_localInclusion` show that its preimage under one local
inclusion is exactly `localIntegral`.

These are internal constructions from the published `Adelic`, `AdelicGL`,
`IntegralFiniteAdeles`, `StandardIntegralStatement`, and `IntegralSubgroup`
models and Mathlib's restricted products, matrix units, and topology. No new
literature theorem or supplied arithmetic map is used. The module does not yet
identify the entire finite adelic matrix group with a restricted product of local
matrix groups, and does not construct a local component of a representation.
