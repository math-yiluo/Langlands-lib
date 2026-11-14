# Quaternionic symplectic models from rank-one type-C indices: proof

Author: Worker 178.

`Langlands.GroupScheme.typeCRankOneQuaternionic.{u}` proves the unchanged
published proposition `Langlands.GroupScheme.TypeCRankOneQuaternionicStatement.{u}`
with no additional premise.

For every field `K : Type u`, affine locally finite type group scheme `G`
over `Spec K`, actual `d : TitsIndexData G` and natural number `n`, assume
that `G` is simply connected and absolutely almost simple,
`d.HasRankOneCIndex n`, and `splitRank G = 1`. The theorem supplies a central
finite-dimensional division algebra `D : Type u` of dimension 4, a first-kind
involution `σ` whose symmetric subspace has dimension 3, a witness `NeZero n`,
and an invertible trace-valued antihermitian matrix `H` of size `n` with
`σ.wittIndex H = 1` and `Nonempty (G ≅ σ.symplecticGroup H)`.
The isomorphism is of actual group schemes. Every characteristic, including
two, and every universe `u` are retained.

The implemented proof applies the published theorem
`typeCRankOneQuaternionic_of_typeCDivisionForm` from
`SimplyConnected.TypeCRankOneQuaternionicReduction` to the published proof
`typeCDivisionForm` from `SimplyConnected.TypeCDivisionFormProof`.
The latter proves `TypeCDivisionFormStatement.{u}` without an extra
hypothesis, so it discharges the reduction's classification premise.

The arithmetic extraction is implemented in the imported reduction: the
vertex numbered 2 is distinguished, so the general index formula writes
`2 = j * degree` with `1 ≤ j ≤ splitRank G = 1`. Thus `j = 1` and
`degree = 2`. The general size identity then gives `m = n`, and the dimension
identities specialize to 4 and 3. The same involution, trace-valued form and
scheme isomorphism provide the required witnesses, and the Witt-index
identity specializes to one.

This proof is an internal composition of these two published results; their
paired Markdown explains their respective proofs and provenance. It uses
no local-field assumption, downstream local classification, or Kneser–Tits
result.
