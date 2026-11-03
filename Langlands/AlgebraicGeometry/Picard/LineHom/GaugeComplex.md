# The gauge complex of two families of transition functions

Helper module for the proof of
`Picard.ProperLineBundleHomRepresentabilityStatement`.

Setting: a commutative ring `R`, a scheme `Y` with a morphism
`p : Y ⟶ Spec R`, and an ordered affine cover `𝒰` of `Y`
(`Scheme.OrderedAffineCover`, from the ported FLT Čech definitions).

- `GaugeC0 p 𝒰` is the type of families `b i ∈ Γ(Y, 𝒰.U i)` indexed by the
  opens of the cover; `GaugeC1 p 𝒰` is the type of families
  `c t ∈ Γ(Y, 𝒰.U (t 0) ⊓ 𝒰.U (t 1))` indexed by the strictly increasing
  pairs `t : 𝒰.Idx 1`. Both are abelian groups pointwise and `R`-modules
  pointwise through the algebra structures
  `Scheme.TwoAffineOpenCover.algebraOfHom p` on sections.
- `scalarOn p r` is the image of `r : R` in `Γ(Y, W)` under `p`;
  `res_scalarOn` says it is compatible with restriction, and
  `GaugeC0.smul_apply`, `GaugeC1.smul_apply` say that scalar multiplication is
  multiplication by `scalarOn p r` in each coordinate (the `add_apply`
  lemmas say addition is pointwise).
- `gaugeD p α β`, for families `α`, `β` of units on the pairwise
  intersections `𝒰.U i ⊓ 𝒰.U j`, is the `R`-linear map `GaugeC0 → GaugeC1`
  sending `b` to the family
  `b (t 0)| * α (t 0) (t 1) - β (t 0) (t 1) * b (t 1)|`, where `|` restricts
  to the intersection; `gaugeD_apply` records this formula.

So the kernel of `gaugeD p α β` consists of the families `b` with
`b i| * α i j = β i j * b j|` for the pairs `i < j`, which is the relation
of the Library notion `IsGaugeFamily α β` restricted to increasing pairs.

Proofs as implemented: additivity of `gaugeD` follows from additivity of
restriction and `ring`; `R`-linearity from multiplicativity of restriction,
`res_scalarOn` and `ring`. `res_scalarOn` is `Scheme.Hom.appLE_map`.

This is the usual coordinate form of the Čech differential computing
morphisms between two line bundles given by transition functions; it is an
internal construction of this proof.
