# Conditional proof of scheme representability of separated commutative group spaces

`separatedAddCommGroupSheafSchemeRepresentability_of` proves
`SeparatedAddCommGroupSheafSchemeRepresentabilityStatement.{u}` from one hypothesis,
`FiniteLocallyFreeEquivalenceRelationAffineQuotientStatement.{u}` (Stacks 03BM). The other two
inputs of the dense affine open step are proved theorems: finite-set Stacks 03JE is
`finiteLocallyFreeEquivalenceRelationInvariantAffineOpen`
(`FiniteLocallyFreeEquivalenceRelationInvariantAffineOpenProof`), and the invariance of the
finite locus of an etale equivalence relation is `FiniteLocus.finiteLocus_invariant`. The module needs
neither the published dense affine open statement nor local-finite-type source descent: the
dense affine open input is proved here, in a form locally of finite type, by
`separatedDenseAffineOpenLFT_of`.

Proof:
1. Transport the sheaf property and the closed diagonal from `H` to `G ⋙ forget` along `e`,
   and use the atlas `a ≫ e.inv`.
2. For each closed point `x` of the atlas `U`, the residue field `κ(x)` is finite over `k`.
   `GroupLocalCharts.exists_open_chart_of_field_point` (with `separatedDenseAffineOpenLFT_of`)
   puts the canonical `κ(x)`-point in an open chart represented by an affine scheme locally of
   finite type.
3. Composing with `e.hom` gives charts of `H`.
4. `separated_lft_representableBy_of_closed_point_lft_charts` glues them into a separated
   scheme `P`, locally of finite type, representing `H`.
