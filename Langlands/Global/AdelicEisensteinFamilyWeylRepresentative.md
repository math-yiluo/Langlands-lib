# The family comparison under a change of Weyl representative

Module `Langlands.Global.AdelicEisensteinFamilyWeylRepresentative` proves two results.

## Statements

- `IsIwasawaCompact.intertwiningOperator_eq_of_weylParameter_eq` (in namespace
  `Langlands.Global.AdelicGroupPoints`): let `G` be connected reductive, `p` parabolic with
  rational Levi `l` and geometric unipotent radical `iU`, `l' ≫ π' = 𝟙`, and let `(w₁, c₁)` and
  `(w₂, c₂)` be Weyl conjugations from `P` to `Q` with equal parameter maps
  `weylParameter l c₁ π' = weylParameter l c₂ π'`. Then for every `φ` invariant under
  `U(𝔸) M(F)`, every `λ` and `g`,
  `M(w₁, λ)φ (g) = M(w₂, λ)φ (g)`
  (`IsIwasawaCompact.intertwiningOperator` with `c₁` and `c₂`).
- `FamilyRegularComparison.of_weylRepresentative`: let `G` be connected reductive, `iU` a
  geometric unipotent radical, `l' ≫ π' = 𝟙`, and `(w₁, c₁)`, `(w₂, c₂)` Weyl conjugations from
  `P` to `Q` with equal parameter maps. Then the family comparison (module
  `Langlands.Global.AdelicEisensteinFamilyRegularComparison`) for `(w₂, c₂)` implies the family
  comparison for `(w₁, c₁)`. That `p` is parabolic and `l` a rational Levi subgroup is not a
  separate hypothesis: it comes from the compatibility field of the root presentation `r`
  (`r.isCompatible.parabolic`, `r.isCompatible.levi`).

## Proofs

For the operators: `IsWeylConjugation.exists_levi_of_weylParameter_eq` (module
`Langlands.Global.AdelicIntertwiningRepresentativeProof`) gives a rational point `y` of `M`
with `w₂ = w₁ · l(y)`. The intertwining operator is the intertwining integral twisted at
`weylParameter`; the parameter maps agree, and the intertwining integral for `w₁ · l(y)` equals
that for `w₁` by left invariance of `φ` under the rational points of the Levi
(`IsIwasawaCompact.intertwiningIntegral_mul_rational_parabolic`, same module).

For the family comparison: the intertwining hypothesis for `(w₁, c₁)` becomes the one for
`(w₂, c₂)` by the operator identity, applied to each `φ x` (invariant by automorphy). The
conclusions agree because the transported parameters `weylParameter l c₁ π' λ` and
`weylParameter l c₂ π' λ` are equal.

## Source

Provenance: derived. J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), §2, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, take Weyl elements as elements of
`W(P, Q)`. In the Library a Weyl element is presented by a rational point and a Levi map; this
module shows that the comparison depends only on the element presented.
