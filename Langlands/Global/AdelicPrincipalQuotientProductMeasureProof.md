# The adelic principal quotient as a product measure space

Module `Langlands.Global.AdelicPrincipalQuotientProductMeasureProof` proves
`Langlands.Global.RestrictionSplitCentre.PrincipalQuotientProductMeasureStatement` (module
`Langlands.Global.AdelicPrincipalQuotientProductMeasureStatement`) from
`Langlands.Global.LeftCosetSpace.ProductQuotientMeasureStatement` (module
`Langlands.Global.LeftCosetProductMeasureStatement`), the product formula for discrete left
quotients, which it takes as a hypothesis (in universes `0, 0, 0`) and does not prove.

| Declaration | Kind | Content |
| --- | --- | --- |
| `principalQuotientProductMeasure_of_productQuotientMeasure` | theorem (proved) | `ProductQuotientMeasureStatement.{0, 0, 0} → PrincipalQuotientProductMeasureStatement` |

## Proof

The conclusion is that `principalQuotientProductEquiv F G hG : G(F) \ G(𝔸) ≃ A_G × [G]` carries
`rationalQuotientHaarMeasure F G` to `(positiveCentreHaarMeasure F G hG).prod (canonicalMeasure F G)`.

1. Apply the hypothesis to the multiplication isomorphism
   `intrinsicNormOneDecomposition F G hG : A₀ × G(𝔸)¹ ≃ G(𝔸)` (module
   `Langlands.Global.AdelicPrincipalQuotientProduct`), with `A₀` the intrinsic positive subgroup
   of the canonical torus, `H = rationalNormOneSubgroup F G` and `Γ = rationalSubgroup F G`.
   Its hypotheses are `intrinsicNormOneDecomposition_mem_principal` (a product lies in `G(F)`
   exactly when its first factor is `1` and its second lies in `G(F)`), the discreteness of both
   rational subgroups, and `measurePreserving_intrinsicNormOneDecomposition` (the product of
   `intrinsicCentreHaarMeasure` and Haar measure on `G(𝔸)¹` is carried to Haar measure on
   `G(𝔸)`). This gives `hquot`: the induced map `G(F) \ G(𝔸) → A₀ × G(F) \ G(𝔸)¹` carries the
   count-normalized quotient of Haar measure to the product of `intrinsicCentreHaarMeasure` and
   the count-normalized quotient of Haar measure on `G(𝔸)¹`.
2. `measurePreserving_positiveCentreEquiv` and
   `measurePreserving_canonicalNormOneQuotientHomeomorph` identify the two factors with
   `(A_G, positiveCentreHaarMeasure)` and `([G], canonicalMeasure)`; `MeasurePreserving.prod`
   gives `hprod`.
3. `hprod.comp hquot` is the statement, since `principalQuotientProductEquiv` is by definition
   this composite.

No finiteness of the volume of `[G]` is used.

## Sources

Getz–Hahn (2024) (`getz-hahn-2024-automorphic-representations`), §2.6, printed pp.68–69
(PDF pp.85–86): `G(𝔸)¹` (2.19), `A_G` (2.20), Lemma 2.6.2 (`A_G G(𝔸)¹ = G(𝔸)` and
`A_G ∩ G(𝔸)¹ = 1` for a number field), `[G]` (2.21) and the homeomorphism (2.22). The measures
are the fixed Haar measures and count-normalized quotient measures of the Library; the statement
imposes no other normalization.
