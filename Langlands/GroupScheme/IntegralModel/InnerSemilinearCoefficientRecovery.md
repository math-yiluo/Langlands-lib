# Recovery of inner-twisted semilinear maps from finite coefficients

This internal construction recovers a specified inner-twisted integral
isomorphism on a supplied coefficient model. It is derived from the Library's
actual pullback comparisons, rational-point coefficient extension, naturality of
inner conjugation, and descent of model isomorphisms from faithfully flat
coefficients. No original-literature assertion is made.

Let `k ⊆ L ⊆ M` be a compatible tower of fields, all in an arbitrary common
universe, and let `G` be a group scheme over `k`. The chosen equality `h`
identifies the composite spectrum map with the direct map. Let `σ` and `τ` be
`k`-automorphisms of `L` and `M` whose spectrum maps commute with inclusion, and
let `x` be an actual rational point of `baseChanged k L G`.

`pullbackComparison_baseChangeBasePoint_fst` computes the original-group
projection of the pulled-back point transported through the actual field-tower
comparison. `baseChangedPoint_ext` says that this projection determines a base
section of a pulled-back group scheme: the other pullback projection is already
fixed by the section condition. Comparing with `relativeRationalExtend_fst`
proves `pullbackComparison_baseChangeBasePoint`, identifying the transported
point with the actual relative rational extension of `x`. This argument needs
neither affineness nor a finite field extension.

`innerIso_hom_comp_rational` writes naturality of inner conjugation using the
named rational-point map. The proof is the existing naturality theorem after
the map's application formula. In `pullbackComparison_innerGaloisDescentIso`,
base change preserves inner conjugation, naturality moves it past the tower
comparison, and the preceding point identity identifies the resulting
conjugator. The remaining square is precisely
`Descent.pullbackComparison_semilinear`. Thus the tower comparison intertwines
the inner-twisted generic maps for `σ, x` and `τ, relativeRationalExtend x`.
Here each inner-twisted map is canonical Galois descent followed by inner
conjugation, as defined in `IntegralModel.InnerSemilinearExtension`.

For the integral construction, let `R` and `A` be domains with fraction fields
`L` and `M`, respectively. The ring and field algebras form compatible scalar
towers. Assume `Spec A → Spec R` is flat and surjective. Supply:

- an integral model `N` of the actual `L`-base change of `G`;
- an integral model `P` of the actual `M`-base change;
- an isomorphism from `N.baseChange A M` to `P` whose generic map is the exact
  field-tower comparison;
- integral base maps `a, a'` compatible with `σ, τ`, and with the coefficient
  inclusion;
- an actual isomorphism from the twist of `P` by `a', τ` back to `P`, with
  generic map the inner twist by `relativeRationalExtend x`.

`innerSemilinearIsoFromCoefficients` applies
`semilinearIsoFromCoefficients` to these data. The proved generic square
discharges its generic descent premise, so the result is an actual
isomorphism from the `a, σ` twist of `N` back to `N`, with generic map the
inner twist by `x`.

`baseChange_innerSemilinearIsoFromCoefficients` proves that pullback of this
integral isomorphism is the specified upstairs conjugate through coefficient
comparison and the supplied model recovery isomorphism.
`innerSemilinearIsoFromCoefficients_generic` records the exact generic
compatibility square, using the resulting model isomorphism's compatibility
field. Both follow from the Library's coefficient-descent recovery and twist
compatibility theorems.

This module does not construct the coefficient model, the upstairs model, their
recovery isomorphism, a finite field containing conjugators, or the upstairs
integral twist. It supplies the compatibility and recovery step once those
objects exist. In particular it does not prove the twisted-chamber
quotient statement this module serves, `UnramifiedTwistedChamberQuotientStatement`
(proved as `unramifiedTwistedChamberQuotient` in
`Langlands.Geometry.Building.UnramifiedTwistedChamberQuotientProof`), or its residue,
Frobenius and chamber conclusions.
