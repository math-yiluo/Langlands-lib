# Extending the normalized Harris determinant to the full rational algebra

Author: Worker 344.

This internal derived construction extends the existing normalized Harris–Taylor
order-family determinant test to families in the full rational algebra and proves
that the two global conditions are equivalent. The comparison uses the same
abelian scheme, rational algebra action, finite Lie chart, smaller open, and full
structure-sheaf section ring. The normalized coefficient map remains the
explicitly conjugated `harrisTaylorReflexToCM`.

The provenance is internal. The definitions and proofs are derived from
`HarrisTaylorCMLieDeterminant`, `HarrisIntegralOrder`, the actual rational Lie
action and section determinant, and the actual regular Hodge and descended
reflex determinants already in the Library. This module does not assert a new
external representability or comparison theorem. The arithmetic trace in its
last theorem is the existing `HarrisTaylor.lieTraceSection`, with the original
source and normalization documented in
[HarrisTaylorCMLieDeterminant.md](HarrisTaylorCMLieDeterminant.md) and
[HarrisDeterminantCentralTrace.md](HarrisDeterminantCentralTrace.md).

## Parameters and the full-algebra condition

The normalized part retains the universe-zero hypotheses of the imported
construction: a totally real number field `E`, a totally complex quadratic
extension `F/E`, the actual central simple unitary datum `D` of degree `n` on
`A`, its compatible rational, `E`, and `F` algebra structures and scalar towers,
an imaginary quadratic CM number field `L` with an algebra structure on `F`,
an embedding `τ₀ : L →+* ℂ`, and Harris signature charts for precisely
`harrisCMSection E (algebraMap L F) τ₀`. It also fixes an actual scheme
`S`, a morphism `p : S ⟶ Spec F`, an abelian scheme `B/S`, and an actual
rational action `i : A →ₐ[ℚ] End0 B`.

`HarrisTaylorCMFullAlgebraLieDeterminantConditionAt` takes any finite family
`a : ι → A`, a finite free Lie chart `e` on an actual open `U`, and an actual
smaller open `V : Over U`. It equates

```text
lieRationalSectionDeterminant p B i.toRingHom e a V
```

with the actual reflex polynomial for `a`, mapped first through
`harrisTaylorReflexToCM C` into `F` and then through `secHom p V.left`
into `Γ(S, V.left)`. Thus it uses the full rational action without an order
membership hypothesis on the family.

The `_order` theorem identifies its restriction to an order-valued family with
the existing `HarrisTaylorCMRationalLieDeterminantConditionAt`. The equality is
definitional: `harrisRationalOrderAction` is the restriction of the same `i`,
and the coefficient polynomial and both coefficient maps agree.

## Rescaling and denominator clearing

The generic helper `HodgeDeterminant.rescaleVariables r` is the ring
endomorphism of multivariate polynomials that fixes coefficients and sends
`X k` to `C (r k) * X k`. `map_rescaleVariables` proves that it commutes with
an arbitrary homomorphism of commutative coefficient rings, after mapping the
scalars `r`. `rescaleVariables_injective` proves injectivity whenever every
`r k` is a unit. Its proof chooses the inverse units, checks the composite
substitution on coefficients and variables, and applies that left inverse to
an equality. This proof includes the zero ring.

`polynomial_smul_family` proves that scaling each endomorphism by `r k`
has exactly this effect on the determinant polynomial. The proof moves the
ring homomorphism through the determinant and checks the universal matrix
entry by entry. `polynomial_zsmul_family` specializes to integer scalars.
`lieRationalSectionDeterminant_zsmul_family` applies this identity to the
actual rational action on Lie sections, using the finite section basis from
the same chart and additivity of the action.

`kottwitzHodgeDeterminant_zsmul_family` proves the corresponding identity
for the actual regular Hodge module, by unfolding its tensor inclusions and
left action and applying the same polynomial identity.
`kottwitzReflexDeterminant_zsmul_family` descends it using the injective
inclusion of the actual reflex field into `ℂ` and the existing theorem
identifying the included reflex polynomial with the Hodge determinant.
`kottwitzReflexDeterminantBaseChange_zsmul_family` then maps it through any
homomorphism to a commutative coefficient ring.

At a fixed `e` and `V`,
`harrisTaylorCMFullAlgebraLieDeterminantConditionAt_iff_order_families`
proves

```text
(every ι-indexed family in A satisfies the full-algebra test)
  ↔
(every ι-indexed family in the Harris order satisfies the existing test).
```

The forward direction restricts the families. For the reverse direction,
`exists_int_multiple_mem_harrisHodgePELIntegralOrder` supplies, for every
`a k`, a nonzero integer `m k` with `m k • a k` in the constructed order.
Apply the assumed order-family identity to this scaled family. The preceding
rescaling laws turn both sides into the same diagonal substitution applied
to the desired unscaled polynomials. Each `m k` is nonzero, hence a unit,
in the number field `F`. Mapping that unit through `secHom p V.left`
proves it is a unit in the actual section ring. Cancellation by
`rescaleVariables_injective` gives the unscaled identity.

Only the reflex-field inclusion used in descent must be injective. No
injectivity is required of the section scalar map, and there is no
nonemptiness, reducedness, flatness, or characteristic-zero hypothesis on
the section ring. Empty families, rank-zero charts, empty opens, and rings
with nilpotents remain within the displayed statements.

## Compatibility and global equivalence

The `_iff_coeff` theorem expresses the local condition as equality of
every multivariate coefficient in the actual section ring, using polynomial
extensionality. The `_restrict` theorem maps the determinant equality along
the actual restriction map and uses `secHom_map` for the prescribed
coefficients.

`HarrisTaylorCMFullAlgebraLieDeterminantCondition` requires the local
condition for every finite full-algebra family, every actual finite free
Lie chart, and every smaller open. Its `_iff` theorem proves equivalence
with the existing normalized order-family global condition. The reverse
direction fixes a chart and smaller open, obtains all order-family tests
there from the global assumption, and applies the fixed-chart equivalence.
Its `_iff_reflex` theorem composes this result with the existing comparison
to `HarrisRationalLieDeterminantCondition` at
`harrisTaylorReflexStructure C p`.

The `_iso` theorem transfers the existing global invariance under an actual
equivariant rational isomorphism of abelian schemes. It assumes the displayed
intertwining identity for every element of `A`; the equivalence with the
order-family condition supplies invariance on every target chart.

Finally, `_At_centralCoefficient` additionally assumes `[IsCMField F]`.
For every `a : F`, the full-algebra local test on
`![1, algebraMap F A a]` implies that the extracted linear coefficient of
the actual Lie determinant is exactly
`HarrisTaylor.lieTraceSection L p n a V.left`. The proof rewrites by the
local determinant identity and applies the existing
`traceCoefficient_harrisTaylorCentralDeterminant_section`. No order
representative of the central element is needed.

This contribution establishes a comparison of determinant conditions and its
coefficient consequence. It supplies no satisfying abelian scheme, geometric
dimension condition, equivalence with the full Lie-plus condition, moduli
scheme, admissibility proof, smoothness, projectivity, or natural
representability isomorphism. The exact published
`DivisionCMRepresentabilityStatement` and its imported pairs are preserved.
