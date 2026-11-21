# An ample line bundle on an abelian variety has a section nonzero at a rational point

Helper module for the core proof of
`Langlands.AbelianScheme.AlgClosedFieldAmpleCubeSeparationStatement`. Mumford's
proof of §17 (*Abelian Varieties*, printed pp.163–164) starts from an effective
divisor `D` with `L ≅ O(D)`, that is, from a nonzero section of `L`. This module
supplies that section in the Library's language and records that it is nonzero at a
rational point, which is the form used by the published triple-translate machinery
(`Langlands/AbelianScheme/SeparatingLineBundle/Assembly`).

Setting: `K` a field, `A : AbelianScheme (Spec K)`, `L` a line bundle on `A.X.left`.
From `eulerCharacteristic_tensorPow_sq` on, `K` is algebraically closed.

## Declarations

- `lineBundle_hasFiniteCohomology A L`: every line bundle on an abelian scheme over a
  field has finite cohomology (the case `k = 1` of the published
  `lineBundleTensorPow_hasFiniteCohomology`, transported along `tensorPow L 1 ≅ L`).
- `powLB A L k`: the tensor power `tensorPow L.obj k` packaged as a `LineBundle`.
- `eulerCharacteristic_tensorPow_sq`: for `A` of relative dimension `g`, `L` ample and
  `k ≥ 1`, `χ(L^k)^2 = k^(2g) · χ(L)^2`.
- `eulerCharacteristic_ne_zero_of_isAmple`: `χ(L) ≠ 0` for ample `L`.
- `exists_globalSection_ne_zero_of_isAmple`: an ample `L` has a nonzero global section.
- `exists_section_not_vanishesAlong_of_isAmple`: an ample `L` has a global section `s`
  and a rational point `x` (a section of the structure morphism) such that `s` does not
  vanish at `x`.

## Proofs

`eulerCharacteristic_tensorPow_sq`. With inverses `L⁻¹` and `(L^k)⁻¹`, the published
`algClosedFieldAmpleEulerInverseScaling` gives
`χ(L^k) · χ((L^k)⁻¹) = k^(2g) · χ(L) · χ(L⁻¹)`, and
`algClosedFieldEulerInverseSymmetry` gives `χ(M⁻¹) = (-1)^g χ(M)` for `M = L, L^k`.
Substituting and cancelling `(-1)^g` gives the identity.

`eulerCharacteristic_ne_zero_of_isAmple`. The published
`smoothProperLineBundleEulerPolynomial` gives a rational polynomial `P` with
`P(k) = χ(L^k)` for `k ≥ 1` whose leading coefficient is positive because `L` is
ample. If `χ(L) = 0`, the identity above forces `χ(L^k) = 0` for all `k ≥ 1`, so `P`
has infinitely many roots and is zero, contradicting the positive leading
coefficient.

`exists_globalSection_ne_zero_of_isAmple`. The higher cohomology of an ample bundle on
an abelian variety vanishes (`ampleLineBundleHigherCohomologyVanishing`), so
`eulerCharacteristicBasic` identifies `χ(L)` with `dim_K H⁰(L)`. This is positive, so
`H⁰(L)`, and through `relativeCohomologyZeroIso` the module of global sections, is
nontrivial.

`exists_section_not_vanishesAlong_of_isAmple`. A smooth scheme over a field is reduced
(`isReduced_of_smooth_over_field`). The underlying group scheme of `A` is smooth,
proper and geometrically connected over the algebraically closed field, so its scheme
is irreducible (`irreducibleSpace_of_smooth_of_isProper`). On such a scheme a nonzero section of a
line bundle has nonempty nonvanishing locus (`LineBundle.eq_zero_of_trivializationOpen_eq_bot`).
A nonempty open subset of a scheme locally of finite type over an algebraically closed
field contains a rational point (`exists_rationalPoint_mem_of_isOpen`), and
`vanishesAlong_field_iff` translates membership in the nonvanishing locus into
non-vanishing at that point.
