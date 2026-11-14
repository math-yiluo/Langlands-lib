# Depth-zero regression: the unramified quadratic norm-one torus

This module supplies concrete data for
`Langlands.BruhatTits.IntegralModels.NormOneTorusDepthZero`. That module
takes a finite free `𝒪[F]`-algebra `B` with its generic and special fibres
and a smoothness hypothesis `hB` as inputs. Here they are constructed for
every nonarchimedean local field `F`, for one quadratic extension.

Let `f = X ^ 2 + b X + c` be monic over `𝒪[F]`, with unit discriminant
`b ^ 2 - 4 c` and reduction irreducible over `𝓀[F]`. The module takes:

- `B = 𝒪[F][X] / (f)`, which is finite free over `𝒪[F]`;
- `E = F[X] / (f)`, a separable quadratic field extension of `F`, with
  `F ⊗[𝒪[F]] B ≃ₐ[F] E`;
- `k' = 𝓀[F][X] / (f̄)`, a field of degree `2` over `𝓀[F]`, with
  `𝓀[F] ⊗[𝒪[F]] B ≃ₐ[𝓀[F]] k'`.

The norm-one kernel of `B` is smooth over `𝒪[F]`. The proof uses the base
change along `𝒪[F] → B`: in `B`, `f` has the roots `α` (the class of `X`)
and `-b - α`. Their difference squares to the discriminant, so it is a unit,
and the Chinese remainder theorem gives `B ⊗[𝒪[F]] B ≃ B × B`. The published
`normOne_smooth_of_decomposition` then applies, since `B` is faithfully flat
over `𝒪[F]`.

Such `b` and `c` exist for every `F`. Lift the coefficients of an
irreducible monic quadratic over the finite field `𝓀[F]`. Over a finite field
an irreducible monic quadratic has nonzero discriminant, so the lifted
discriminant is a unit.

The headline result is `exists_unramifiedQuadraticNormOne`. For every
nonarchimedean local field `F` there are such data for which:

- the generic torus `R¹_{E/F} G_m` is anisotropic;
- the norm-one model is smooth;
- the identity quotient is a reductive quotient;
- the index of `G(F)^{0+}` in `G^0(𝒪)` is `q + 1`, with `q = Nat.card 𝓀[F]`.

The name "unramified" describes the mathematics: such an `f` presents the
unramified quadratic extension of `F`. The Lean statements do not define or
use ramification; they work with the quotient rings directly.

## Provenance

The module is derived. It gives a concrete instance of the published
norm-one depth-zero results. The finite-field facts and the splitting are
standard algebra, proved here from Mathlib.

The task objective (Task 3557, section "Regression examples") asks for a
proved example of an anisotropic group. `NormOneTorusDepthZero` gives that
example only for supplied data. This module makes it unconditional.

The comparison values come from Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023). The registered original is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The authors' corrections of 1 November 2024 are
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.

- Remark 2.5.15 is replaced by the corrections (Section 2.5, PDF pp. 24–25).
  The corrected remark treats the kernel `T` of the norm map
  `R_{ℓ/k} G_m → G_m` for a separable quadratic extension `ℓ / k`. It
  identifies `T(k)_0 = T(k)` when `ℓ / k` is unramified. This is the case
  modelled here, with `ℓ = E`.
- 13.2.6 (printed p. 470 / PDF p. 501) identifies `P_{x,0} / P_{x,0+}` with
  the `f`-points of the maximal reductive quotient of the special fibre. For
  the unramified quadratic norm-one torus that quotient is
  `R¹_{f'/f} G_m`, with `q + 1` points over `f`.

The corrections do not amend 13.2.6: in Chapter 13 (PDF p. 49) they amend
only 13.5.2, 13.6.2 and 13.8.5.

KP's objects are not used in the Lean statements. The module computes the
Library's `integralPoints`, `positivePoints` and the index for the
constructed data. The KP values above are what these results are compared
against.

## Setting

The file imports the norm-one module
`Langlands.BruhatTits.IntegralModels.NormOneTorusDepthZero`. It also imports
the published `Langlands.CommutativeAlgebra.FiniteSeparableLiftedPolynomialModel`,
for `adjoinRootBaseChangeEquiv` (base change of `AdjoinRoot`).

`F` is a field in universe `u` with `ValuativeRel F`, `TopologicalSpace F`
and `IsNonarchimedeanLocalField F`. `𝒪[F]` is its valuation ring and `𝓀[F]`
its residue field.

The file opens `CategoryTheory.MonObj` (scoped). That provides the group
structure on `rationalPoints` used in the index statements.

## Declarations

All declarations are in namespace `Langlands.BruhatTits.IntegralModels`.

### Monic quadratics over a commutative ring `R`

- `monicQuadratic b c : R[X]` (definition): `X ^ 2 + C b * X + C c`.
- `monicQuadratic_monic`, `natDegree_monicQuadratic` (`[Nontrivial R]`:
  degree `2`), `map_monicQuadratic` (map along a ring hom is
  `monicQuadratic (f b) (f c)`), `eval_monicQuadratic`,
  `derivative_monicQuadratic` (`2 * X + C b`).
- `monicQuadratic_separable`: if `b ^ 2 - 4 * c` is a unit, the polynomial
  is separable. The proof gives the Bézout identity explicitly:
  `(-4 u⁻¹) f + u⁻¹ f' · f' = 1` for `u = b ^ 2 - 4 c`.
- `adjoinRootMonicQuadraticSplit b c α hα h` (definition): if `α` is a root
  and the discriminant is a unit, then
  `AdjoinRoot (monicQuadratic b c) ≃ₐ[R] (Fin 2 → R)`. The proof factors the
  polynomial as `(X - α) (X - (-b - α))` and applies Mathlib's Chinese
  remainder theorem (`Ideal.quotientInfRingEquivPiQuotient`). The factors are
  coprime because `α - (-b - α)` squares to the discriminant.

### Monic quadratics over a finite field `K`

- `exists_eval_monicQuadratic_eq_zero_of_disc_eq_zero`: if
  `b ^ 2 - 4 * c = 0`, the polynomial has a root. In characteristic `2`,
  `b = 0` and `c` is a square (`FiniteField.isSquare_of_char_two`), and its
  square root is a root. Otherwise Mathlib's `exists_quadratic_eq_zero`
  gives the root `-b / 2`.
- `disc_ne_zero_of_irreducible_monicQuadratic`: an irreducible monic
  quadratic has nonzero discriminant, because an irreducible polynomial with
  a root has degree `1`.
- `exists_irreducible_monicQuadratic K`: some `monicQuadratic b c` is
  irreducible over `K`. It is the minimal polynomial of a primitive element
  of Mathlib's degree-2 extension `FiniteField.Extension K (ringChar K) 2`.

### The unramified quadratic data

- `UnramifiedQuadraticData F` (structure): fields `b c : 𝒪[F]`,
  `isUnit_disc : IsUnit (b ^ 2 - 4 * c)` and
  `irreducible_residue : Irreducible ((monicQuadratic b c).map (algebraMap 𝒪[F] 𝓀[F]))`.

For `D : UnramifiedQuadraticData F`:

- `D.polynomial`, `D.Carrier = AdjoinRoot D.polynomial` (the algebra `B`),
  `D.GenericField` (`E`) and `D.ResidueField` (`k'`) (abbreviations), with
  instances `Module.Finite 𝒪[F] D.Carrier`, `Module.Free 𝒪[F] D.Carrier`,
  `Nontrivial D.Carrier`, `FiniteDimensional F D.GenericField` and
  `Algebra.IsSeparable F D.GenericField`.
- `irreducible_generic`: the polynomial is irreducible over `F`. The proof
  uses Mathlib's `Monic.irreducible_of_irreducible_map` with
  `algebraMap 𝒪[F] 𝓀[F]`,
  then Gauss's lemma (`Monic.irreducible_iff_irreducible_map_fraction_map`).
  The two `Fact (Irreducible ...)` instances make `E` and `k'` fields.
- `genericEquiv : F ⊗[𝒪[F]] D.Carrier ≃ₐ[F] D.GenericField` and
  `residueEquiv : 𝓀[F] ⊗[𝒪[F]] D.Carrier ≃ₐ[𝓀[F]] D.ResidueField`
  (abbreviations), both the published `adjoinRootBaseChangeEquiv`.
- `finrank_residueField`: `Module.finrank 𝓀[F] D.ResidueField = 2`.
- `smooth`: `Smooth (normOne (CommRingCat.of 𝒪[F]) D.Carrier).X.hom`.
  It applies the published `normOne_smooth_of_decomposition` with
  `A' = D.Carrier` and index `ULift (Fin 2)`. The splitting combines
  `adjoinRootBaseChangeEquiv`, `adjoinRootMonicQuadraticSplit` at the root
  `AdjoinRoot.root D.polynomial`, and reindexing by `ULift`.
- `modelData` (definition): the published `normOneModelData` for these data,
  a `RelativeComponentModelData 𝒪[F] F (normOne (CommRingCat.of F) D.GenericField)`.
- `quotientData` (definition): the published `normOneQuotientData`, which is
  the identity quotient.
- `quotientData_isReductiveQuotient`: it is a reductive quotient (published
  `normOneQuotientData_isReductiveQuotient`).
- `isAnisotropic`: `IsAnisotropic (normOne (CommRingCat.of F) D.GenericField)`
  (published `normOne_isAnisotropic`).
- `index_positivePoints_subgroupOf`: the index of
  `D.quotientData.positivePoints.subgroupOf D.modelData.neutral.integralPoints`
  is `Nat.card 𝓀[F] + 1`. It applies the published
  `normOne_index_positivePoints_subgroupOf_of_finrank_eq_two` with
  `finrank_residueField`.
- `UnramifiedQuadraticData.nonempty F`: `Nonempty (UnramifiedQuadraticData F)`.

### Summary

- `exists_unramifiedQuadraticNormOne`: there is
  `D : UnramifiedQuadraticData F` with
  `IsAnisotropic (normOne (CommRingCat.of F) D.GenericField)`,
  `D.modelData.neutral.IsSmooth`, `D.quotientData.IsReductiveQuotient` and
  index `Nat.card 𝓀[F] + 1`.

## Scope

- Only the quadratic case is treated. Unramified norm-one tori of higher
  degree still need supplied data in `NormOneTorusDepthZero`.
- `D.Carrier` is not shown to be the ring of integers of `E`, and `E / F` is
  not shown to be unramified in any Library sense. Nothing identifies the
  model with the Néron model or a Bruhat–Tits parahoric group scheme.
- `G^0(𝒪)` is not computed. In particular, `T(k)_0 = T(k)` from corrected
  Remark 2.5.15 is not proved.
- No building and no point `x` appear. `G^0(𝒪)` and `G(F)^{0+}` are not
  identified with KP's `P_{x,0}` and `P_{x,0+}`. The agreement with the KP
  value `q + 1` is only a comparison of numbers.
- Ramified quadratic norm-one tori are not treated.
