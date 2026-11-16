# The Whittaker expansion of the vectors of a cuspidal realization

Module `Langlands.Global.RankinSelberg.WhittakerExpansionCore.ExpansionRealization`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`. This helper module applies the two halves of
the proof to an actual cuspidal operator realization. Half (S) is `WhittakerMajorantsStatement`,
proved in `WhittakerStep`. Half (E) is `hasSum_whittaker_of_levelPropsB`, proved in
`ExpansionInduction`. The module is internal to this proof. It checks that the cusp functions
`φ_v = cuspFunction F T v` satisfy the hypotheses of both halves, using only Library facts about
operator realizations.

Notation. `F` is a number field. `S : OperatorRealization F n` is an operator realization of
`GL_n`, and `T : CuspidalOperatorRealization F r` is an actual cuspidal realization of `GL_(r+1)`
with underlying realization `T.realization`. For a vector `w`, `evaluate F n (S.toContinuous w)`
is its function on the matrix group `AdelicGL F n = GL_n(𝔸)`. Write
`homeo = GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)` for the Library homeomorphism
from the group-scheme points `Points F (r + 1)` to `AdelicGL F (r + 1)`.

The file opens `Matrix.Norms.Operator` and sets `backward.isDefEq.respectTransparency false`. It
also declares local `AddCommGroup` instances (`Submodule.addCommGroup`) for the Library function
spaces it passes through, and for `S.Space` in the archimedean section. These are technical
elaboration settings and do not change any statement.

## Archimedean derivatives (section `Archimedean`, any `S`)

* `matrixGenerator F n Z` is the enveloping-algebra element of a real archimedean matrix `Z`:
  the Library `envelopingGenerator` of the complexification of the real Lie-algebra element
  `realLieAlgebraToMatrix.symm Z`. It is additive (`matrixGenerator_add`). It is real-homogeneous
  in the sense `matrixGenerator (c • Z) = (c : ℂ) • matrixGenerator Z` (`matrixGenerator_smul`).
* `mul_ofInfinite_eq`: `g · ofInfinite h = ofInfinite (g_∞ h) · ofFinite g_f`. This is right
  translation by an archimedean matrix, in product form.
* `hasDerivAt_smooth_squareZero`: let `f` be a smooth function on `GL_n(F_∞)` and let
  `Z * Z = 0`. Then the derivative of `t ↦ f(x (1 + t Z))` at `t = 0` is the Library
  left-invariant derivative `smoothDifferential` of `f` in the direction `Z`, evaluated at `x`.
  The curve `t ↦ x (1 + t Z)` is the matrix curve `p(t) = x (1 + t Z)` (the Library
  `squareZeroUnit`), with derivative `x Z`. The function is the Library
  `coordinateExtension` of `f` composed with `p`, and the coordinate extension is smooth
  (`coordinateExtension_contDiffAt`). The chain rule then gives
  `fderiv (coordinateExtension f) x (x Z)`, which is the Library formula
  `smoothDifferential_apply`.
* `smoothDifferential_slice`: the left-invariant derivative in direction `Z` of the archimedean
  slice `finiteSmoothSlice F n y (S.ambient w)` at `x` equals the value of
  `S.envelopingAction (matrixGenerator F n Z) w` at `ofInfinite x · ofFinite y`. This combines
  the Library facts `S.ambient_envelopingAction`, `finiteSmoothSlice_envelopingAction`,
  `ArchimedeanGL.envelopingAction_real_generator` and `S.finiteSmoothSlice_ambient_apply`.
* `hasDerivAt_evaluate_squareZero`: for `Z * Z = 0` and `g ∈ GL_n(𝔸)`, the derivative at
  `t = 0` of `t ↦ φ_w(g · ofInfinite(1 + t Z))` is `φ_(R_Z w)(g)`, where
  `R_Z w = S.envelopingAction (matrixGenerator F n Z) w`. The function of `t` is the slice at
  `g_f` evaluated along `g_∞ (1 + t Z)` (by `mul_ofInfinite_eq`). Apply
  `hasDerivAt_smooth_squareZero`, then `smoothDifferential_slice`.

## Finite level and bands (section `Archimedean`, any `S`)

* `exists_level_evaluate`: every realized vector `w` is right invariant under some open subgroup
  `L` of `GL_n(𝔸_f)`. This is the Library `S.exists_level` at the enveloping element `1`.
* `exists_band_bound` (with `𝔸_F/F` compact and `S` cuspidal): for `0 < lo`, the function
  `φ_w` is bounded on the band `lo ≤ |det g|_𝔸 ≤ hi`. The Library Siegel decomposition
  `exists_siegelDecomposition` writes `γ g = ofInfinite(torInf x) · q`, with `γ` rational, `q`
  in a fixed compact set `Q₁` and `x` in a chamber. Since `log |det|` is bounded on `Q₁` by some
  `L`, the Library inequality `abs_sum_le_of_absDet` gives
  `|Σ x_i| ≤ max(|log lo|, |log hi|) + L`. The Library chamber estimate `exists_chamber_decay`
  with decay rate `c = 0` then bounds `φ_w(ofInfinite(torInf x) q)` by a constant. Finally
  `φ_w(γ g) = φ_w(g)` (`evaluate_rational`).

## Cusp functions (section `Realization`)

Assume from here on that `𝔸_F/F` is compact.

* `cuspFunction_apply_eq`: `φ_v(x) = evaluate (T.realization.toContinuous v) (homeo x)`. This is
  the Library `evaluate_continuousGeneralLinearEquiv_at_point`.
* `adelicHomeomorph_finitePoint` and `adelicHomeomorph_archPoint`: `homeo` sends
  `finitePoint F n l` to `ofFinite l`, and `archPoint F n Z hZ` to `ofInfinite(1 + Z)`.
* `cuspLinear F T : v ↦ φ_v` is complex-linear. It is injective (`cuspLinear_injective`),
  because `homeo` is bijective and `T.realization.toContinuous` is injective (Library
  `toContinuous_injective`).
* `cuspSpace F T` is the range of `cuspLinear`. `cuspEquiv F T : T.Space ≃ cuspSpace F T` is the
  resulting linear equivalence (`LinearEquiv.ofInjective`). `coe_cuspEquiv` and
  `coe_eq_cuspFunction` say that the function of `f ∈ cuspSpace` is `φ_v` for
  `v = cuspEquiv.symm f`.
* `cuspDerivative F T Z` transports `R_Z = T.realization.envelopingAction (matrixGenerator Z)`
  to `cuspSpace` through `cuspEquiv`. It is real-linear in `Z` by `matrixGenerator_add` and
  `matrixGenerator_smul`. By `coe_cuspDerivative` (which holds by `rfl`), the function of
  `cuspDerivative F T Z f` is `φ_(R_Z v)` for `v = cuspEquiv.symm f`.

The five properties of a `WhittakerDecayClass` (module `Interface`) are proved first for `φ_v`
and then transferred to `cuspSpace` with `coe_eq_cuspFunction`:

* continuity: the Library `continuous_cuspFunction` (`cuspSpace_continuous`);
* left invariance under rational points: the Library `cuspFunction_rational_mul`
  (`cuspSpace_rational`);
* finite level: `cuspFunction_level`, from `exists_level_evaluate` and
  `homeo(x · finitePoint l) = homeo x · ofFinite l` (`cuspSpace_level`);
* boundedness on bands: `exists_bound_cuspFunction`, from `exists_band_bound` with the cuspidality
  `T.cuspidal` of `T`. The Library values `detNorm F (r + 1) x` and `absDet F (r + 1) (homeo x)`
  agree after unfolding the definitions, so Lean accepts the bound directly
  (`cuspSpace_bounded`);
* derivatives: `cuspFunction_deriv` says that `d/dt φ_v(x · archPoint(t Z))|_(t=0) = φ_(R_Z v)(x)`.
  It follows from `hasDerivAt_evaluate_squareZero` at `homeo x`, using
  `homeo(x · archPoint(t Z)) = homeo x · ofInfinite(1 + t Z)` (`cuspSpace_deriv`).

* `whittakerDecayClass_cuspSpace`: `(cuspSpace F T, cuspDerivative F T)` is a
  `WhittakerDecayClass`.

## The expansion (section `Expansion`)

* `cuspidalWhittakerExpansion : CuspidalWhittakerExpansion F T`. Fix a standard character `ψ`,
  a vector `v` and `g`.
  - Half (S): `whittakerMajorantsStatement_proof`, applied to the decay class
    `whittakerDecayClass_cuspSpace` and to `cuspEquiv v`, gives `HasWhittakerMajorants F r ψ φ_v`.
    For every `k ≤ r` and `x`, take the compact set `{x}`. The majorant `b` is summable and
    dominates `q ↦ ‖W_(φ_v)(diag(q.out, I) x)‖`, so this family is summable (`hsum`).
  - Cuspidality at the top level (`htop`): the Library `levelProps_top`, applied to
    `T.realization.toContinuous v` with the vanishing constant terms
    `T.realization.constantTerm_eq_zero T.cuspidal`, gives the Library `LevelProps r` of `φ̃_v`,
    the function of `v` on the matrix group. `LevelProps.levelPropsB` (module `ColumnsB`) turns it
    into `LevelPropsB r`. Also `φ_v ∘ homeo.symm = φ̃_v`, by `cuspFunction_apply_eq`.
  - Absolute summability: `cuspWhittaker F T ψ v` is by definition the Whittaker function
    `whittaker F r ψ φ_v`, and `padRational F _ q.out = cornerAdelicPoint F r q.out` (Library
    `padRational_eq_cornerAdelicPoint`). So the first clause is `hsum` at `k = r`.
  - The sum: `hasSum_whittaker_of_levelPropsB` with continuity (`continuous_cuspFunction`),
    rational invariance (`cuspFunction_rational_mul`), `htop` and `hsum` gives
    `HasSum (q ↦ W(cornerAdelicPoint F r q.out * g)) (φ_v(g))`.
