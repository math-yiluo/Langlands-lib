# Determinant windows on `GL_n(E)`

The module `Langlands.BaseChange.DeterminantWindow` defines the cut-off function
`determinantWindow` used to make matrix coefficients of supercuspidal representations
compactly supported, and proves that it is locally constant.

## Definition

Let `F` be a nonarchimedean local field (`[Field F] [TopologicalSpace F] [ValuativeRel F]
[IsNonarchimedeanLocalField F]`), `E` a field with `[Algebra F E]`, `n m : ℕ`. For
`x ∈ GL_n(E)` (the Library's `GeneralLinear n E`),

`determinantWindow F m x = 1` if `0 ≤ ord_F (N_{E/F} (det x)) < m`, and `0` otherwise,

as a complex number. Here `det x` is `GeneralLinear.determinant x : Eˣ`, `N_{E/F}` is Mathlib's
`Algebra.norm F : E →* F`, and `ord_F` is `(LocalFieldData.ofInstances F).ord`, the normalized
integer order of `F` (`ord_F ϖ = 1` for a uniformizer `ϖ`; module
`Langlands.LocalField.LocalFieldData`). Since `E` is a field and `det x` is a unit,
`N_{E/F}(det x) ≠ 0`, so the convention `ord_F 0 = 0` of `LocalFieldData.ord` plays no role.
Formally the function is `Set.indicator` of the set of such `x` applied to the constant
function `1`.

## Normalization over the scalars

The window is designed for `m = n · [E : F]` with `0 < n` and `E` a field finite over `F`, so
that `m > 0`. For `z ∈ F^×` embedded as the scalar matrix
`z · 1 ∈ GL_n(E)`, `N_{E/F}(det(z x)) = z^{n [E : F]} N_{E/F}(det x)`, so
`ord_F N_{E/F}(det(z x)) = n [E : F] · ord_F z + ord_F N_{E/F}(det x)`. Hence, for every `x`,
exactly one value of `ord_F z` puts `z x` in the window (an interval of `m > 0` consecutive
integers contains exactly one multiple-shift of `ord_F N_{E/F}(det x)` by `m`): the set of `z ∈ F^×` with
`determinantWindow F (n [E : F]) (z x) = 1` is one coset `ϖ^k O_F^×`, and for a Haar measure
`μ_Z` on `F^×`, `∫ determinantWindow F (n [E : F]) (z x) dμ_Z(z) = μ_Z(O_F^×)` does not depend
on `x`. For `n = 0` the length `m` is `0`, the window is identically zero and none of this
applies. This is the property that makes window cut-offs of coefficients compatible with Schur
orthogonality modulo the centre (Renard 2026, IV.3.3, Remark, printed p. 102: integrals over
`G / Z(G)` may be replaced by integrals over `G / A` for a closed central subgroup `A` with
`Z(G) / A` compact; here `A = F^×` in the centre `E^×` of `GL_n(E)`). These facts are explained
here and are not stated in Lean in this module.

## Local constancy

Assume moreover `[Module.Finite F E] [TopologicalSpace E] [IsTopologicalRing E]
[IsModuleTopology F E]`.

- `continuous_algebraNorm_of_isModuleTopology`: `Algebra.norm F : E → F` is continuous, for any
  finite commutative `F`-algebra `E` with its module topology. Proof: with a basis `b` of `E`
  over `F`, `Algebra.norm F x` is the determinant of `Algebra.leftMulMatrix b x`
  (`Algebra.norm_eq_matrix_det`), and `x ↦ Algebra.leftMulMatrix b x` is `F`-linear, hence
  continuous for the module topology (`IsModuleTopology.continuous_of_linearMap`).
- `ord_eq_zero_iff_mem_ker_normalizedAbsUnits`: a unit `a` of `F` has `ord_F a = 0` iff it lies
  in the kernel of the normalized absolute value `LocalFieldData.normalizedAbsUnits` of
  `LocalFieldData.ofInstances F`. Proof: `|a| = q^{-ord_F a}` with `q > 1` the residue
  cardinality (`LocalFieldData.normalizedAbs_of_ne_zero`, `residueCardinality_gt_one`).
- `isLocallyConstant_determinantWindow m`: `determinantWindow F m` is locally constant on
  `GL_n(E)`. Proof: `g = N_{E/F} ∘ det : GL_n(E) → F^×` is a continuous homomorphism
  (Mathlib's `Matrix.GeneralLinearGroup.continuous_det` and `Continuous.units_map`), and the
  kernel of the normalized absolute value is open in `F^×`
  (`LocalFieldData.isOpen_ker_normalizedAbsUnits`), so `U = g⁻¹(ker)` is an open subgroup of
  `GL_n(E)`. For `u ∈ U`, `ord_F (g (x u)) = ord_F (g x) + ord_F (g u) = ord_F (g x)`
  (`LocalFieldData.ord_mul`), so the window is constant on each neighbourhood `x U` of `x`.

## Provenance

The cut-off by a determinant window normalized over the scalars is this Library's
construction: it comes from step 1 of the proof sketch in
`Langlands/BaseChange/SupercuspidalCoefficientEllipticMatchingStatement.md`, where it turns
matrix coefficients of supercuspidal representations, which are compactly supported only
modulo the centre, into Schwartz–Bruhat test functions whose traces can be computed by Schur
orthogonality modulo `F^×`. Henniart–Lemaire 2011, II.6.3–II.6.4 (printed pp. 119–121), which
that statement follows, impose at auxiliary places a central-character covariance, elliptic
support and a linear combination of matrix coefficients of cuspidal representations; they do
not use a determinant window.

The Library contains related facts in other settings:
`Langlands.LocalFieldData.ker_ordUnits` (module `Langlands.AllField.Group.GL.UnramifiedCharacter`)
identifies the kernel of the order on units with that of the normalized absolute value, and
`Langlands.Plancherel.TorusNormKernel.continuous_algebraNorm` proves continuity of the field
norm for a nontrivially normed base field; the two lemmas of this module are the forms needed
for a local field given by instances and for any finite algebra with its module topology.
