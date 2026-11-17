import Langlands.Global.RankinSelberg.ArchimedeanFunctionalEquationStatement
import Langlands.Automorphic.ArchimedeanPlaceParameter

/-! # Reduction of the complex-place Rankin–Selberg functional equation to local premises

This module proves `ComplexPlaceFunctionalEquationStatement` (Jacquet 2009, Theorem 2.1, at
a complex place, for archimedean restrictions of global Whittaker functions of actual cuspidal
realizations) from five explicitly stated premises:

* the local functional equations `ComplexLocalUnequalFunctionalEquationStatement` and
  `ComplexLocalEqualFunctionalEquationStatement` for the functions of the Whittaker model
  `complexWhittakerModel` of the complex standard module of a list of characters (Jacquet
  2009, Theorem 2.1, for the induced representations `π_(σ,u)`);
* `ComplexPlaceWhittakerModelStatement`: archimedean restrictions of global Whittaker functions
  lie in the Whittaker model of the parameter at the place;
* `ComplexPlaceMinusOneStatement`: the scalar of `-1` at the place is `∏ χ_j(-1)`;
* `ComplexPlaceContragredientParameterStatement`: the parameter of the contragredient is a
  permutation of the inverse characters.

None of the premises is proved here. See the paired Markdown.
-/

noncomputable section
universe u
open NumberField MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.Operator
open Langlands.Global.HeckeFunctionalEquation Langlands.LocalFactor.Archimedean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.LocalFactor.Archimedean.ComplexCharacterData

/-- The inverse character `z ↦ χ(z)⁻¹`, with negated weight and negated exponent. -/
def inv (d : ComplexCharacterData) : ComplexCharacterData where
  character := (ContinuousMonoidHom.inv ℂˣ).comp d.character
  weight := -d.weight
  exponent := -d.exponent
  character_eq z := by
    have h : (((ContinuousMonoidHom.inv ℂˣ).comp d.character z : ℂˣ) : ℂ) =
        ((d.character z : ℂˣ) : ℂ)⁻¹ := Units.val_inv_eq_inv_val _
    rw [h, d.character_eq, mul_inv, zpow_neg, mul_neg, Complex.cpow_neg]

@[simp]
theorem inv_weight (d : ComplexCharacterData) : d.inv.weight = -d.weight := rfl

@[simp]
theorem inv_exponent (d : ComplexCharacterData) : d.inv.exponent = -d.exponent := rfl

theorem inv_character_apply (d : ComplexCharacterData) (z : Weil.Archimedean.ComplexWeil) :
    ((d.inv.character z : ℂˣ) : ℂ) = ((d.character z : ℂˣ) : ℂ)⁻¹ :=
  Units.val_inv_eq_inv_val _

end Langlands.LocalFactor.Archimedean.ComplexCharacterData

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

/-! ### Local objects -/

/-- The value `∏_j χ_j(-1)` of the characters of a list of complex character blocks at `-1`:
the scalar by which `-1 ∈ GL_n(ℂ)` acts on their standard module (central character at
`-1`). -/
def complexCentralSign (ds : List ComplexCharacterData) : ℂ :=
  (ds.map fun d => ((d.character (-1) : ℂˣ) : ℂ)).prod

/-- Jacquet's height `‖g‖_H = Tr(g g*) + Tr((g⁻¹)* g⁻¹) = ∑_(i,j) |g_(ij)|² + |(g⁻¹)_(ij)|²`
on `GL_n(ℂ)` (Jacquet 2009, (2.1)). -/
def complexMatrixHeight {n : ℕ} (g : Langlands.GeneralLinear n ℂ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    (‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 +
      ‖((g⁻¹ : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2)

/-- The standard generic character `θ(u) = ψ_a(∑_i u_(i,i+1))` of the upper unipotent matrices
of `GL_(r+1)(ℂ)`, for `ψ_a = complexScaledCharacter a` (Jacquet 2009, (2.2)). It is
evaluated on all of `GL_(r+1)(ℂ)`; only its values on `N_(r+1)(ℂ)` are used. -/
def complexWhittakerCharacter {r : ℕ} (a : ℂˣ) (u : Langlands.GeneralLinear (r + 1) ℂ) : ℂ :=
  (complexScaledCharacter a).complex
    (∑ i : Fin r, (u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) i.castSucc i.succ)

/-- `B` is a Whittaker intertwiner of the complex standard module of `ds` for `ψ_a`: a linear
map from the `U(r+1)`-finite functions of the standard module to functions on `GL_(r+1)(ℂ)`
such that every `B f`

* is `θ`-equivariant on the left: `B f (u g) = ψ_a(∑_i u_(i,i+1)) B f (g)` for `u ∈ N_(r+1)(ℂ)`;
* is smooth;
* has moderate growth: `|B f (g)| ≤ C ‖g‖_H^N`;

and `B` carries right translation by `k ∈ U(r+1)` and the right derivative along a real
direction `X ∈ 𝔤𝔩_(r+1)(ℂ)` to the same operations on the values: whenever `f'` is the right
translate (right derivative) of `f`, `B f'` is that of `B f`. -/
def IsComplexWhittakerIntertwiner (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ)
    (B : Automorphic.complexStandardKFinite (r + 1) ds →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℂ → ℂ)) : Prop :=
  (∀ (f : Automorphic.complexStandardKFinite (r + 1) ds),
      ∀ u ∈ GeneralLinear.upperUnipotent (r + 1) ℂ, ∀ g : Langlands.GeneralLinear (r + 1) ℂ,
        B f (u * g) = complexWhittakerCharacter a u * B f g) ∧
    (∀ f : Automorphic.complexStandardKFinite (r + 1) ds,
      ContMDiff (Archimedean.matrixModel ℂ (r + 1)) 𝓘(ℝ, ℂ) ∞ (B f)) ∧
    (∀ f : Automorphic.complexStandardKFinite (r + 1) ds, ∃ (C : ℝ) (N : ℕ),
      ∀ g : Langlands.GeneralLinear (r + 1) ℂ, ‖B f g‖ ≤ C * complexMatrixHeight g ^ N) ∧
    (∀ (k : Archimedean.unitaryCompact ℂ (r + 1))
      (f f' : Automorphic.complexStandardKFinite (r + 1) ds),
      (f' : Langlands.GeneralLinear (r + 1) ℂ → ℂ) =
          Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (r + 1) ℂ)
            (k : Langlands.GeneralLinear (r + 1) ℂ) f →
        B f' = Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (r + 1) ℂ)
          (k : Langlands.GeneralLinear (r + 1) ℂ) (B f)) ∧
    ∀ (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
      (f f' : Automorphic.complexStandardKFinite (r + 1) ds),
      (f' : Langlands.GeneralLinear (r + 1) ℂ → ℂ) =
          Archimedean.rightDerivative (Archimedean.matrixModel ℂ (r + 1)) X
            (f : Langlands.GeneralLinear (r + 1) ℂ → ℂ) →
        B f' = Archimedean.rightDerivative (Archimedean.matrixModel ℂ (r + 1)) X (B f)

/-- The (`U(r+1)`-finite) Whittaker model of the complex standard module of `ds` for `ψ_a`:
the span of the values of all Whittaker intertwiners. By the uniqueness of the continuous
`ψ`-form on the induced representation (Jacquet 2009, p.4, citing Wallach), it is contained in
Jacquet's `W(π_(σ,u) : ψ_a)`; see the paired Markdown. -/
def complexWhittakerModel (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ) :
    Submodule ℂ (Langlands.GeneralLinear (r + 1) ℂ → ℂ) :=
  ⨆ (B : Automorphic.complexStandardKFinite (r + 1) ds →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℂ → ℂ)) (_ : IsComplexWhittakerIntertwiner r ds a B),
    LinearMap.range B

/-! ### The premises -/

/-- **Local premise, unequal ranks** (Jacquet 2009, Theorem 2.1 (i)–(iii), for
`GL_(r+1)(ℂ) × GL_(t+1)(ℂ)`, `t < r`, and the induced representations of lists of
characters).

For lists `d`, `d'` of `r + 1` and `t + 1` complex characters, `a ∈ ℂˣ`, a quotient measure
`D`, `W` in the Whittaker model of the standard module of `d` for `ψ_a` and `W'` in that of
`d'` for `ψ_(-a) = ψ_a⁻¹`, the conclusion of `ComplexUnequalFunctionalEquationStatement`
holds with the sign `ω'(-1)^r = complexCentralSign d' ^ r` and the dual `L`-factor of the
inverse characters. -/
def ComplexLocalUnequalFunctionalEquationStatement : Prop := by
  classical
  exact
  ∀ (r t : ℕ) (h : t < r) (d d' : List ComplexCharacterData),
    d.length = r + 1 → d'.length = t + 1 →
  ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData t)
    (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℂ → ℂ),
    W ∈ complexWhittakerModel r d a → W' ∈ complexWhittakerModel t d' (-a) →
  ∃ (σ : ℝ) (M Md : ℂ → ℂ),
    (∀ s : ℂ, σ < s.re → Integrable (complexUnequalIntegrand h W W' s) D.measure) ∧
    (∀ s : ℂ, σ < s.re →
      Integrable (complexUnequalDualKernel h W W' s) (complexUnequalDualMeasure (r := r) a D)) ∧
    DifferentiableOn ℂ (complexUnequalIntegral h D W W') {s : ℂ | σ < s.re} ∧
    DifferentiableOn ℂ (complexUnequalDualIntegral h a D W W') {s : ℂ | σ < s.re} ∧
    MeromorphicOn M Set.univ ∧ MeromorphicOn Md Set.univ ∧
    (∀ s : ℂ, σ < s.re → complexUnequalIntegral h D W W' s = M s) ∧
    (∀ s : ℂ, σ < s.re → complexUnequalDualIntegral h a D W W' s = Md s) ∧
    ∀ᶠ s in Filter.codiscrete ℂ,
      ((complexPairLFactor d d').denominator s)⁻¹ * Md (1 - s) =
        complexCentralSign d' ^ r *
          (complexPairEpsilon d d' a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) *
          ((complexPairLFactor (d.map ComplexCharacterData.inv)
            (d'.map ComplexCharacterData.inv)).denominator (1 - s))⁻¹ * M s

/-- **Local premise, equal ranks** (Jacquet 2009, Theorem 2.1 (i)–(iii), for
`GL_(r+1)(ℂ) × GL_(r+1)(ℂ)` and the induced representations of lists of characters).

For lists `d`, `d'` of `r + 1` complex characters, `a ∈ ℂˣ`, a quotient measure `D`, `W` in
the Whittaker model of `d` for `ψ_a`, `W'` in that of `d'` for `ψ_(-a)` and a Schwartz
function `Φ`, the conclusion of `ComplexEqualFunctionalEquationStatement` holds with the sign
`complexCentralSign d' ^ r` and the dual `L`-factor of the inverse characters. -/
def ComplexLocalEqualFunctionalEquationStatement : Prop := by
  classical
  exact
  ∀ (r : ℕ) (d d' : List ComplexCharacterData), d.length = r + 1 → d'.length = r + 1 →
  ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData r) (W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
    (Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ),
    W ∈ complexWhittakerModel r d a → W' ∈ complexWhittakerModel r d' (-a) →
  ∃ (σ : ℝ) (M Md : ℂ → ℂ),
    (∀ s : ℂ, σ < s.re → Integrable (complexEqualIntegrand W W' Φ s) D.measure) ∧
    (∀ s : ℂ, σ < s.re →
      Integrable (complexEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
        (ArchimedeanLocal.dualFunction (r + 1) W') (complexFourierTransform a Φ) s)
        D.measure) ∧
    DifferentiableOn ℂ (complexEqualIntegral D W W' Φ) {s : ℂ | σ < s.re} ∧
    DifferentiableOn ℂ (complexEqualDualIntegral a D W W' Φ) {s : ℂ | σ < s.re} ∧
    MeromorphicOn M Set.univ ∧ MeromorphicOn Md Set.univ ∧
    (∀ s : ℂ, σ < s.re → complexEqualIntegral D W W' Φ s = M s) ∧
    (∀ s : ℂ, σ < s.re → complexEqualDualIntegral a D W W' Φ s = Md s) ∧
    ∀ᶠ s in Filter.codiscrete ℂ,
      ((complexPairLFactor d d').denominator s)⁻¹ * Md (1 - s) =
        complexCentralSign d' ^ r *
          (complexPairEpsilon d d' a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) *
          ((complexPairLFactor (d.map ComplexCharacterData.inv)
            (d'.map ComplexCharacterData.inv)).denominator (1 - s))⁻¹ * M s

/-- **Bridge premise.** Let `T` be an actual cuspidal realization of `GL_(r+1)` over a number
field `F`, `ψ` a unitary character of the adeles trivial on `F` whose component at the
complex place `w` is `ψ_a`, and `d` the parameter of `T` at `w`. Then every archimedean
restriction `g ↦ W_x(ι_w(g) a_f)` of a global Whittaker function of `T` for `ψ` lies in the
Whittaker model of `d` for `ψ_a`, and every one for `ψ⁻¹` lies in that for `ψ_(-a)`. -/
def ComplexPlaceWhittakerModelStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T : Automorphic.CuspidalOperatorRealization F r)
    (w : {v : InfinitePlace F // v.IsComplex}) (a : ℂˣ),
    IsComplexAdditiveComponent ψ w.1 w.2 a →
  ∀ d : List ComplexCharacterData,
    Automorphic.OperatorRealization.HasComplexPlaceParameter T.realization w d →
  ∀ W : Langlands.GeneralLinear (r + 1) ℂ → ℂ,
    (IsComplexPlaceWhittaker F T ψ.complex w W → W ∈ complexWhittakerModel r d a) ∧
    (IsComplexPlaceWhittaker F T ψ.complex⁻¹ w W → W ∈ complexWhittakerModel r d (-a))

/-- **Minus-one premise.** If an actual cuspidal realization `T` of `GL_(r+1)` has the
parameter `d` at the complex place `w`, then the scalar `ω_w(-1)` by which `-1 ∈ U(r+1)` acts
at `w` is `∏_j χ_j(-1)`. -/
def ComplexPlaceMinusOneStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (w : {v : InfinitePlace F // v.IsComplex}) (d : List ComplexCharacterData),
    Automorphic.OperatorRealization.HasComplexPlaceParameter T.realization w d →
    complexMinusOneScalar T w = complexCentralSign d

/-- **Contragredient premise.** If `Td` is contragredient to the actual cuspidal realization
`T`, and `d`, `dd` are parameters of `T`, `Td` at the complex place `w`, then `dd` is a
permutation of the list of inverse characters of `d`. -/
def ComplexPlaceContragredientParameterStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T Td : Automorphic.CuspidalOperatorRealization F r),
    Automorphic.OperatorRealization.IsContragredientOf Td.realization T.realization →
  ∀ (w : {v : InfinitePlace F // v.IsComplex}) (d dd : List ComplexCharacterData),
    Automorphic.OperatorRealization.HasComplexPlaceParameter T.realization w d →
    Automorphic.OperatorRealization.HasComplexPlaceParameter Td.realization w dd →
    dd.Perm (d.map ComplexCharacterData.inv)

/-! ### The reductions -/

/-- The unequal-rank complex-place functional equation follows from the unequal-rank local
premise, the bridge, the minus-one and the contragredient premises. -/
def ComplexUnequalFunctionalEquationReductionStatement : Prop :=
  ComplexLocalUnequalFunctionalEquationStatement → ComplexPlaceWhittakerModelStatement.{u} →
    ComplexPlaceMinusOneStatement.{u} → ComplexPlaceContragredientParameterStatement.{u} →
    ComplexUnequalFunctionalEquationStatement.{u}

/-- The equal-rank complex-place functional equation follows from the equal-rank local
premise, the bridge, the minus-one and the contragredient premises. -/
def ComplexEqualFunctionalEquationReductionStatement : Prop :=
  ComplexLocalEqualFunctionalEquationStatement → ComplexPlaceWhittakerModelStatement.{u} →
    ComplexPlaceMinusOneStatement.{u} → ComplexPlaceContragredientParameterStatement.{u} →
    ComplexEqualFunctionalEquationStatement.{u}

/-- **The reduction.** `ComplexPlaceFunctionalEquationStatement` follows from the two local
functional equations, the bridge, the minus-one and the contragredient premises. -/
def ComplexPlaceFunctionalEquationReductionStatement : Prop :=
  ComplexLocalUnequalFunctionalEquationStatement →
    ComplexLocalEqualFunctionalEquationStatement → ComplexPlaceWhittakerModelStatement.{u} →
    ComplexPlaceMinusOneStatement.{u} → ComplexPlaceContragredientParameterStatement.{u} →
    ComplexPlaceFunctionalEquationStatement.{u}

theorem complexUnequalFunctionalEquationReduction :
    ComplexUnequalFunctionalEquationReductionStatement.{u} := by
  intro hloc hmodel hsign hdual
  unfold ComplexUnequalFunctionalEquationStatement
  intro F _ _ _ ψ hψ r t h T Td T' Td' hTd hTd' w a ha d d' dd dd' hd hd' hdd hdd' D W W'
    hW hW'
  obtain ⟨σ, M, Md, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    hloc r t h d d' hd.1 hd'.1 a D W W'
      ((hmodel F ψ hψ r T w a ha d hd W).1 hW) ((hmodel F ψ hψ t T' w a ha d' hd' W').2 hW')
  have hL : complexPairLFactor dd dd' =
      complexPairLFactor (d.map ComplexCharacterData.inv) (d'.map ComplexCharacterData.inv) :=
    complexPairLFactor_perm (hdual F r T Td hTd w d dd hd hdd)
      (hdual F t T' Td' hTd' w d' dd' hd' hdd')
  refine ⟨σ, M, Md, h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
  rw [hL, hsign F t T' w d' hd']
  exact h9

theorem complexEqualFunctionalEquationReduction :
    ComplexEqualFunctionalEquationReductionStatement.{u} := by
  intro hloc hmodel hsign hdual
  unfold ComplexEqualFunctionalEquationStatement
  intro F _ _ _ ψ hψ r T Td T' Td' hTd hTd' w a ha d d' dd dd' hd hd' hdd hdd' D W W' Φ
    hW hW'
  obtain ⟨σ, M, Md, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    hloc r d d' hd.1 hd'.1 a D W W' Φ
      ((hmodel F ψ hψ r T w a ha d hd W).1 hW) ((hmodel F ψ hψ r T' w a ha d' hd' W').2 hW')
  have hL : complexPairLFactor dd dd' =
      complexPairLFactor (d.map ComplexCharacterData.inv) (d'.map ComplexCharacterData.inv) :=
    complexPairLFactor_perm (hdual F r T Td hTd w d dd hd hdd)
      (hdual F r T' Td' hTd' w d' dd' hd' hdd')
  refine ⟨σ, M, Md, h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
  rw [hL, hsign F r T' w d' hd']
  exact h9

theorem complexPlaceFunctionalEquationReduction :
    ComplexPlaceFunctionalEquationReductionStatement.{u} :=
  fun hU hE hmodel hsign hdual =>
    ⟨complexUnequalFunctionalEquationReduction hU hmodel hsign hdual,
      complexEqualFunctionalEquationReduction hE hmodel hsign hdual⟩

end Langlands.Global.RankinSelbergGlobal
