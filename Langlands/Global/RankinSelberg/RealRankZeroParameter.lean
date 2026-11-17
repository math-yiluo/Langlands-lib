import Langlands.Global.RankinSelberg.RealPlaceWhittakerCovariance
import Langlands.Global.RankinSelberg.RealRankZeroPlace
import Langlands.Automorphic.ArchimedeanPlaceParameter
import Langlands.Automorphic.Contragredient
import Langlands.Representation.Archimedean.PrincipalSeriesStability
import Langlands.Representation.Archimedean.PrincipalSeriesExtension

/-! # Rank-one realizations with a real-place parameter

For a real character `χ_c`, the function `g ↦ χ_c(det g)` lies in the `O(1)`-finite part of the
real standard module of the single block `[character c]`; right translation by `h` multiplies it
by `χ_c(det h)` and the right derivative along `1 ∈ 𝔤𝔩₁(ℝ)` multiplies it by the exponent of
`c`. Through the injective intertwiner of a real-place parameter, the Schur scalars of an
irreducible rank-one realization are therefore `χ_c(-1)` and the exponent of `c`. Restrictions
of global Whittaker functions of a cuspidal realization of `GL₁` are then multiples of
`χ_c ∘ det`, and the parameter of a contragredient has the same parity and the negated exponent.
See the paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.Operator TensorProduct CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealRankZero

open Langlands.Automorphic Langlands.Global.ArchimedeanGL Langlands.LocalFactor.Archimedean
open Langlands.Archimedean

/-! ### The character `χ_c ∘ det` of `GL₁(ℝ)` -/

section Character

variable (c : RealCharacterData)

/-- The function `g ↦ χ_c(det g)` on `GL₁(ℝ)`. -/
def characterFunction : Langlands.GeneralLinear 1 ℝ → ℂ :=
  fun g => (c.character (GeneralLinear.determinant g) : ℂ)

theorem characterFunction_mul (g h : Langlands.GeneralLinear 1 ℝ) :
    characterFunction c (g * h) = characterFunction c g * characterFunction c h := by
  simp only [characterFunction, map_mul, Units.val_mul]

theorem characterFunction_one : characterFunction c 1 = 1 := by
  simp only [characterFunction, map_one, Units.val_one]

theorem character_exp (u : ℝ) :
    ((c.character (Units.mk0 (Real.exp u) (Real.exp_pos u).ne') : ℂˣ) : ℂ) =
      Complex.exp (c.exponent * u) := by
  rw [c.character_eq]
  simp only [Units.val_mk0, abs_of_pos (Real.exp_pos u), div_self (Real.exp_pos u).ne',
    Complex.ofReal_one, one_pow, one_mul]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'),
    ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp, mul_comm]

theorem character_neg_one : ((c.character (-1) : ℂˣ) : ℂ) = (-1) ^ c.parity.val := by
  rw [c.character_eq]
  simp

theorem rightTranslation_characterFunction (h : Langlands.GeneralLinear 1 ℝ) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 1 ℝ) h (characterFunction c) =
      characterFunction c h • characterFunction c := by
  funext g
  change characterFunction c (g * h) = characterFunction c h * characterFunction c g
  rw [characterFunction_mul, mul_comm]

theorem determinant_val_fin_one (g : Langlands.GeneralLinear 1 ℝ) :
    ((GeneralLinear.determinant g : ℝˣ) : ℝ) = (g : Matrix (Fin 1) (Fin 1) ℝ) 0 0 := by
  change (g : Matrix (Fin 1) (Fin 1) ℝ).det = _
  exact Matrix.det_fin_one _

theorem contMDiff_characterFunction :
    ContMDiff (matrixModel ℝ 1) 𝓘(ℝ, ℂ) ∞ (characterFunction c) := by
  refine contMDiff_of_contDiffOn (ψ := fun Y : Matrix (Fin 1) (Fin 1) ℝ =>
      (((Y 0 0 / |Y 0 0| : ℝ) : ℂ) ^ c.parity.val * ((|Y 0 0| : ℝ) : ℂ) ^ c.exponent)) ?_ ?_
  · intro Y hY
    have h0 : Y 0 0 ≠ 0 := by
      have h := (Matrix.isUnit_iff_isUnit_det Y).mp hY
      rw [Matrix.det_fin_one] at h
      exact h.ne_zero
    have he : ContDiff ℝ ∞ (fun Y : Matrix (Fin 1) (Fin 1) ℝ => Y 0 0) :=
      PrincipalSeriesExtension.contDiff_entry 0 0
    have habs : ContDiffAt ℝ ∞ (fun Y : Matrix (Fin 1) (Fin 1) ℝ => |Y 0 0|) Y :=
      ContDiffAt.comp (g := fun x : ℝ => |x|) Y (contDiffAt_abs h0) he.contDiffAt
    refine ContDiffAt.contDiffWithinAt ?_
    refine ContDiffAt.mul ?_ ?_
    · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp Y
        (he.contDiffAt.div habs (abs_ne_zero.mpr h0))).pow _
    · exact PrincipalSeriesExtension.contDiffAt_ofReal_cpow habs (abs_pos.mpr h0) _
  · intro g
    simp only [characterFunction]
    rw [c.character_eq, determinant_val_fin_one]

theorem characterFunction_mem_principalSeries :
    characterFunction c ∈
      principalSeries ℝ 1 (realPositionCharacter [RealBlock.character c]) := by
  refine ⟨contMDiff_characterFunction c, fun a u g => ?_⟩
  have hu : characterFunction c (u : Langlands.GeneralLinear 1 ℝ) = 1 := by
    have hdet : GeneralLinear.determinant (u : Langlands.GeneralLinear 1 ℝ) = 1 := by
      apply Units.ext
      change ((u : Langlands.GeneralLinear 1 ℝ) : Matrix (Fin 1) (Fin 1) ℝ).det = 1
      rw [Matrix.det_of_isUpperTriangular u.2.1]
      exact Finset.prod_eq_one fun i _ => u.2.2 i
    simp only [characterFunction, hdet, map_one, Units.val_one]
  have ha : GeneralLinear.determinant
      (GeneralLinear.Iwasawa.diagonalUnits a : Langlands.GeneralLinear 1 ℝ) = a 0 := by
    apply Units.ext
    change ((GeneralLinear.Iwasawa.diagonalUnits a : Langlands.GeneralLinear 1 ℝ) :
      Matrix (Fin 1) (Fin 1) ℝ).det = _
    rw [GeneralLinear.Iwasawa.diagonalUnits_val, Matrix.det_diagonal, Fin.prod_univ_one]
  rw [characterFunction_mul, characterFunction_mul, hu, mul_one]
  simp only [characterFunction, ha, principalSeriesCharacter, Fin.prod_univ_one,
    realPositionCharacter]
  simp

theorem characterFunction_mem_realStandardModule :
    characterFunction c ∈ realStandardModule 1 [RealBlock.character c] := by
  refine ⟨characterFunction_mem_principalSeries c, fun p d hd => ?_⟩
  cases p <;> simp [realInducedBlockAt] at hd

theorem characterFunction_mem_kFinite :
    characterFunction c ∈ realStandardKFinite 1 [RealBlock.character c] := by
  refine Submodule.mem_inf.mpr ⟨characterFunction_mem_realStandardModule c, ?_⟩
  rw [mem_kFiniteVectors_iff]
  have hle : Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ 1 =>
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 1 ℝ) (k : Langlands.GeneralLinear 1 ℝ)
        (characterFunction c)) ≤ Submodule.span ℂ {characterFunction c} := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    change Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 1 ℝ)
      (k : Langlands.GeneralLinear 1 ℝ) (characterFunction c) ∈ _
    rw [rightTranslation_characterFunction]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  exact Submodule.finiteDimensional_of_le hle

theorem rightDerivative_characterFunction :
    rightDerivative (matrixModel ℝ 1) (1 : Matrix (Fin 1) (Fin 1) ℝ) (characterFunction c) =
      c.exponent • characterFunction c := by
  funext g
  rw [rightDerivative_eq_fderiv_mul_left (contMDiff_characterFunction c)]
  have hL := (differentiableAt_unitsExtension_mul_left (contMDiff_characterFunction c) g).hasFDerivAt
  have hγ : HasDerivAt (fun t : ℝ => Real.exp t • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      (Real.exp 0 • (1 : Matrix (Fin 1) (Fin 1) ℝ)) 0 :=
    (Real.hasDerivAt_exp 0).smul_const _
  have hcomp := hL.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by simp)
  have hfun : (fun y : Matrix (Fin 1) (Fin 1) ℝ =>
      unitsExtension (characterFunction c) ((g : Matrix (Fin 1) (Fin 1) ℝ) * y)) ∘
        (fun t : ℝ => Real.exp t • (1 : Matrix (Fin 1) (Fin 1) ℝ)) =
      fun t : ℝ => characterFunction c g * Complex.exp (c.exponent * t) := by
    funext t
    simp only [Function.comp_apply]
    have hv : (g : Matrix (Fin 1) (Fin 1) ℝ) * (Real.exp t • (1 : Matrix (Fin 1) (Fin 1) ℝ)) =
        ((g * scalarUnit (Units.mk0 (Real.exp t) (Real.exp_pos t).ne') :
          Langlands.GeneralLinear 1 ℝ) : Matrix (Fin 1) (Fin 1) ℝ) := by
      rw [Units.val_mul, scalarUnit_val, Algebra.algebraMap_eq_smul_one, Units.val_mk0]
    rw [hv, unitsExtension_val, characterFunction_mul]
    congr 1
    simp only [characterFunction, determinant_scalarUnit, character_exp]
  rw [hfun] at hcomp
  have hd : HasDerivAt (fun t : ℝ => characterFunction c g * Complex.exp (c.exponent * t))
      (characterFunction c g * c.exponent) 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul c.exponent).cexp).const_mul
      (characterFunction c g)
    convert h using 1 <;> simp
  have heq := hcomp.unique hd
  simp only [Real.exp_zero, one_smul] at heq
  rw [heq, Pi.smul_apply, smul_eq_mul, mul_comm]

end Character

/-- In a complex vector space, `a • x = b • x` with `x ≠ 0` forces `a = b`. -/
theorem eq_of_smul_eq_smul {V : Type*} [AddCommGroup V] [Module ℂ V] {a b : ℂ} {x : V}
    (hx : x ≠ 0) (h : a • x = b • x) : a = b := by
  by_contra hab
  apply hx
  have h' : (a - b) • x = 0 := by rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hab)

/-- A bilinear form is homogeneous of bidegree `(1, 1)`. The module structures are implicit
arguments read off from the form. -/
theorem bilinear_smul_smul {V W : Type*} {iV : AddCommMonoid V} {mV : Module ℂ V}
    {iW : AddCommMonoid W} {mW : Module ℂ W} (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a b : ℂ) (x : V)
    (y : W) : B (a • x) (b • y) = (a * b) * B x y := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem bilinear_smul_left {V W : Type*} {iV : AddCommMonoid V} {mV : Module ℂ V}
    {iW : AddCommMonoid W} {mW : Module ℂ W} (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a : ℂ) (x : V)
    (y : W) : B (a • x) y = a * B x y := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem bilinear_smul_right {V W : Type*} {iV : AddCommMonoid V} {mV : Module ℂ V}
    {iW : AddCommMonoid W} {mW : Module ℂ W} (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (b : ℂ) (x : V)
    (y : W) : B x (b • y) = b * B x y := by
  simp only [map_smul, smul_eq_mul]

/-! ### The Schur scalars of a realization with a rank-one real parameter -/

section Realization

variable {F : Type u} [Field F] [NumberField F]

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}

local instance realRankZeroParamRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F 1) :=
  Submodule.addCommGroup _
local instance realRankZeroParamContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F 1) :=
  Submodule.addCommGroup _
local instance realRankZeroParamSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F 1) :=
  Submodule.addCommGroup _
local instance realRankZeroParamFormsAddCommGroup : AddCommGroup (AutomorphicForms F 1) :=
  Submodule.addCommGroup _
local instance realRankZeroParamStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F 1) :=
  Submodule.addCommGroup _
local instance realRankZeroParamRealizationAddCommGroup (S : OperatorRealization F 1) :
    AddCommGroup S.Space := Submodule.addCommGroup _

/-- The vector of `S` attached to `χ_c ∘ det` by a real-place parameter `[character c]`. -/
theorem parameter_characterFunction_ne_zero (S : OperatorRealization F 1)
    (c : RealCharacterData)
    (A : realStandardKFinite 1 [RealBlock.character c] →ₗ[ℂ] S.Space)
    (hA : Function.Injective A) :
    A ⟨characterFunction c, characterFunction_mem_kFinite c⟩ ≠ 0 := by
  intro h
  have h0 := hA (h.trans (map_zero A).symm)
  have h1 := congrFun (congrArg Subtype.val h0) 1
  change characterFunction c 1 = 0 at h1
  rw [characterFunction_one] at h1
  exact one_ne_zero h1

/-- An irreducible rank-one realization with the real-place parameter `[character c]` at `v`
is nonzero. -/
theorem hasRealPlaceParameter_nontrivial (S : OperatorRealization F 1) (v : RP)
    (c : RealCharacterData) (hp : S.HasRealPlaceParameter v [RealBlock.character c]) :
    ∃ x : S.Space, x ≠ 0 := by
  obtain ⟨-, A, hA, -, -⟩ := hp
  exact ⟨_, parameter_characterFunction_ne_zero S c A hA⟩

/-- On an irreducible rank-one realization with the real-place parameter `[character c]` at
`v`, the element `-1 ∈ O(1)` at `v` acts by `χ_c(-1)`. -/
theorem hasRealPlaceParameter_compact (S : OperatorRealization F 1) (hS : S.IsIrreducible)
    (v : RP) (c : RealCharacterData)
    (hp : S.HasRealPlaceParameter v [RealBlock.character c]) (f : S.Space) :
    S.realPlaceCompactRepresentation v minusOneOrthogonal f =
      ((c.character (-1) : ℂˣ) : ℂ) • f := by
  obtain ⟨-, A, hA, hK, -⟩ := hp
  let f0 : realStandardKFinite 1 [RealBlock.character c] :=
    ⟨characterFunction c, characterFunction_mem_kFinite c⟩
  have hx0 : A f0 ≠ 0 := parameter_characterFunction_ne_zero S c A hA
  obtain ⟨ε, hε⟩ := exists_compactRepresentation_eq_smul S hS
    (realPlaceCompactInclusion F 1 v minusOneOrthogonal)
  have hε' : ∀ f : S.Space, S.realPlaceCompactRepresentation v minusOneOrthogonal f = ε • f :=
    hε
  have hk0mem : (Unitary.toUnits minusOneOrthogonal : Langlands.GeneralLinear 1 ℝ) ∈
      unitaryCompact ℝ 1 := minusOneOrthogonal.2
  let k0 : unitaryCompact ℝ 1 := ⟨_, hk0mem⟩
  have hk0eq : (⟨((k0 : Langlands.GeneralLinear 1 ℝ) : Matrix (Fin 1) (Fin 1) ℝ), k0.2⟩ :
      Matrix.unitaryGroup (Fin 1) ℝ) = minusOneOrthogonal :=
    Subtype.ext (Unitary.val_toUnits_apply _)
  have hK0 := hK k0 f0
  obtain ⟨hf, hAk⟩ := hK0
  have hdet : characterFunction c (k0 : Langlands.GeneralLinear 1 ℝ) =
      ((c.character (-1) : ℂˣ) : ℂ) := by
    change ((c.character (GeneralLinear.determinant
      (Unitary.toUnits minusOneOrthogonal)) : ℂˣ) : ℂ) = _
    rw [toUnits_minusOneOrthogonal, determinant_scalarUnit]
  have hsub : (⟨_, hf⟩ : realStandardKFinite 1 [RealBlock.character c]) =
      ((c.character (-1) : ℂˣ) : ℂ) • f0 := by
    apply Subtype.ext
    change Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 1 ℝ)
      (k0 : Langlands.GeneralLinear 1 ℝ) (characterFunction c) =
        ((c.character (-1) : ℂˣ) : ℂ) • characterFunction c
    rw [rightTranslation_characterFunction, hdet]
  have h1 : ((c.character (-1) : ℂˣ) : ℂ) • A f0 = ε • A f0 := by
    calc ((c.character (-1) : ℂˣ) : ℂ) • A f0
        = A (((c.character (-1) : ℂˣ) : ℂ) • f0) := (map_smul A _ _).symm
      _ = A ⟨_, hf⟩ := congrArg A hsub.symm
      _ = S.realPlaceCompactRepresentation v
          ⟨((k0 : Langlands.GeneralLinear 1 ℝ) : Matrix (Fin 1) (Fin 1) ℝ), k0.2⟩ (A f0) := hAk
      _ = S.realPlaceCompactRepresentation v minusOneOrthogonal (A f0) :=
        congrArg (fun k => S.realPlaceCompactRepresentation v k (A f0)) hk0eq
      _ = ε • A f0 := hε' (A f0)
  have hεc := eq_of_smul_eq_smul hx0 h1
  exact (hε' f).trans (congrArg (fun z : ℂ => z • f) hεc.symm)

set_option maxHeartbeats 1000000 in
attribute [local instance 100] LieRing.ofAssociativeRing in
/-- On an irreducible rank-one realization the Lie operator of every `X ∈ ℂ ⊗ 𝔤𝔩₁(ℝ)` at a
real place is a scalar. -/
theorem exists_realPlaceLieAction_eq_smul (S : OperatorRealization F 1) (hS : S.IsIrreducible)
    (v : RP) (X : ℂ ⊗[ℝ] Matrix (Fin 1) (Fin 1) ℝ) :
    ∃ lam : ℂ, ∀ f : S.Space, S.realPlaceLieAction v X f = lam • f := by
  have key : ∀ a : EnvelopingAlgebra F 1, ∃ lam : ℂ, ∀ f : S.Space,
      S.envelopingAction a f = lam • f := fun a => exists_envelopingAction_eq_smul S hS a
  obtain ⟨lam, hlam⟩ := key (envelopingGenerator F 1 (realPlaceComplexLieInclusion F 1 v X))
  exact ⟨lam, fun f => (S.realPlaceLieAction_apply v X f).trans (hlam f)⟩

set_option maxHeartbeats 1000000 in
/-- On an irreducible rank-one realization with the real-place parameter `[character c]` at
`v`, the Lie operator of `1 ∈ 𝔤𝔩₁(ℝ)` at `v` acts by the exponent of `c`. -/
theorem hasRealPlaceParameter_lie (S : OperatorRealization F 1) (hS : S.IsIrreducible)
    (v : RP) (c : RealCharacterData)
    (hp : S.HasRealPlaceParameter v [RealBlock.character c]) (f : S.Space) :
    S.realPlaceLieAction v ((1 : ℂ) ⊗ₜ[ℝ] (1 : Matrix (Fin 1) (Fin 1) ℝ)) f =
      c.exponent • f := by
  obtain ⟨-, A, hA, -, hL⟩ := hp
  let f0 : realStandardKFinite 1 [RealBlock.character c] :=
    ⟨characterFunction c, characterFunction_mem_kFinite c⟩
  have hx0 : A f0 ≠ 0 := parameter_characterFunction_ne_zero S c A hA
  obtain ⟨lam, hlam'⟩ := exists_realPlaceLieAction_eq_smul S hS v
    ((1 : ℂ) ⊗ₜ[ℝ] (1 : Matrix (Fin 1) (Fin 1) ℝ))
  have hL0 := hL 1 f0
  obtain ⟨hf, hAX⟩ := hL0
  have hsub : (⟨_, hf⟩ : realStandardKFinite 1 [RealBlock.character c]) = c.exponent • f0 :=
    Subtype.ext (rightDerivative_characterFunction c)
  have h1 : c.exponent • A f0 = lam • A f0 := by
    calc c.exponent • A f0 = A (c.exponent • f0) := (map_smul A _ _).symm
      _ = A ⟨_, hf⟩ := congrArg A hsub.symm
      _ = S.realPlaceLieAction v ((1 : ℂ) ⊗ₜ[ℝ] (1 : Matrix (Fin 1) (Fin 1) ℝ)) (A f0) := hAX
      _ = lam • A f0 := hlam' (A f0)
  have hlamc := eq_of_smul_eq_smul hx0 h1
  exact (hlam' f).trans (congrArg (fun z : ℂ => z • f) hlamc.symm)

/-- In a nonzero product `p * z = z` forces `p = 1`. -/
theorem eq_one_of_mul_eq_self {p z : ℂ} (h : p * z = z) (hz : z ≠ 0) : p = 1 :=
  mul_right_cancel₀ hz (h.trans (one_mul z).symm)

/-- A contragredient pairing of a nonzero realization pairs some vector nontrivially with a
given nonzero vector. -/
theorem exists_pairing_ne_zero {S Sd : OperatorRealization F 1}
    {B : S.Space →ₗ[ℂ] Sd.Space →ₗ[ℂ] ℂ} (hinj : Function.Injective B.flip) {y : Sd.Space}
    (hy : y ≠ 0) : ∃ x, B x y ≠ 0 := by
  have hBy : B.flip y ≠ 0 := fun h => hy (hinj (h.trans (map_zero B.flip).symm))
  by_contra h
  push Not at h
  exact hBy (LinearMap.ext fun x => h x)

/-- The parameter of a contragredient of an irreducible rank-one realization has the same
parity. -/
theorem contragredient_parity_rankOne {S Sd : OperatorRealization F 1}
    (hS : S.IsIrreducible) (hSd : Sd.IsIrreducible)
    (hc : OperatorRealization.IsContragredientOf Sd S) (v : RP) (c cd : RealCharacterData)
    (hp : S.HasRealPlaceParameter v [RealBlock.character c])
    (hpd : Sd.HasRealPlaceParameter v [RealBlock.character cd]) :
    cd.parity = c.parity := by
  obtain ⟨y, hy⟩ := hasRealPlaceParameter_nontrivial Sd v cd hpd
  obtain ⟨B, ⟨-, hBk, -⟩, -, hinj, -⟩ := hc
  obtain ⟨x, hx⟩ := exists_pairing_ne_zero hinj hy
  have hk := hBk (realPlaceCompactInclusion F 1 v minusOneOrthogonal) x y
  have h2 : B (((c.character (-1) : ℂˣ) : ℂ) • x) (((cd.character (-1) : ℂˣ) : ℂ) • y) =
      B x y :=
    (congrArg₂ (fun a b => B a b) (hasRealPlaceParameter_compact S hS v c hp x).symm
      (hasRealPlaceParameter_compact Sd hSd v cd hpd y).symm).trans hk
  have h3 := eq_one_of_mul_eq_self ((bilinear_smul_smul B _ _ x y).symm.trans h2) hx
  rw [character_neg_one, character_neg_one] at h3
  have key : ∀ p q : Fin 2, (-1 : ℂ) ^ p.val * (-1 : ℂ) ^ q.val = 1 → q = p := by
    intro p q h
    fin_cases p <;> fin_cases q <;> first | rfl | norm_num at h
  exact key _ _ h3

/-- The parameter of a contragredient of an irreducible rank-one realization has the negated
exponent. -/
theorem contragredient_exponent_rankOne {S Sd : OperatorRealization F 1}
    (hS : S.IsIrreducible) (hSd : Sd.IsIrreducible)
    (hc : OperatorRealization.IsContragredientOf Sd S) (v : RP) (c cd : RealCharacterData)
    (hp : S.HasRealPlaceParameter v [RealBlock.character c])
    (hpd : Sd.HasRealPlaceParameter v [RealBlock.character cd]) :
    cd.exponent = -c.exponent := by
  obtain ⟨y, hy⟩ := hasRealPlaceParameter_nontrivial Sd v cd hpd
  obtain ⟨B, ⟨-, -, hBl⟩, -, hinj, -⟩ := hc
  obtain ⟨x, hx⟩ := exists_pairing_ne_zero hinj hy
  have hl := hBl (realPlaceLieInclusion F 1 v 1) x y
  have e1 : S.lieAction (realPlaceLieInclusion F 1 v 1) x = c.exponent • x :=
    hasRealPlaceParameter_lie S hS v c hp x
  have e2 : Sd.lieAction (realPlaceLieInclusion F 1 v 1) y = cd.exponent • y :=
    hasRealPlaceParameter_lie Sd hSd v cd hpd y
  have h2 : B (c.exponent • x) y + B x (cd.exponent • y) = 0 :=
    (congrArg₂ (· + ·) (congrArg (fun z => B z y) e1)
      (congrArg (fun z => B x z) e2)).symm.trans hl
  have h5 : c.exponent * B x y + cd.exponent * B x y = 0 :=
    (congrArg₂ (· + ·) (bilinear_smul_left B _ x y) (bilinear_smul_right B _ x y)).symm.trans h2
  have h4 := (mul_eq_zero.mp ((add_mul _ _ _).trans h5)).resolve_right hx
  exact eq_neg_of_add_eq_zero_right h4

end Realization

/-! ### Global Whittaker restrictions of cuspidal realizations of `GL₁` -/

section Whittaker

local instance realRankZeroParamSchemeAffine (n : ℕ) {F : Type u} [Field F] :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance realRankZeroParamSchemeSmooth (n : ℕ) {F : Type u} [Field F] :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable {F : Type u} [Field F] [NumberField F]

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}

local instance realRankZeroWhitRationalAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance realRankZeroWhitContinuousAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance realRankZeroWhitSmoothAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance realRankZeroWhitFormsAddCommGroup (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance realRankZeroWhitStableAddCommGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance realRankZeroWhitRealizationAddCommGroup (n : ℕ) (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

variable [CompactSpace (AdeleQuotient F)]

omit [CompactSpace (AdeleQuotient F)] in
theorem realPlaceAdelic_apply (v : RP) (g : Matrix.GeneralLinearGroup (Fin 1) ℝ) :
    realPlaceAdelic F v g =
      AdelicGL.ofInfinite F 1 ((archimedeanGLCoordinates F 1).symm (realPlaceGL F 1 v g)) := rfl

/-- The adelic matrix of `ι_v(g) a` is `(1, a) · ι_v(g)`. -/
theorem adelicEquiv_realPlacePoint_mul_finitePoint (v : RP)
    (g : Matrix.GeneralLinearGroup (Fin 1) ℝ) (a : FiniteAdelicGL F 1) :
    GeneralLinearGroupPoints.adelicEquiv F 1 (realPlacePoint F 1 v g * finitePoint F 1 a) =
      AdelicGL.pair F 1 1 a * realPlaceAdelic F v g := by
  have h1 : GeneralLinearGroupPoints.adelicEquiv F 1 (realPlacePoint F 1 v g) =
      AdelicGL.pair F 1 ((archimedeanGLCoordinates F 1).symm (realPlaceGL F 1 v g)) 1 := by
    simp only [realPlacePoint, adelicPoint, MulEquiv.apply_symm_apply]
  have h2 : GeneralLinearGroupPoints.adelicEquiv F 1 (finitePoint F 1 a) =
      AdelicGL.pair F 1 1 a := by
    simp only [finitePoint, adelicPoint, MulEquiv.apply_symm_apply, map_one]
  rw [map_mul, h1, h2, realPlaceAdelic_apply]
  apply AdelicGL.ext_infinite_finite F 1
  · rw [map_mul, map_mul, AdelicGL.infinite_pair, AdelicGL.infinite_pair,
      AdelicGL.infinite_ofInfinite, mul_one, one_mul]
  · rw [map_mul, map_mul, AdelicGL.finite_pair, AdelicGL.finite_pair,
      AdelicGL.finite_ofInfinite, mul_one, one_mul]

/-- A real-place restriction of a global Whittaker function of a cuspidal realization of `GL₁`
on which `-1 ∈ O(1)` acts by `χ_c(-1)` and the Lie operator of `1` by the exponent of `c` is a
multiple of `χ_c ∘ det`. -/
theorem isRealPlaceWhittaker_rankZero {T : CuspidalOperatorRealization F 0}
    {χ : AddChar (Adeles F) ℂ} {v : RP} {W : Langlands.GeneralLinear (0 + 1) ℝ → ℂ}
    (hW : IsRealPlaceWhittaker F T χ v W) (c : RealCharacterData)
    (hε : ∀ f : T.Space, T.realization.realPlaceCompactRepresentation v minusOneOrthogonal f =
      ((c.character (-1) : ℂˣ) : ℂ) • f)
    (hμ : ∀ f : T.Space, T.realization.realPlaceLieAction v
      ((1 : ℂ) ⊗ₜ[ℝ] (1 : Matrix (Fin 1) (Fin 1) ℝ)) f = c.exponent • f) :
    ∃ C : ℂ, ∀ g, W g = C * (c.character (GeneralLinear.determinant g) : ℂ) := by
  obtain ⟨x, a, rfl⟩ := hW
  refine ⟨ContinuousRationalFunctions.evaluate F 1 (T.realization.toContinuous x)
    (AdelicGL.pair F 1 1 a), fun g => ?_⟩
  calc cuspWhittaker F T χ x (realPlacePoint F (0 + 1) v g * finitePoint F (0 + 1) a)
      = cuspFunction F T x (realPlacePoint F 1 v g * finitePoint F 1 a) :=
        congrFun (cuspWhittaker_rankZero T χ x) _
    _ = ContinuousRationalFunctions.evaluate F 1 (T.realization.toContinuous x)
          (GeneralLinearGroupPoints.adelicEquiv F 1 (realPlacePoint F 1 v g * finitePoint F 1 a)) :=
        RealPlaceWhittaker.cuspFunction_eq_evaluate F T x _
    _ = ContinuousRationalFunctions.evaluate F 1 (T.realization.toContinuous x)
          (AdelicGL.pair F 1 1 a * realPlaceAdelic F v g) :=
        congrArg (ContinuousRationalFunctions.evaluate F 1 (T.realization.toContinuous x))
          (adelicEquiv_realPlacePoint_mul_finitePoint v g a)
    _ = ((c.character (GeneralLinear.determinant g) : ℂˣ) : ℂ) *
          ContinuousRationalFunctions.evaluate F 1 (T.realization.toContinuous x)
            (AdelicGL.pair F 1 1 a) :=
        evaluate_mul_realPlaceAdelic T.realization v c hε hμ g x _
    _ = _ := mul_comm _ _

end Whittaker

end Langlands.Global.RankinSelbergGlobal.RealRankZero
