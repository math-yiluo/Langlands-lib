import Langlands.LocalFactor.RealBlockRankOne
import Langlands.Representation.Archimedean.RealRankZeroStandardModule
import Langlands.Representation.Archimedean.PrincipalSeriesExtension
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Real standard modules in rank one

The actual compact-finite standard module of a single real character is
one-dimensional, by evaluation at the identity.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Matrix Matrix.Norms.Operator

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealRankOneStandardModule

abbrev G := Langlands.GeneralLinear 1 ℝ

abbrev KF (d : RealCharacterData) :=
  kFiniteFunctions (realStandardModule 1 [.character d]) (unitaryCompact ℝ 1)

/-- The character of `GL₁(ℝ)` obtained from the given real character. -/
def characterVector (d : RealCharacterData) (g : G) : ℂ :=
  (d.character (Matrix.GeneralLinearGroup.det g) : ℂ)

@[simp]
theorem characterVector_one (d : RealCharacterData) : characterVector d 1 = 1 := by
  simp [characterVector]

theorem characterVector_mul (d : RealCharacterData) (g h : G) :
    characterVector d (g * h) = characterVector d g * characterVector d h := by
  simp [characterVector, map_mul]

/-- Every invertible one-by-one matrix is diagonal. -/
theorem diagonal_det (g : G) :
    (Iwasawa.diagonalUnits (fun _ : Fin 1 => Matrix.GeneralLinearGroup.det g) : G) = g := by
  apply Units.ext
  ext i j
  fin_cases i
  fin_cases j
  simp [Iwasawa.diagonalUnits_val]

/-- The upper unipotent subgroup in rank one is trivial. -/
theorem upperUnipotent_eq_one (u : upperUnipotent 1 ℝ) : (u : G) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i
  fin_cases j
  exact u.2.2 0

theorem principalSeriesCharacter_eq (d : RealCharacterData) (a : Fin 1 → ℝˣ) :
    principalSeriesCharacter ℝ 1 (realPositionCharacter [.character d]) a =
      (d.character (a 0) : ℂ) := by
  simp [principalSeriesCharacter, realPositionCharacter]

/-- Evaluation at the identity determines a principal-series function in
rank one. -/
theorem eval_formula (d : RealCharacterData) {f : G → ℂ}
    (hf : f ∈ principalSeries ℝ 1 (realPositionCharacter [.character d])) (g : G) :
    f g = characterVector d g * f 1 := by
  have h := hf.2 (fun _ : Fin 1 => Matrix.GeneralLinearGroup.det g) 1 1
  simpa only [OneMemClass.coe_one, mul_one, diagonal_det,
    principalSeriesCharacter_eq, characterVector] using h

/-- The character vector is smooth, using the signed-power expression of
the given character away from determinant zero. -/
theorem contMDiff_characterVector (d : RealCharacterData) :
    ContMDiff (matrixModel ℝ 1) 𝓘(ℝ, ℂ) ∞ (characterVector d) := by
  refine contMDiff_of_contDiffOn
    (ψ := fun y : Matrix (Fin 1) (Fin 1) ℝ =>
      (((y.det / |y.det| : ℝ) : ℂ) ^ d.parity.val) *
        ((|y.det| : ℝ) : ℂ) ^ d.exponent) ?_ (fun g => d.character_eq _)
  intro y hy
  have hdet : y.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det y).mp hy).ne_zero
  have hd : ContDiff ℝ ∞ (fun y : Matrix (Fin 1) (Fin 1) ℝ => y.det) :=
    PrincipalSeriesExtension.contDiff_det_comp fun i j =>
      PrincipalSeriesExtension.contDiff_entry i j
  have ha : ContDiffAt ℝ ∞ (fun y : Matrix (Fin 1) (Fin 1) ℝ => |y.det|) y :=
    (contDiffAt_abs hdet).comp y hd.contDiffAt
  have hs := (Complex.ofRealCLM.contDiff.contDiffAt.comp y
    (hd.contDiffAt.div ha (abs_ne_zero.mpr hdet))).pow d.parity.val
  exact (hs.mul (PrincipalSeriesExtension.contDiffAt_ofReal_cpow ha
    (abs_pos.mpr hdet) d.exponent)).contDiffWithinAt

/-- The nonzero character vector satisfies all standard-module conditions. -/
theorem characterVector_mem_standard (d : RealCharacterData) :
    characterVector d ∈ realStandardModule 1 [.character d] := by
  refine ⟨⟨contMDiff_characterVector d, ?_⟩, ?_⟩
  · intro a u g
    rw [upperUnipotent_eq_one, mul_one, characterVector_mul, principalSeriesCharacter_eq]
    congr 1
    apply congrArg (fun x : ℝˣ => (d.character x : ℂ))
    apply Units.ext
    simp [Iwasawa.diagonalUnits_val]
  · intro p e hp
    cases p with
    | zero => simp [realInducedBlockAt] at hp
    | succ p => simp [realInducedBlockAt] at hp

/-- Right translates of the character vector span one line. -/
theorem characterVector_mem (d : RealCharacterData) : characterVector d ∈ KF d := by
  refine ⟨characterVector_mem_standard d, (mem_kFiniteVectors_iff _ _ _).mpr ?_⟩
  apply Submodule.finiteDimensional_of_le
    (S₂ := Submodule.span ℂ {characterVector d})
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  have h : Whittaker.rightTranslation ℂ G (k : G) (characterVector d) =
      characterVector d k • characterVector d := by
    funext g
    change characterVector d (g * k) = characterVector d k * characterVector d g
    rw [characterVector_mul, mul_comm]
  change Whittaker.rightTranslation ℂ G (k : G) (characterVector d) ∈
    Submodule.span ℂ {characterVector d}
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

/-- Evaluation at the identity identifies the actual compact-finite
standard module with `ℂ`. -/
def evalEquiv (d : RealCharacterData) : KF d ≃ₗ[ℂ] ℂ where
  toFun f := (f : G → ℂ) 1
  invFun c := ⟨c • characterVector d, (KF d).smul_mem c (characterVector_mem d)⟩
  left_inv f := by
    apply Subtype.ext
    funext g
    change (f : G → ℂ) 1 * characterVector d g = (f : G → ℂ) g
    calc
      (f : G → ℂ) 1 * characterVector d g =
          characterVector d g * (f : G → ℂ) 1 := mul_comm _ _
      _ = (f : G → ℂ) g := (eval_formula d f.2.1.1 g).symm
  right_inv c := by simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every complex subspace of a one-character standard module is zero or
the whole space. -/
theorem submodule_eq_bot_or_top (d : RealCharacterData) (U : Submodule ℂ (KF d)) :
    U = ⊥ ∨ U = ⊤ := by
  by_cases hU : U = ⊥
  · exact Or.inl hU
  · right
    obtain ⟨f, hfU, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
    have hf1 : evalEquiv d f ≠ 0 := by
      intro h
      apply hf
      apply (evalEquiv d).injective
      simpa using h
    refine eq_top_iff.mpr fun g _ => ?_
    have hg : g = (evalEquiv d g / evalEquiv d f) • f := by
      apply (evalEquiv d).injective
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hf1]
    rw [hg]
    exact U.smul_mem _ hfU

/-- The actual standard module of a real character is irreducible. -/
theorem isIrreducible (d : RealCharacterData) :
    IsIrreducibleGKModule (realStandardRep 1 [.character d])
      (realStandardLie 1 [.character d]) := by
  refine ⟨(evalEquiv d).symm.injective.nontrivial,
    fun U _ _ => submodule_eq_bot_or_top d U⟩

/-- A list of real blocks of total rank one consists of one character. -/
theorem eq_singleton_of_realRank_eq_one (ds : List RealBlock) (h : realRank ds = 1) :
    ∃ d : RealCharacterData, ds = [.character d] :=
  Langlands.Global.RankinSelbergGlobal.RealRankZero.eq_singleton_of_realRank_eq_one h

end RealRankOneStandardModule

/-- Irreducibility of every real standard module of total rank one. -/
def RealRankOneStandardIrreducibleStatement : Prop :=
  ∀ ds : List RealBlock, realRank ds = 1 →
    IsIrreducibleGKModule (realStandardRep 1 ds) (realStandardLie 1 ds)

/-- Rank one reduces to the one-dimensional standard module of a character. -/
theorem realRankOneStandardIrreducible : RealRankOneStandardIrreducibleStatement := by
  intro ds h
  obtain ⟨d, rfl⟩ := RealRankOneStandardModule.eq_singleton_of_realRank_eq_one ds h
  exact RealRankOneStandardModule.isIrreducible d

end Langlands.Archimedean
