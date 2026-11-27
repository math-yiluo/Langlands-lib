import Langlands.Global.AdelicSiegelConstantTermGrowth
import Langlands.Global.AdelicExponentOrbitSpan
import Langlands.Global.AdelicLeadingCuspidalPairing

/-! # Siegel chamber bounds for split-component orbit vectors -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints AdelicSiegelFactors RepresentationGrowth

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)
  {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (j : T₀ ⟶ fam.T)
  {N : ℕ} (rho : MatrixRepresentation G (Fin N))

local notation "Idx" => StandardIndex F G fam.i fam.ν
local notation "A" => AdelicGroupPoints F G
local notation "Torus" => PositiveRealTorus.intrinsicSubgroup F T₀
local notation "aG" => positiveMap F G fam.T fam.i T₀ j
local notation "δ" => siegelModulus F G fam.T fam.i fam.ν T₀ j
local notation "σ" => (fun a : Torus => 1 + Real.log (adelicHeight F G rho (aG a)))
local notation "Growth" => fam.HasSiegelChamberGrowth j rho

attribute [local instance] positiveSplitComponentCommGroup

/-- A torus weight times a power of the logarithmic height bounds the function on the weak
chamber with compact right factors. -/
def HasWeightedSiegelChamberGrowth (B : Torus → ℝ) (f : A → ℂ) : Prop :=
  ∀ (t : ℝ≥0ˣ) (Ω : Set A), IsCompact Ω →
    ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (a : Torus),
      a ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ fam.T j G fam.i fam.ν t → ∀ w ∈ Ω,
        ‖f (aG a * w)‖ ≤ C * B a * (σ a) ^ m

/-- Weighted logarithmic Siegel chamber growth is closed under complex linear combinations. -/
def weightedSiegelChamberGrowthSubmodule (hN : 0 < N) {B : Torus → ℝ}
    (hB : ∀ a, 0 ≤ B a) : Submodule ℂ (A → ℂ) where
  carrier := {f | fam.HasWeightedSiegelChamberGrowth j rho B f}
  zero_mem' := fun _ _ _ => ⟨0, 0, le_rfl, by simp⟩
  add_mem' {f g} hf hg := by
    intro t Ω hΩ
    obtain ⟨m, C, hC, hF⟩ := hf t Ω hΩ
    obtain ⟨n, D, hD, hG⟩ := hg t Ω hΩ
    refine ⟨max m n, C + D, add_nonneg hC hD, fun a ha w hw => ?_⟩
    have hσ : 1 ≤ σ a :=
      le_add_of_nonneg_right (Real.log_nonneg (one_le_adelicHeight F G rho hN (aG a)))
    calc
      ‖(f + g) (aG a * w)‖ ≤ ‖f (aG a * w)‖ + ‖g (aG a * w)‖ := norm_add_le _ _
      _ ≤ C * B a * (σ a) ^ m + D * B a * (σ a) ^ n :=
        add_le_add (hF a ha w hw) (hG a ha w hw)
      _ ≤ (C * B a + D * B a) * (σ a) ^ max m n := by
        rw [add_mul]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hσ (le_max_left _ _))
            (mul_nonneg hC (hB a)))
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hσ (le_max_right _ _))
            (mul_nonneg hD (hB a)))
      _ = _ := by simp only [add_mul]
  smul_mem' z f hf := by
    intro t Ω hΩ
    obtain ⟨m, C, hC, hBound⟩ := hf t Ω hΩ
    refine ⟨m, ‖z‖ * C, mul_nonneg (norm_nonneg _) hC, fun a ha w hw => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (by simpa only [mul_assoc] using hBound a ha w hw) (norm_nonneg _)

/-- The chamber growth weighted by the square root of the Siegel modulus. -/
abbrev siegelChamberGrowthSubmodule (hN : 0 < N) : Submodule ℂ (A → ℂ) :=
  fam.weightedSiegelChamberGrowthSubmodule j rho hN (B := fun a => Real.sqrt (δ a))
    (fun _ => Real.sqrt_nonneg _)

/-- Fixed left split-component shifts commute with the Siegel torus and only enlarge the
compact right factor. -/
theorem hasWeightedSiegelChamberGrowth_splitComponentTranslate (J : Idx)
    {B : Torus → ℝ} {f : A → ℂ} (hf : fam.HasWeightedSiegelChamberGrowth j rho B f)
    (b : fam.positiveSplitComponent J) :
    fam.HasWeightedSiegelChamberGrowth j rho B (fam.splitComponentRepresentation J b f) := by
  let x := map F (fam.P J) G (fam.p J) b.val
  intro t Ω hΩ
  obtain ⟨m, C, hC, hBound⟩ := hf t ((fun w => x * w) '' Ω)
    (hΩ.image (continuous_const.mul continuous_id))
  refine ⟨m, C, hC, fun a ha w hw => ?_⟩
  have hTor (a : Torus) :
      aG a = map F (fam.M J) G (fam.l J ≫ fam.p J)
        (map F T₀.toGrp (fam.M J) (CommGroupScheme.groupHom j ≫ fam.torus J) a.val) := by
    rw [map_comp_apply_of_hom]
    change map F T₀.toGrp G (CommGroupScheme.groupHom j ≫ fam.i) a.val =
      map F T₀.toGrp G ((CommGroupScheme.groupHom j ≫ fam.torus J) ≫ fam.l J ≫ fam.p J) a.val
    rw [Category.assoc, fam.torus_comp]
  have hComm : Commute x (aG a) := by
    rw [hTor]
    exact fam.commute_positiveSplitComponent_levi J b _
  change ‖f (x * (aG a * w))‖ ≤ _
  rw [← mul_assoc, hComm.eq, mul_assoc]
  exact hBound a ha (x * w) ⟨w, hw, rfl⟩

/-- Acting by a complex group-algebra element preserves a nonnegative torus weight. -/
theorem hasWeightedSiegelChamberGrowth_shiftAlgHom (hN : 0 < N) (J : Idx)
    {B : Torus → ℝ} (hB : ∀ a, 0 ≤ B a)
    {f : A → ℂ} (hf : fam.HasWeightedSiegelChamberGrowth j rho B f)
    (D : MonoidAlgebra ℂ (fam.positiveSplitComponent J)) :
    fam.HasWeightedSiegelChamberGrowth j rho B (fam.shiftAlgHom J D f) := by
  exact fam.shiftAlgHom_mem (fam.weightedSiegelChamberGrowthSubmodule j rho hN hB)
    (fun b _ hg => fam.hasWeightedSiegelChamberGrowth_splitComponentTranslate j rho J hg b) D f hf

/-- Every vector in the span of positive split-component translates inherits the
logarithmic Siegel chamber growth of the generating function. -/
theorem hasSiegelChamberGrowth_of_mem_splitComponentOrbitSpan (hN : 0 < N) (J : Idx)
    {f w : A → ℂ} (hf : Growth f) (hw : w ∈ fam.splitComponentOrbitSpan J f) :
    Growth w := by
  have hle : fam.splitComponentOrbitSpan J f ≤ fam.siegelChamberGrowthSubmodule j rho hN := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b, rfl⟩
    exact fam.hasWeightedSiegelChamberGrowth_splitComponentTranslate j rho J hf b
  exact hle hw

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open GroupScheme AdelicGroupPoints PositiveRealTorus

/-- A nonnegative torus weight in a logarithmic chamber bound is preserved
by the complex group algebra of the positive split component. -/
def AdelicSiegelOrbitGrowthStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G)
    (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ fam.T)
    {N : ℕ} (rho : MatrixRepresentation G (Fin N)), 0 < N →
    ∀ (J : StandardIndex F G fam.i fam.ν) (B : intrinsicSubgroup F T₀ → ℝ),
      (∀ a, 0 ≤ B a) →
    ∀ (f : AdelicGroupPoints F G → ℂ), fam.HasWeightedSiegelChamberGrowth j rho B f →
    ∀ D : MonoidAlgebra ℂ (fam.positiveSplitComponent J),
      fam.HasWeightedSiegelChamberGrowth j rho B (fam.shiftAlgHom J D f)

theorem adelicSiegelOrbitGrowth : AdelicSiegelOrbitGrowthStatement := by
  intro F _ _ G _ _ _ fam T₀ j N rho hN J B hB f hf D
  exact fam.hasWeightedSiegelChamberGrowth_shiftAlgHom j rho hN J hB hf D

end Langlands.Global
