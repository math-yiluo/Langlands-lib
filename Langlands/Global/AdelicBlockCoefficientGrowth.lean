import Langlands.Global.AdelicBlockParabolicHeight
import Langlands.Global.AdelicFiniteTranslateHeightReduction
import Langlands.Automorphic.GeneralLinearGrowthIndependence
import Langlands.Global.AdelicBlockScalarSections

/-! # Full adelic growth of realized Levi coefficients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Langlands.Automorphic.OperatorRealization

open Langlands.Global Langlands.Global.GeneralLinearGroupPoints
open GroupSchemeFunctions

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
local notation "std" => GroupScheme.MatrixRepresentation.standard (Fin n) (CommRingCat.of F)

local instance blockCoefficientGLAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

/-- A vector of an actual general-linear operator realization has a
polynomial bound on the full adelic group. -/
theorem evaluate_polynomialGrowth (hn : 0 < n) (S : OperatorRealization F n) (f : S.Space) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ e : ℕ, ∀ g : AdelicGL F n,
      ‖ContinuousRationalFunctions.evaluate F n (S.toContinuous f) g‖ ≤
        C * AdelicMatrixHeight.height F n g ^ e := by
  let x := S.toContinuous f
  let y := (continuousGeneralLinearEquiv F n).symm x
  have hxy : continuousGeneralLinearEquiv F n y = x := (continuousGeneralLinearEquiv F n).apply_symm_apply x
  have hxfin : x ∈ Langlands.Automorphic.finiteSmoothSubrepresentation F n := f.val.val.property.2
  have hyfin : y ∈ GroupSchemeFunctions.finiteSmoothSubrepresentation F GLG :=
    (continuousGeneralLinearEquiv_mem_finiteSmooth F n y).mp (hxy.symm ▸ hxfin)
  let f₀ := stableAutomorphicInclusion F n f.val
  have hxgrowth : Langlands.Automorphic.HasPolynomialGrowth F n x := by
    have h := (mem_automorphicSubrepresentation F n f₀.val).mp f₀.property
    exact h.2.2.2
  have hcl : GroupScheme.IsClosedSubgroup std := by
    change IsClosedImmersion (𝟙 (GLG).X.left)
    infer_instance
  have hygrowth : GroupSchemeFunctions.HasPolynomialGrowth F GLG std y :=
    (GroupSchemeFunctions.mem_polynomialGrowthSubrepresentation F GLG std y).mp
      ((continuousGeneralLinearEquiv_mem_polynomialGrowth F n y).mp
        (hxy.symm ▸ (mem_polynomialGrowthSubrepresentation F n x).mpr hxgrowth))
  have hy := (adelicSliceModerateGrowthStatement_of_rationalHeightReduction
    RepresentationGrowth.adelicRationalHeightReduction_of_finiteRightSiegelCover)
    F GLG std (GroupScheme.isConnectedReductive_generalLinear F (Fin n)) hcl hn y hyfin hygrowth
  obtain ⟨C, hC, e, h⟩ := (hasAdelicModerateGrowth_iff F GLG std hn y).mp hy
  refine ⟨max 1 C, le_max_left _ _, e, fun g => ?_⟩
  let a := (adelicHomeomorph F n).symm g
  have hga : adelicHomeomorph F n a = g := (adelicHomeomorph F n).apply_symm_apply _
  have he := evaluate_continuousGeneralLinearEquiv_at_point F n y a
  rw [hxy, hga] at he
  have ha := h a
  rw [RepresentationGrowth.adelicHeight_standard, hga, ← he] at ha
  exact ha.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
    (pow_nonneg (zero_le_one.trans (AdelicMatrixHeight.one_le_height F n hn g)) _))

end Langlands.Automorphic.OperatorRealization

namespace Langlands.Global.AdelicBlockScalarSections

open Langlands.Automorphic Langlands.GeneralLinear
open AdelicBlockParabolic AdelicMatrixHeight

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

/-- The polynomial growth algebra for the product of the block heights. -/
abbrev leviPolynomialGrowth : Subalgebra ℂ (FullLevi F B → ℂ) :=
  polynomialGrowthAlgebra (blockProductHeight B F) (one_le_blockProductHeight B F)

/-- Realized Levi coefficients are of polynomial growth in the product of
the block heights. -/
theorem coefficientValues_le_leviPolynomialGrowth :
    coefficientValues F B S ≤ (leviPolynomialGrowth F B).toSubmodule := by
  apply Submodule.span_le.mpr
  rintro φ ⟨f, rfl⟩
  let A := leviPolynomialGrowth F B
  let s (i : Fin B.length) (m : FullLevi F B) :=
    ContinuousRationalFunctions.evaluate F (B.size i) ((S i).toContinuous (f i)) (m i)
  have hs (i : Fin B.length) : s i ∈ A := by
    obtain ⟨C, hC, e, h⟩ := (S i).evaluate_polynomialGrowth F _ (B.positive i) (f i)
    refine ⟨C, hC, e, fun m => (h (m i)).trans ?_⟩
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans (one_le_height F _ (B.positive i) _))
        (blockHeight_le_blockProductHeight B F m i) e) (zero_le_one.trans hC)
  change blockCoefficient F B S f ∈ A
  have he : blockCoefficient F B S f = ∏ i, s i := by
    funext m
    simp only [blockCoefficient, Finset.prod_apply, s]
  rw [he]
  exact A.prod_mem fun i _ => hs i

end Langlands.Global.AdelicBlockScalarSections
