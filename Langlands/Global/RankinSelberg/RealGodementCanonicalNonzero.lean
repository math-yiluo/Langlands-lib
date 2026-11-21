import Langlands.Global.RankinSelberg.RealGodementCanonicalModel
import Langlands.Global.RankinSelberg.RealGodementPolynomialTest
import Langlands.Representation.Archimedean.RealRankOneStandardModule

/-! # Nonvanishing of the canonical real Jacquet maps -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open MeasureTheory
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open RealGodementProfiles RealJacquetFrobenius

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

/-- At every exponent vector a K-finite real character section has nonzero
canonical Jacquet image. -/
def RealGodementCanonicalNonzeroStatement : Prop :=
  ∀ (r : ℕ) (a : ℝˣ) (p : Fin (r + 1) → Fin 2) (z : Fin (r + 1) → ℂ),
    ∃ f : Automorphic.realStandardKFinite (r + 1) (characterList p z), canonicalJacquetMap a p z f ≠ 0

theorem realGodementCanonicalNonzero : RealGodementCanonicalNonzeroStatement := by
  intro r
  induction r with
  | zero =>
    intro a p z
    let d := charData (p 0) (z 0)
    have hList : characterList p z = [.character d] := by
      simp only [characterList, List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil, d]
    let f : Automorphic.realStandardKFinite 1 (characterList p z) :=
      ⟨RealRankOneStandardModule.characterVector d,
        hList.symm ▸ RealRankOneStandardModule.characterVector_mem d⟩
    refine ⟨f, ?_⟩
    have hz : z ∈ realSpectralChamber 0 := fun i => Fin.elim0 i
    rw [canonicalJacquetMap_agrees a p hz f]
    intro h
    have he := congrFun h (1 : Langlands.GeneralLinear 1 ℝ)
    rw [additiveJacquetIntegral_rankOne] at he
    change RealRankOneStandardModule.characterVector d 1 = 0 at he
    exact one_ne_zero ((RealRankOneStandardModule.characterVector_one d).symm.trans he)
  | succ t ih =>
    intro a p z
    let p' (i : Fin (t + 1)) := p i.succ
    let z' (i : Fin (t + 1)) := z i.succ
    obtain ⟨f, hf⟩ := ih a p' z'
    let W := canonicalJacquetMap a p' z' f
    let D := (nonempty_realQuotientMeasureData t a).some
    let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
    have hGrowth := RealUniformWhittaker.uniformDerivativeGrowth_of_mem_model
      (canonicalJacquetMap_mem_uniformModel a p' z' f)
    obtain ⟨S, hS, hRank, Φ, hSupport, hFinite, hNZ⟩ := realGodementPolynomialTest D a W
      (canonicalJacquetMap_derivative_mem_regularFunctions a p' z' f) hGrowth hf (p 0) (z 0)
    let φ := compactRestriction f.val
    have hφ : IsCompactProfile p' φ := isCompactProfile_compactRestriction f.property
    obtain ⟨E, hE, hConv, C, hLower, hTest⟩ :=
      realGodementFiniteCompactTest D.groupHaar p φ hφ S hS hRank Φ hSupport hFinite
    let := hE
    have hLowerEval : canonicalJacquetFamily a C.lower_profile z' = W := by
      rw [← canonicalJacquetMap_standardSection a C.lower_profile z']
      apply congrArg (canonicalJacquetMap a p' z')
      apply Subtype.ext
      change standardSection z' C.lower = f.val
      rw [hLower]
      exact standardSection_compactRestriction f.property
    let f' := spectralFrameKFiniteLift p E hConv z (C.frameVector D hConv z)
    refine ⟨f', fun he => hNZ ?_⟩
    have hv := congrFun he (weylLong (t + 2) ℝ)
    change canonicalJacquetMap a p z f' (weylLong (t + 2) ℝ) = 0 at hv
    rw [show f' = spectralFrameKFiniteLift p E hConv z (C.frameVector D hConv z) from rfl,
      realGodementCanonicalColumn D a p E hConv, hTest,
      show (fun i => z i.succ) = z' from rfl, hLowerEval] at hv
    exact hv

/-- The continued evaluation map itself is nonzero for every character list. -/
theorem canonicalJacquetMap_ne_zero (r : ℕ) (a : ℝˣ) (p : Fin (r + 1) → Fin 2)
    (z : Fin (r + 1) → ℂ) : canonicalJacquetMap a p z ≠ 0 := by
  obtain ⟨f, hf⟩ := realGodementCanonicalNonzero r a p z
  intro h
  exact hf (congrArg (fun L => L f) h)

end Langlands.Global.RankinSelbergGlobal.RealGodement
