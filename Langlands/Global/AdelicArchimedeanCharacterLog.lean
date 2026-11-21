import Langlands.Global.AdelicCharacterLog
import Langlands.Global.AdelicGroupProduct
import Langlands.Global.InfiniteAdelicGroupManifold
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Geometry.Manifold.Algebra.Monoid

/-! # Smooth extensions of actual archimedean character logarithms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped CategoryTheory.MonObj Manifold ContDiff NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme InfiniteAdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

local notation "Ar" => CommAlgCat.of F (InfiniteAdeleRing F)
local notation "Fr" => CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F)
local notation "Adr" => CommAlgCat.of F (AdeleRing (𝓞 F) F)

/-- The regular function obtained by pulling the universal unit back along a character. -/
def characterRegularFunction (χ : rationalCharacters G) : Γ(G.X.left, ⊤) :=
  χ.toMul.hom.hom.left.appTop (GroupScheme.Gm.universalUnit (CommRingCat.of F)).val

omit [NumberField F] in
/-- Evaluation of the lifted coordinate gives the value of the actual character unit. -/
theorem characterUnits_val_eq_evaluation (χ : rationalCharacters G) (C : CommAlgCat.{u} (CommRingCat.of F))
    (g : G.affinePoints C) :
    (characterUnits F G χ.toMul C g).val = G.affinePointEvaluation C g (characterRegularFunction F G χ) := by
  change (GroupScheme.Gm.affineUnitsEquiv (CommRingCat.of F) C (G.affinePointsTarget χ.toMul C g)).val = _
  rw [GroupScheme.Gm.affineUnitsEquiv_eq_map, Units.coe_map]
  exact G.affinePointEvaluation_postcomp C χ.toMul.hom.hom g _

variable [IsAffine G.X.left]

/-- On a pure infinite point the logarithmic character uses just the infinite product. -/
theorem characterLog_apply_ofInfinite (χ : rationalCharacters G) (a : InfiniteAdelicGroupPoints F G) :
    characterLog F G (ofInfinite F G a) χ =
      Real.log (∏ v : InfinitePlace F, ‖G.affinePointEvaluation Ar a (characterRegularFunction F G χ) v‖ ^ v.mult) := by
  let U := characterUnits F G χ.toMul Adr (ofInfinite F G a)
  have hinf : U.val.1 = (characterUnits F G χ.toMul Ar a).val := by
    let f := CommAlgCat.ofHom (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
    have h := characterUnits_naturality F G χ.toMul f (ofInfinite F G a)
    change characterUnits F G χ.toMul Ar (infinite F G (ofInfinite F G a)) = _ at h
    rw [infinite_ofInfinite] at h
    exact (congrArg Units.val h).symm
  have hfin : U.val.2 = (1 : FiniteAdeleRing (𝓞 F) F) := by
    let f := CommAlgCat.ofHom (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
    have h := characterUnits_naturality F G χ.toMul f (ofInfinite F G a)
    change characterUnits F G χ.toMul Fr (finite F G (ofInfinite F G a)) = _ at h
    rw [finite_ofInfinite, map_one] at h
    exact (congrArg Units.val h).symm
  change Real.log ((IdeleAbsoluteValue.full F U : ℝ≥0) : ℝ) = _
  rw [IdeleAbsoluteValue.coe_full, hinf, hfin, characterUnits_val_eq_evaluation]
  have hone (v : FinitePlace F) : (1 : FiniteAdeleRing (𝓞 F) F) v = 1 := rfl
  simp only [hone, norm_one, finprod_one, mul_one]

/-- The logarithm of the archimedean absolute value of a regular function. -/
def archimedeanLogRegular (s : Γ(G.X.left, ⊤)) (a : InfiniteAdelicGroupPoints F G) : ℝ :=
  Real.log (∏ v : InfinitePlace F, ‖G.affinePointEvaluation Ar a s v‖ ^ v.mult)

/-- This logarithm is smooth at any point where all its local values are nonzero. -/
theorem contMDiffAt_archimedeanLogRegular {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (s : Γ(G.X.left, ⊤)) (a : InfiniteAdelicGroupPoints F G)
    (ha : ∀ v : InfinitePlace F, G.affinePointEvaluation Ar a s v ≠ 0) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    ContMDiffAt 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℝ) ∞ (archimedeanLogRegular F G s) a := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let : ContMDiffMul 𝓘(ℝ, ℝ) ∞ ℝ := ⟨by
    have hprod : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞ (id : ℝ × ℝ → ℝ × ℝ) :=
      (contMDiff_prod_module_iff _).mpr ⟨contMDiff_fst, contMDiff_snd⟩
    exact (contDiff_mul (𝕜 := ℝ) (𝔸 := ℝ)).contMDiff.comp hprod⟩
  let f (a : InfiniteAdelicGroupPoints F G) := ∏ v : InfinitePlace F, ‖G.affinePointEvaluation Ar a s v‖ ^ v.mult
  have hf : ContMDiffAt 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℝ) ∞ f a := by
    apply contMDiffAt_finsetProd
    intro v _
    have hv := (contMDiff_completionEvaluation F G hsmooth v s).contMDiffAt (x := a)
    have hn := ((contDiffAt_norm (𝕜 := v.Completion) (n := ∞) (ha v)).contMDiffAt.comp a hv)
    exact hn.pow _
  have hne : f a ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (ha v))
  exact (Real.contDiffAt_log.mpr hne).contMDiffAt.comp a hf

variable {G} {P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine P.X.left]
  (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left]

/-- An algebraic character logarithm of a closed subgroup extends to a
function on the ambient infinite points, smooth at each subgroup point. -/
theorem exists_archimedeanLogRegular_characterExtension {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (χ : rationalCharacters P) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    ∃ s : Γ(G.X.left, ⊤), ∀ a : InfiniteAdelicGroupPoints F P,
      let y := P.affinePointsTarget p Ar a
      archimedeanLogRegular F G s y = characterLog F P (ofInfinite F P a) χ ∧
        ContMDiffAt 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℝ) ∞ (archimedeanLogRegular F G s) y := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  obtain ⟨s, hs⟩ := (IsClosedImmersion.isAffine_surjective_of_isAffine p.hom.hom.left).2
    (characterRegularFunction F P χ)
  refine ⟨s, fun a => ?_⟩
  let y := P.affinePointsTarget p Ar a
  have he : G.affinePointEvaluation Ar y s = (characterUnits F P χ.toMul Ar a).val := by
    rw [characterUnits_val_eq_evaluation, ← hs]
    exact P.affinePointEvaluation_postcomp Ar p.hom.hom a s
  refine ⟨?_, contMDiffAt_archimedeanLogRegular F G hsmooth s y (fun v => ?_)⟩
  · rw [archimedeanLogRegular, characterLog_apply_ofInfinite, he, characterUnits_val_eq_evaluation]
  · rw [he]
    exact Units.ne_zero (Units.map (Pi.evalMonoidHom _ v) (characterUnits F P χ.toMul Ar a))

end Langlands.Global.AdelicGroupPoints
