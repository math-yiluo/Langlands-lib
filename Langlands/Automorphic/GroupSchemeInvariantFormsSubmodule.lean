import Langlands.Global.AdelicEisensteinGrowthBound
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # The space of adelic automorphic functions is a complex submodule -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints Langlands.GroupScheme
  Langlands.Global.RepresentationGrowth

private theorem finite_quotient_inf {E : Type*} [AddCommGroup E] [Module ℂ E]
    (P Q : Submodule ℂ E) [Module.Finite ℂ (E ⧸ P)] [Module.Finite ℂ (E ⧸ Q)] :
    Module.Finite ℂ (E ⧸ (P ⊓ Q)) := by
  have hker : (P.mkQ.prod Q.mkQ).ker = P ⊓ Q := by
    rw [LinearMap.ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ]
  let e := (P ⊓ Q).liftQ (P.mkQ.prod Q.mkQ) hker.ge
  exact Module.Finite.of_injective e (LinearMap.ker_eq_bot.mp
    (Submodule.ker_liftQ_eq_bot _ _ _ hker.le))

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {N d : ℕ} {rho : MatrixRepresentation G (Fin N)}
  {hsmooth : SmoothOfRelativeDimension d G.X.hom} {hcalc : AdelicDifferentialCommutator F G hsmooth}
  {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)}

local notation "Functions" => AdelicGroupPoints F G → ℂ

private abbrev infiniteRightOrbitSpan (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (f : Functions) :
    Submodule ℂ Functions :=
  Submodule.span ℂ (Set.range fun k : Kinf =>
    fun g : AdelicGroupPoints F G => f (g * AdelicGroupPoints.ofInfinite F G k))

omit [IsAffine G.X.left] in
private theorem moderateGrowth_add {f h : Functions}
    (hf : HasModerateGrowthFunction F G rho f) (hh : HasModerateGrowthFunction F G rho h) :
    HasModerateGrowthFunction F G rho (f + h) := by
  obtain ⟨r, -, hf⟩ := RepresentationGrowth.HasModerateGrowthFunction.exists_compact_mul_le_height hf
  obtain ⟨s, -, hh⟩ := RepresentationGrowth.HasModerateGrowthFunction.exists_compact_mul_le_height hh
  obtain ⟨C, hC, hf⟩ := hf {1} isCompact_singleton
  obtain ⟨D, hD, hh⟩ := hh {1} isCompact_singleton
  have hbound (g : AdelicGroupPoints F G) :
      ‖(f + h) g‖ ≤ (C + D) * adelicHeightAtLeastOne rho g ^ max r s := by
    have h₁ : 1 ≤ adelicHeightAtLeastOne rho g := le_max_left _ _
    have hf' : ‖f g‖ ≤ C * adelicHeightAtLeastOne rho g ^ r :=
      by simpa using hf g 1 (Set.mem_singleton 1)
    have hh' : ‖h g‖ ≤ D * adelicHeightAtLeastOne rho g ^ s :=
      by simpa using hh g 1 (Set.mem_singleton 1)
    calc
      ‖(f + h) g‖ ≤ ‖f g‖ + ‖h g‖ := norm_add_le _ _
      _ ≤ C * adelicHeightAtLeastOne rho g ^ r + D * adelicHeightAtLeastOne rho g ^ s :=
        add_le_add hf' hh'
      _ ≤ C * adelicHeightAtLeastOne rho g ^ max r s + D * adelicHeightAtLeastOne rho g ^ max r s :=
        add_le_add (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le h₁ (le_max_left _ _)) hC.le)
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le h₁ (le_max_right _ _)) hD.le)
      _ = _ := (add_mul _ _ _).symm
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hmatrix (g : AdelicGroupPoints F G) : adelicMatrix F G rho g = 1 := by
      apply Units.ext
      ext i j
      exact Fin.elim0 i
    let B := max 1 (AdelicMatrixHeight.height F 0 1)
    have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
    refine ⟨(C + D) * B ^ max r s, mul_pos (add_pos hC hD) (Real.rpow_pos_of_pos hB _), 0, ?_⟩
    intro g
    simpa only [Real.rpow_zero, mul_one, adelicHeightAtLeastOne, adelicHeight, hmatrix, B] using hbound g
  · let scale : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)
    have hscale : 0 < scale := pow_pos (Nat.cast_pos.mpr hN) _
    refine ⟨(C + D) * scale ^ max r s, mul_pos (add_pos hC hD) (Real.rpow_pos_of_pos hscale _),
      max r s, fun g => ?_⟩
    calc
      _ ≤ (C + D) * adelicHeightAtLeastOne rho g ^ max r s := hbound g
      _ = _ := by
        rw [adelicHeightAtLeastOne_eq hN, adelicHeight_eq_scalar_mul_sourceNorm,
          Real.mul_rpow hscale.le (adelicSourceNorm_pos F G rho hN g).le, mul_assoc]

omit [IsAffine G.X.left] in
private theorem moderateGrowth_smul {f : Functions}
    (hf : HasModerateGrowthFunction F G rho f) (c : ℂ) :
    HasModerateGrowthFunction F G rho (c • f) := by
  obtain ⟨C, hC, R, hbound⟩ := hf
  refine ⟨(‖c‖ + 1) * C, mul_pos (by positivity) hC, R, fun g => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
  exact (mul_le_mul_of_nonneg_left (hbound g) (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
      ((norm_nonneg _).trans (hbound g)))

/-- The original adelic automorphy predicate is closed under addition and
complex scalar multiplication for a fixed left invariance subgroup,
archimedean finiteness subgroup and growth representation. -/
def automorphicFunctionsOn (Γ : Subgroup (AdelicGroupPoints F G))
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth) :
    Submodule ℂ Functions where
  carrier := {f | IsAutomorphicFunctionOn F G hsmooth hcalc Γ Kinf rho f}
  zero_mem' := by
    refine ⟨fun _ _ _ => rfl, ⟨continuous_const, fun _ => (InfinitePlotSmoothFunctions F G).zero_mem,
        ⟨⊤, isOpen_univ, fun _ _ _ => rfl⟩⟩, ?_, ?_, ⟨1, zero_lt_one, 0, fun _ => by simp⟩⟩
    · change FiniteDimensional ℂ (infiniteRightOrbitSpan Kinf 0)
      have hspan : infiniteRightOrbitSpan Kinf 0 = ⊥ := by
        apply le_antisymm ?_ bot_le
        apply Submodule.span_le.mpr
        rintro _ ⟨_, rfl⟩
        exact (⊥ : Submodule ℂ Functions).zero_mem
      rw [hspan]
      infer_instance
    · refine ⟨⊤, ?_, fun z _ b h => ?_⟩
      · change Module.Finite ℂ (AdelicEnvelopingCenter F G hsmooth ⧸
          (⊤ : Submodule ℂ (AdelicEnvelopingCenter F G hsmooth)))
        infer_instance
      · change (plotSmoothCenterAction F G hsmooth hcalc z) 0 = 0
        exact map_zero _
  add_mem' := by
    rintro f h ⟨hfInv, hfSmooth, hfFin, hfCenter, hfBound⟩
      ⟨hhInv, hhSmooth, hhFin, hhCenter, hhBound⟩
    refine ⟨fun x hx g => by simp only [Pi.add_apply, hfInv x hx g, hhInv x hx g],
      ?_, ?_, ?_, moderateGrowth_add hfBound hhBound⟩
    · obtain ⟨L, hL, hf⟩ := hfSmooth.2.2
      obtain ⟨M, hM, hh⟩ := hhSmooth.2.2
      refine ⟨hfSmooth.1.add hhSmooth.1, fun b => (InfinitePlotSmoothFunctions F G).add_mem
        (hfSmooth.2.1 b) (hhSmooth.2.1 b), L ⊓ M, hL.inter hM, fun k hk g => ?_⟩
      simp only [Pi.add_apply, hf k hk.1 g, hh k hk.2 g]
    · let : FiniteDimensional ℂ (infiniteRightOrbitSpan Kinf f) := hfFin
      let : FiniteDimensional ℂ (infiniteRightOrbitSpan Kinf h) := hhFin
      change FiniteDimensional ℂ (infiniteRightOrbitSpan Kinf (f + h))
      apply Submodule.finiteDimensional_of_le (S₂ := infiniteRightOrbitSpan Kinf f ⊔
        infiniteRightOrbitSpan Kinf h)
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      apply Submodule.mem_sup.mpr
      exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, _, Submodule.subset_span ⟨k, rfl⟩, rfl⟩
    · obtain ⟨I, hI, hf⟩ := hfCenter
      obtain ⟨J, hJ, hh⟩ := hhCenter
      let : Module.Finite ℂ _ := hI
      let : Module.Finite ℂ _ := hJ
      refine ⟨I ⊓ J, finite_quotient_inf (I.restrictScalars ℂ) (J.restrictScalars ℂ), ?_⟩
      intro z hz b hb
      let fSlice : InfinitePlotSmoothFunctions F G :=
        ⟨functionInfiniteSlice F G f b, hfSmooth.2.1 b⟩
      let hSlice : InfinitePlotSmoothFunctions F G :=
        ⟨functionInfiniteSlice F G h b, hhSmooth.2.1 b⟩
      change plotSmoothCenterAction F G hsmooth hcalc z (fSlice + hSlice) = 0
      rw [map_add, hf z hz.1 b (hfSmooth.2.1 b), hh z hz.2 b (hhSmooth.2.1 b), add_zero]
  smul_mem' := by
    rintro c f ⟨hfInv, hfSmooth, hfFin, hfCenter, hfBound⟩
    refine ⟨fun x hx g => by simp only [Pi.smul_apply, hfInv x hx g],
      ?_, ?_, ?_, moderateGrowth_smul hfBound c⟩
    · obtain ⟨L, hL, hf⟩ := hfSmooth.2.2
      refine ⟨continuous_const.smul hfSmooth.1,
        fun b => (InfinitePlotSmoothFunctions F G).smul_mem c (hfSmooth.2.1 b), L, hL, ?_⟩
      intro k hk g
      simp only [Pi.smul_apply, hf k hk g]
    · let : FiniteDimensional ℂ (infiniteRightOrbitSpan Kinf f) := hfFin
      change FiniteDimensional ℂ (infiniteRightOrbitSpan Kinf (c • f))
      apply Submodule.finiteDimensional_of_le (S₂ := infiniteRightOrbitSpan Kinf f)
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨k, rfl⟩)
    · obtain ⟨I, hI, hf⟩ := hfCenter
      refine ⟨I, hI, fun z hz b hb => ?_⟩
      let fSlice : InfinitePlotSmoothFunctions F G :=
        ⟨functionInfiniteSlice F G f b, hfSmooth.2.1 b⟩
      change plotSmoothCenterAction F G hsmooth hcalc z (c • fSlice) = 0
      rw [map_smul, hf z hz b (hfSmooth.2.1 b), smul_zero]

@[simp] theorem mem_automorphicFunctionsOn {Γ : Subgroup (AdelicGroupPoints F G)} {f : Functions} :
    f ∈ automorphicFunctionsOn Γ Kinf rho hsmooth hcalc ↔
      IsAutomorphicFunctionOn F G hsmooth hcalc Γ Kinf rho f :=
  Iff.rfl

end Langlands.Automorphic.GroupSchemeFunctions
