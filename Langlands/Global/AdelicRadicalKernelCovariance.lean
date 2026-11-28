import Langlands.Global.AdelicStandardParabolicIwasawa
import Langlands.Global.AdelicLeviRadicalAverageTestFunctionStatement
import Langlands.Global.AdelicTestFunctionCompactAverage

/-! # Compact radical kernels and their left covariance -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj NNReal CompactlySupported

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

local notation "A" => AdelicGroupPoints F G
local notation "AM" => AdelicGroupPoints F (fam.M J)
local notation "ι" => map F (fam.M J) G (fam.l J ≫ fam.p J)
local notation "ιU" => map F (fam.U J) G (fam.iU J ≫ fam.p J)

/-- The radical kernel as a compactly supported continuous function on the Levi. -/
def radicalKernelCc (β : C_c(A, ℂ)) (g k : A) : C_c(AM, ℂ) where
  toFun := fam.radicalKernel J β g k
  continuous_toFun := by
    change Continuous (fun m : AM => fam.radicalKernel J β g k m)
    have h : Continuous (fun m : AM => ((g, k, m) : A × A × AM)) :=
      continuous_const.prodMk (continuous_const.prodMk continuous_id)
    exact Continuous.comp' (g := fun p : A × A × AM =>
      fam.radicalKernel J β p.1 p.2.1 p.2.2)
      (f := fun m : AM => ((g, k, m) : A × A × AM)) (fam.continuous_radicalKernel J β) h
  hasCompactSupport' := by
    classical
    change HasCompactSupport (fun m : AM => fam.radicalKernel J β g k m)
    obtain ⟨D, hD, h⟩ := fam.exists_compact_radicalKernel_support J β
      (isCompact_singleton (x := g)) (isCompact_singleton (x := k))
    refine HasCompactSupport.intro hD fun m hm => ?_
    by_contra hne
    exact hm (h g rfl k rfl m hne)

@[simp] theorem radicalKernelCc_apply (β : C_c(A, ℂ)) (g k : A) (m : AM) :
    fam.radicalKernelCc J β g k m = fam.radicalKernel J β g k m := rfl

/-- All the radical kernels with arguments in two fixed compact sets have support in one
compact subset of the Levi. -/
theorem exists_compact_tsupport_radicalKernelCc (β : C_c(A, ℂ))
    {C D : Set A} (hC : IsCompact C) (hD : IsCompact D) :
    ∃ E : Set AM, IsCompact E ∧ ∀ g ∈ C, ∀ k ∈ D, tsupport (fam.radicalKernelCc J β g k) ⊆ E := by
  obtain ⟨E, hE, h⟩ := fam.exists_compact_radicalKernel_support J β hC hD
  refine ⟨E, hE, fun g hg k hk => closure_minimal ?_ hE.isClosed⟩
  exact h g hg k hk

/-- Left multiplication by a radical point does not change the radical kernel. -/
theorem radicalKernel_mul_radical (β : A → ℂ) (g k : A) (u : AdelicGroupPoints F (fam.U J))
    (m : AM) :
    fam.radicalKernel J β (ιU u * g) k m = fam.radicalKernel J β g k m := by
  let := locallyOfFiniteType_unipotent F (fam.isRepresentedBy_unipotent J)
  let := isAffine_unipotent F (fam.isRepresentedBy_unipotent J)
  unfold radicalKernel
  rw [← integral_mul_left_eq_self (fun v => β (g⁻¹ * (ιU v * ι m * k))) u⁻¹]
  apply integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  congr 1
  rw [map_mul, map_inv, mul_inv_rev]
  group

/-- Left multiplication by a Levi point translates the Levi variable of the radical kernel
and contributes the parabolic modulus. -/
theorem radicalKernel_mul_levi (β : A → ℂ) (g k : A) (x m : AM) :
    fam.radicalKernel J β (ι x * g) k m =
      (fam.leviModulus J x : ℝ) • fam.radicalKernel J β g k (x⁻¹ * m) := by
  let := locallyOfFiniteType_unipotent F (fam.isRepresentedBy_unipotent J)
  let := isAffine_unipotent F (fam.isRepresentedBy_unipotent J)
  have h := integral_conj_parabolicModulus F (fam.isRepresentedBy_parabolic J)
    (fam.isRepresentedBy_unipotent J) (map F (fam.M J) (fam.P J) (fam.l J) x)
    (Measure.haar : Measure (AdelicGroupPoints F (fam.U J)))
    (fun v => β (g⁻¹ * (v * ι (x⁻¹ * m) * k)))
  rw [← map_comp_apply_of_hom (fam.l J)] at h
  unfold radicalKernel
  rw [← NNReal.smul_def]
  change _ = (parabolicModulus F (fam.isRepresentedBy_parabolic J)
    (fam.isRepresentedBy_unipotent J) (map F (fam.M J) (fam.P J) (fam.l J) x) : ℝ≥0) • _
  rw [← h]
  apply integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  congr 1
  rw [map_mul, map_inv, mul_inv_rev]
  group

/-- The unnormalized radical kernel of a test function is a Levi test function whenever the
normalized radical averaging statement holds. -/
theorem isAdelicTestFunction_radicalKernel (hAvg : LeviRadicalAverageTestFunctionStatement.{u})
    {β : A → ℂ} (hβ : IsAdelicTestFunction F G β) (g k : A) :
    IsAdelicTestFunction F (fam.M J) (fam.radicalKernel J β g k) := by
  let j := fam.iU J ≫ fam.p J
  let := locallyOfFiniteType_unipotent F (fam.isRepresentedBy_unipotent J)
  let := isAffine_unipotent F (fam.isRepresentedBy_unipotent J)
  let : IsClosedImmersion j.hom.hom.left := inferInstanceAs
    (IsClosedImmersion (fam.iU J ≫ fam.p J).hom.hom.left)
  let := fam.compactSpace_radicalRationalQuotient J
  obtain ⟨d, hd⟩ := fam.connectedReductive.exists_smoothOfRelativeDimension
  let f : A → ℂ := fun z => β (g⁻¹ * z * k)
  have hf : IsAdelicTestFunction F G f := isAdelicTestFunction_comp_mul_mul hd hβ g⁻¹ k
  let L : AM → ℂ := fun m =>
    ∫ v : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j),
      f ((v : A) * ι m) ∂AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range j)
  have hL : IsAdelicTestFunction F (fam.M J) L := hAvg F G fam J f hf
  obtain ⟨a, -, ha⟩ := exists_integral_adelicRangeMap_eq_normalized (F := F) j
  have hEq : fam.radicalKernel J β g k = (a : ℂ) • L := by
    funext m
    rw [Pi.smul_apply, smul_eq_mul, ← Complex.real_smul]
    rw [← show (∫ v, f ((v : A) * ι m)
      ∂AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range j)) = L m from rfl]
    rw [← ha]
    unfold radicalKernel
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    change β (g⁻¹ * (ιU u * ι m * k)) = β (g⁻¹ * (ιU u * ι m) * k)
    simp only [mul_assoc]
  rw [hEq]
  obtain ⟨R, hRo, hR⟩ := hL.1.2.2
  obtain ⟨S, hSo, hS⟩ := hL.2.2
  refine ⟨⟨hL.1.1.const_smul _, ?_, R, hRo, ?_⟩, hL.2.1.smul_left, S, hSo, ?_⟩
  · exact fun b => (InfinitePlotSmoothFunctions F (fam.M J)).smul_mem _ (hL.1.2.1 b)
  · exact fun l hl x => congrArg ((a : ℂ) • ·) (hR l hl x)
  · exact fun l hl x => congrArg ((a : ℂ) • ·) (hS l hl x)

end Langlands.Global.StandardParabolicFamily
