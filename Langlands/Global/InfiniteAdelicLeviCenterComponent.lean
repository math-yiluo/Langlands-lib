import Langlands.Global.InfiniteAdelicLeviCenterComponentStatement
import Langlands.Global.InfiniteAdelicLeviWeightBasis
import Langlands.Algebra.EnvelopingFixedWeightDecomposition
import Langlands.Algebra.EnvelopingMapInjective
import Langlands.Algebra.LieCasimir
import Langlands.Automorphic.GroupSchemeEnvelopingCenterConjugationProof

/-! # The Levi component of a central element of the archimedean enveloping algebra -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Geometry.Manifold Langlands.Automorphic.GroupSchemeFunctions
  InfiniteAdelicGroupPoints Langlands.Algebra.UniversalEnveloping

attribute [local instance 100] LieRing.ofAssociativeRing

section Algebra

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- The range of an algebra map out of an enveloping algebra lies in a subalgebra containing the
images of the generators. -/
theorem range_le_of_ι_mem {A : Type*} [Ring A] [Algebra ℂ A]
    {L' : Type*} [LieRing L'] [LieAlgebra ℂ L']
    (φ : UniversalEnvelopingAlgebra ℂ L' →ₐ[ℂ] A) (S : Subalgebra ℂ A)
    (h : ∀ x, φ (UniversalEnvelopingAlgebra.ι ℂ x) ∈ S) : φ.range ≤ S := by
  rw [← Algebra.map_top, ← Langlands.Algebra.LieCasimir.enveloping_adjoin_range, AlgHom.map_adjoin,
    Algebra.adjoin_le_iff]
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact h x

/-- The complexification of an injective real Lie algebra map is injective. -/
theorem extendLieHom_injective {L' : Type*} [LieRing L'] [LieAlgebra ℝ L'] (f : L →ₗ⁅ℝ⁆ L')
    (hf : Function.Injective f) :
    Function.Injective (Langlands.Algebra.ComplexLieExtension.extendLieHom f) := by
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := ℂ) f.toLinearMap hf
  have heq : ∀ x, Langlands.Algebra.ComplexLieExtension.extendLieHom f x =
      LinearMap.lTensor ℂ f.toLinearMap x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul z X => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  intro x y hxy
  apply h
  rw [← heq, ← heq, hxy]

end Algebra

/-- The Levi component of a central element, from the weight basis of the archimedean Lie
algebra. -/
theorem leviCenterComponent_of_weightBasis (hW : LeviTangentWeightBasisStatement.{u}) :
    LeviCenterComponentStatement.{u} := by
  intro F _ _ G Q M' V _ _ _ q iV l' hG hq hV hl d d' hsmooth hsmooth' SV
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothChartedSpace F M' hsmooth'
  let := smoothLieGroup F G hsmooth
  let := smoothLieGroup F M' hsmooth'
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  let : LieGroup 𝓘(ℝ, smoothModel F d') (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F M') := LieGroup.of_le (n := ∞) (by simp)
  obtain ⟨t, n, b, w, heig, hinj, h0, h0le, hpos, hposle⟩ :=
    hW F G Q M' V q iV l' hG hq hV hl hsmooth hsmooth'
  let ιQ := M'.affinePointsTarget (l' ≫ q) (CommAlgCat.of F (InfiniteAdeleRing F))
  let bC := Algebra.TensorProduct.basis ℂ b
  have hbC : ∀ a, bC a = (1 : ℂ) ⊗ₜ[ℝ] b a := fun a => Algebra.TensorProduct.basis_apply b a
  let T := Langlands.Algebra.ComplexLieExtension.extendLieHom
    (groupTangentConjugationLieEquiv 𝓘(ℝ, smoothModel F d) (ιQ t)).toLieHom
  let c : ℂˣ := Units.mk0 2 two_ne_zero
  have hc : ∀ m : ℤ, c ^ m = 1 → m = 0 := by
    intro m hm
    have h1 : ((c ^ m : ℂˣ) : ℂ) = 1 := by rw [hm, Units.val_one]
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0] at h1
    have h2 : ‖(2 : ℂ) ^ m‖ = 1 := by rw [h1, norm_one]
    rw [norm_zpow, Complex.norm_two] at h2
    exact (zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)).mp h2
  have hT : ∀ a, T (bC a) = ((c ^ w a : ℂˣ) : ℂ) • bC a := by
    intro a
    rw [hbC, Langlands.Algebra.ComplexLieExtension.extendLieHom_tmul]
    change (1 : ℂ) ⊗ₜ[ℝ] groupTangentConjugation 𝓘(ℝ, smoothModel F d) (ιQ t) (b a) = _
    rw [heig a, TensorProduct.tmul_smul, ← algebraMap_smul ℂ, Units.val_zpow_eq_zpow_val,
      Units.val_mk0, Complex.coe_algebraMap, Complex.ofReal_zpow, Complex.ofReal_ofNat]
  obtain ⟨hfix, hdisj⟩ := envelopingFixedWeightDecomposition ℂ _ n bC w c hc T hT
  let j := pointEnvelopingMap F hsmooth' hsmooth (l' ≫ q)
  -- generators of positive weight lie in the curve ideal
  have hposI : positiveWeightGeneratorSpan bC w ≤ curveRightIdeal F hsmooth SV := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, ha, v, rfl⟩
    refine Submodule.subset_span ⟨b a, hpos a ha, v, ?_⟩
    rw [hbC]
  -- the curve ideal lies in the span of the generators of positive weight
  have hIpos : curveRightIdeal F hsmooth SV ≤ positiveWeightGeneratorSpan bC w := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨X, hXc, v, rfl⟩
    obtain ⟨cv, hcv, hcv0, hcvS, hcvX⟩ := hXc
    have hX : X ∈ Submodule.span ℝ (b '' {a | 0 < w a}) := by
      rw [← hcvX]
      exact hposle cv hcv hcv0 hcvS
    suffices H : ∀ (z : ℂ) (v : AdelicEnvelopingAlgebra F G hsmooth),
        UniversalEnvelopingAlgebra.ι ℂ (z ⊗ₜ[ℝ] X) * v ∈ positiveWeightGeneratorSpan bC w from
      H 1 v
    clear hcvX
    induction hX using Submodule.span_induction with
    | mem X hX =>
      obtain ⟨a, ha, rfl⟩ := hX
      intro z v
      have : z ⊗ₜ[ℝ] b a = z • bC a := by
        rw [hbC, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, map_smul, smul_mul_assoc, ← mul_smul_comm]
      exact Submodule.subset_span ⟨a, ha, z • v, rfl⟩
    | zero =>
      intro z v
      rw [TensorProduct.tmul_zero, map_zero, zero_mul]
      exact Submodule.zero_mem _
    | add X Y _ _ hX hY =>
      intro z v
      rw [TensorProduct.tmul_add, map_add, add_mul]
      exact Submodule.add_mem _ (hX z v) (hY z v)
    | smul r X _ hX =>
      intro z v
      rw [← TensorProduct.smul_tmul]
      exact hX (r • z) v
  -- generators of weight zero lie in the image of the Levi enveloping algebra
  have hzeroJ : zeroWeightGeneratorSubalgebra bC w ≤ j.range := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨Y, hY⟩ := h0 a ha
    refine ⟨UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] Y), ?_⟩
    refine (pointEnvelopingMap_ι_tmul F hsmooth' hsmooth (l' ≫ q) 1 Y).trans ?_
    rw [hbC, ← hY]
    rfl
  -- the image of the Levi enveloping algebra lies in the weight-zero subalgebra
  have hJzero : j.range ≤ zeroWeightGeneratorSubalgebra bC w := by
    refine range_le_of_ι_mem j _ fun x => ?_
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add]; exact Subalgebra.add_mem _ hx hy
    | tmul z Y =>
      have e := pointEnvelopingMap_ι_tmul F hsmooth' hsmooth (l' ≫ q) z Y
      change j (UniversalEnvelopingAlgebra.ι ℂ (z ⊗ₜ[ℝ] Y)) ∈ _
      rw [e]
      clear e
      have hY : pointTangent F hsmooth' hsmooth (l' ≫ q) Y ∈
          Submodule.span ℝ (b '' {a | w a = 0}) := h0le Y
      generalize pointTangent F hsmooth' hsmooth (l' ≫ q) Y = X at hY ⊢
      induction hY using Submodule.span_induction generalizing z with
      | mem X hX =>
        obtain ⟨a, ha, rfl⟩ := hX
        have : z ⊗ₜ[ℝ] b a = z • bC a := by
          rw [hbC, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this, map_smul]
        refine Subalgebra.smul_mem _ ?_ z
        exact Algebra.subset_adjoin ⟨a, ha, rfl⟩
      | zero => rw [TensorProduct.tmul_zero, map_zero]; exact Subalgebra.zero_mem _
      | add X Y _ _ hX hY =>
        rw [TensorProduct.tmul_add, map_add]
        exact Subalgebra.add_mem _ (hX z) (hY z)
      | smul r X _ hX =>
        rw [← TensorProduct.smul_tmul]
        exact hX (r • z)
  -- the enveloping map of the Levi subgroup is injective
  have hjinj : Function.Injective j := by
    have : FiniteDimensional ℝ
        (GroupLieAlgebra 𝓘(ℝ, smoothModel F d') (InfiniteAdelicGroupPoints F M')) :=
      inferInstanceAs (FiniteDimensional ℝ (smoothModel F d'))
    have : FiniteDimensional ℂ (ℂ ⊗[ℝ]
        GroupLieAlgebra 𝓘(ℝ, smoothModel F d') (InfiniteAdelicGroupPoints F M')) :=
      inferInstance
    have : FiniteDimensional ℂ (ℂ ⊗[ℝ]
        GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) :=
      Module.Finite.of_basis bC
    exact lift_comp_injective _ (extendLieHom_injective _ hinj)
  refine ⟨fun z => ?_, fun y hy => ?_⟩
  · have hfz : UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp T)
        (z : AdelicEnvelopingAlgebra F G hsmooth) = z :=
      adelicEnvelopingCenterConjugation F G hsmooth hG (ιQ t) z z.property
    obtain ⟨p, hp, r, hr, hpr⟩ := Submodule.mem_sup.mp (hfix _ hfz)
    obtain ⟨y, hy⟩ := hzeroJ hr
    refine ⟨y, ?_⟩
    rw [← hpr]
    have hy' : j y = r := hy
    change p + r - j y ∈ _
    rw [hy', add_sub_cancel_right]
    exact hposI hp
  · have h1 := hIpos hy
    have h2 : j y ∈ (zeroWeightGeneratorSubalgebra bC w).toSubmodule := hJzero ⟨y, rfl⟩
    have h3 : j y = 0 := Submodule.disjoint_def.mp hdisj _ h1 h2
    exact hjinj (h3.trans (map_zero j).symm)

/-- The Levi component of central elements of the archimedean enveloping algebra modulo the
right ideal of the unipotent radical: existence, and uniqueness through injectivity. -/
theorem leviCenterComponent : LeviCenterComponentStatement.{u} :=
  leviCenterComponent_of_weightBasis leviTangentWeightBasis

end Langlands.Global
