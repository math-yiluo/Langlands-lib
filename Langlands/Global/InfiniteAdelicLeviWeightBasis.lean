import Langlands.Global.InfiniteAdelicLeviWeightBasisStatement
import Langlands.Global.InfiniteAdelicInnerTangent
import Langlands.Global.InfiniteAdelicTangentCurve
import Langlands.Global.InfiniteAdelicLeviEnveloping
import Langlands.Global.InfiniteAdelicRealTrace
import Langlands.Global.InfiniteAdelicTangentKernelBijective
import Langlands.GroupScheme.GmBasePointCharacter
import Langlands.GroupScheme.Rational.LeviCocharacterLieWeightBasis
import Langlands.Geometry.Manifold.InvolutionFixedCurve
import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof

/-! # A weight basis of the archimedean Lie algebra for a parabolic and a Levi subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Opposite
open scoped CategoryTheory.MonObj Manifold ContDiff Pointwise

set_option autoImplicit false

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.GroupScheme Langlands.Geometry.Manifold

variable (F : Type u) [Field F] [NumberField F]

theorem realAlgebra_finiteDimensional :
    letI := realAlgebra F
    FiniteDimensional ℝ (InfiniteAdeleRing F) :=
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  inferInstanceAs (FiniteDimensional ℝ ((v : InfinitePlace F) → v.Completion))

variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

/-- The real structure of the dual-number identity kernel over `F_∞`, by restriction of
scalars. -/
@[reducible] def kernelRealModule : Module ℝ (Additive (lieKernel G (InfiniteAdeleRing F))) :=
  letI := realAlgebra F
  Module.compHom _ (algebraMap ℝ (InfiniteAdeleRing F))

omit [NumberField F] in
theorem kernelReal_isScalarTower :
    letI := realAlgebra F
    letI := kernelRealModule F G
    IsScalarTower ℝ (InfiniteAdeleRing F) (Additive (lieKernel G (InfiniteAdeleRing F))) := by
  let := realAlgebra F
  let := kernelRealModule F G
  exact ⟨fun r a x => by
    change (r • a) • x = algebraMap ℝ (InfiniteAdeleRing F) r • a • x
    rw [Algebra.smul_def, mul_smul]⟩

variable {G} {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

/-- The tangent map `X ↦ tangentKernel X`, as a real-linear map. -/
def tangentKernelLinear :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := realAlgebra F
    letI := kernelRealModule F G
    GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) →ₗ[ℝ]
      Additive (lieKernel G (InfiniteAdeleRing F)) := by
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := realAlgebra F
  letI := kernelRealModule F G
  exact
    { toFun := fun X => Additive.ofMul (tangentKernel F hsmooth X)
      map_add' := fun X Y => congrArg Additive.ofMul (tangentKernel_add F hsmooth X Y)
      map_smul' := fun r X => by
        refine (congrArg Additive.ofMul (tangentKernel_smul F hsmooth X r)).trans ?_
        change _ = algebraMap ℝ (InfiniteAdeleRing F) r • Additive.ofMul (tangentKernel F hsmooth X)
        rw [realAlgebra_algebraMap]
        rfl }

theorem tangentKernelLinear_apply
    (X : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) :
    tangentKernelLinear F hsmooth X = Additive.ofMul (tangentKernel F hsmooth X) := rfl

/-- The tangent map, as a real-linear equivalence, when it is bijective. -/
def tangentKernelAdeleEquiv (hbij : Function.Bijective (tangentKernel F hsmooth)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := realAlgebra F
    letI := kernelRealModule F G
    GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) ≃ₗ[ℝ]
      Additive (lieKernel G (InfiniteAdeleRing F)) :=
  LinearEquiv.ofBijective (tangentKernelLinear F hsmooth)
    (Additive.ofMul.bijective.comp hbij)

theorem tangentKernelAdeleEquiv_apply (hbij : Function.Bijective (tangentKernel F hsmooth))
    (X : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) :
    tangentKernelAdeleEquiv F hsmooth hbij X = Additive.ofMul (tangentKernel F hsmooth X) := rfl

/-- The chain rule between manifolds at a point given up to equality. -/
theorem mfderiv_comp_apply_of_eq' {E E' E'' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {M M' M'' : Type*} [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace M']
    [ChartedSpace E' M'] [TopologicalSpace M''] [ChartedSpace E'' M''] {f : M → M'}
    {g : M' → M''} {x : M} {y : M'}
    (hg : MDifferentiableAt 𝓘(ℝ, E') 𝓘(ℝ, E'') g y) (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E') f x)
    (hy : f x = y) (w : TangentSpace 𝓘(ℝ, E) x) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E'') (g ∘ f) x w =
      mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E'') g y (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E') f x w) := by
  subst hy
  exact mfderiv_comp_apply _ hg hf w


section CurveTangents

variable {V : GroupScheme (Spec (CommRingCat.of F))} [IsAffine V.X.left]

/-- For a closed subgroup `j : V ⟶ G` with a smooth structure on `V`, a tangent vector of
`G(F_∞)` at `1` is a real combination of velocities at `0` of smooth curves through `1` in the
image of `V(F_∞)` exactly when its dual-number Lie vector lies in the image of the dual-number
Lie algebra of `V` over `F_∞`. -/
theorem mem_span_curveTangents_iff {e : ℕ} (hsmoothV : SmoothOfRelativeDimension e V.X.hom)
    (j : V ⟶ G) [IsClosedImmersion j.hom.hom.left]
    (X : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) :
    X ∈ Submodule.span ℝ (curveTangents F hsmooth
        (Set.range (V.affinePointsTarget j (CommAlgCat.of F (InfiniteAdeleRing F))))) ↔
      Additive.ofMul (tangentKernel F hsmooth X) ∈
        LinearMap.range (Lie.targetMapLinear j (InfiniteAdeleRing F)) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := realAlgebra F
  let := kernelRealModule F G
  have := kernelReal_isScalarTower F G
  let SV := Set.range (V.affinePointsTarget j (CommAlgCat.of F (InfiniteAdeleRing F)))
  constructor
  · intro hX
    have hle : Submodule.span ℝ (curveTangents F hsmooth SV) ≤
        ((LinearMap.range (Lie.targetMapLinear j (InfiniteAdeleRing F))).restrictScalars ℝ).comap
          (tangentKernelLinear F hsmooth) := by
      rw [Submodule.span_le]
      rintro _ ⟨c, hc, hc0, hcV, rfl⟩
      exact tangentKernel_curve_mem_range F hsmooth j c hc hc0 hcV
    exact hle hX
  · rintro ⟨y, hy⟩
    obtain ⟨Y, hY⟩ := (tangentKernel_bijective F hsmoothV).2 (Additive.toMul y)
    let := smoothChartedSpace F V hsmoothV
    have := smoothIsManifold F V hsmoothV
    obtain ⟨cV, hcV, hcV0, -, hcV'⟩ :=
      Langlands.Geometry.Manifold.InvolutionFixedCurve.exists_contMDiff_curve_fixed
        (E := smoothModel F e) (M := InfiniteAdelicGroupPoints F V) id contMDiff_id
        (fun _ => rfl) 1 rfl Y (by rw [mfderiv_id]; rfl)
    let ιV := V.affinePointsTarget j (CommAlgCat.of F (InfiniteAdeleRing F))
    have hιV : ContMDiff 𝓘(ℝ, smoothModel F e) 𝓘(ℝ, smoothModel F d) ∞ ιV :=
      contMDiff_affinePointsTarget F hsmoothV hsmooth j
    have hcomp : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, smoothModel F d) ∞ (ιV ∘ cV) := hιV.comp hcV
    have hX : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, smoothModel F d) (ιV ∘ cV) 0 (1 : ℝ) = X := by
      have hchain := mfderiv_comp_apply_of_eq' (g := ιV) (f := cV)
        (hιV.mdifferentiable (by simp) 1) (hcV.mdifferentiable (by simp) 0) hcV0 (1 : ℝ)
      refine hchain.trans ?_
      rw [hcV']
      apply (tangentKernel_bijective F hsmooth).1
      apply Additive.ofMul.injective
      refine (tangentKernel_pointTangent F hsmoothV hsmooth j Y).trans ?_
      rw [hY]
      exact hy
    refine Submodule.subset_span ⟨ιV ∘ cV, hcomp, ?_, fun s => ⟨cV s, rfl⟩, hX⟩
    show ιV (cV 0) = 1
    rw [hcV0]
    exact map_one _

end CurveTangents

/-- The integral powers of the unit `2` of `F` in `F_∞` are the images of the real powers of `2`. -/
theorem units_map_two_zpow (m : ℤ) :
    letI := realAlgebra F
    ((Units.map (algebraMap F (InfiniteAdeleRing F)).toMonoidHom
        (Units.mk0 (2 : F) two_ne_zero) ^ m : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) =
      algebraMap ℝ (InfiniteAdeleRing F) ((2 : ℝ) ^ m) := by
  let := realAlgebra F
  have hu : Units.map (algebraMap F (InfiniteAdeleRing F)).toMonoidHom
      (Units.mk0 (2 : F) two_ne_zero) =
      Units.map (algebraMap ℝ (InfiniteAdeleRing F)).toMonoidHom
        (Units.mk0 (2 : ℝ) two_ne_zero) := by
    ext
    change algebraMap F (InfiniteAdeleRing F) 2 = algebraMap ℝ (InfiniteAdeleRing F) 2
    rw [map_ofNat, map_ofNat]
  rw [hu, ← map_zpow, Units.coe_map, Units.val_zpow_eq_zpow_val, Units.val_mk0]
  rfl

end Langlands.Global.InfiniteAdelicGroupPoints

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Geometry.Manifold InfiniteAdelicGroupPoints

/-- A real basis, obtained by transporting a tower basis, spans in the expected
way: `A`-combinations of a family of `e`-vectors are real combinations of the tower vectors
with the same `e`-index. -/
theorem mem_span_smulTower_map {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [AddCommGroup N]
    [Module R N] {J K : Type*} (bS : Module.Basis K R S) (e : Module.Basis J S M)
    (f : M ≃ₗ[R] N) (P : J → Prop) {x : M} (hx : x ∈ Submodule.span S (e '' {i | P i})) :
    f x ∈ Submodule.span R (((bS.smulTower e).map f) '' {ji | P ji.2}) := by
  have h := Submodule.span_smul_of_span_eq_top bS.span_eq (e '' {i | P i})
  have hx' : x ∈ Submodule.span R (Set.range bS • e '' {i | P i}) := by
    rw [h]
    exact hx
  have hfx : f x ∈ (Submodule.span R (Set.range bS • e '' {i | P i})).map (f : M →ₗ[R] N) :=
    Submodule.mem_map_of_mem hx'
  rw [Submodule.map_span] at hfx
  refine Submodule.span_mono ?_ hfx
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨a, ⟨k, rfl⟩, z, ⟨i, hi, rfl⟩, rfl⟩ := Set.mem_smul.mp hy
  exact ⟨(k, i), hi, by simp [Module.Basis.smulTower_apply]⟩

set_option maxHeartbeats 1000000 in
/-- The weight basis of the archimedean Lie algebra adapted to a parabolic and a Levi
subgroup. -/
theorem leviTangentWeightBasis : LeviTangentWeightBasisStatement.{u} := by
  intro F _ _ G Q M' V _ _ _ q iV l' hG hq hV hl d d' hsmooth hsmooth' Ainf ιQ SV
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothChartedSpace F M' hsmooth'
  let := smoothLieGroup F G hsmooth
  have : IsAffineHom V.X.hom := BorelFieldExtension.isAffineHom_source hV.1.isClosedSubgroup
  have : IsAffine V.X.left := isAffine_of_isAffineHom V.X.hom
  obtain ⟨ψ, n, w, -, -, hbasis⟩ :=
    exists_leviCocharacterLieWeightBasis_baseChange F G Q M' V q iV l' hG hq hV hl
  obtain ⟨e, he_eig, he0, he0le, hepos, heposle⟩ := hbasis (InfiniteAdeleRing F)
  obtain ⟨dV, hsmoothV⟩ :=
    Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension _ _ V.X.hom hV.1.smooth hV.1.connectedSpace
  let := realAlgebra F
  have := realAlgebra_finiteDimensional F
  let := kernelRealModule F G
  have := kernelReal_isScalarTower F G
  let BG := tangentKernelAdeleEquiv F hsmooth (tangentKernel_bijective F hsmooth)
  let bA := Module.finBasis ℝ (InfiniteAdeleRing F)
  let E0 := (bA.smulTower e).map BG.symm
  let σ := Fintype.equivFin (Fin (Module.finrank ℝ (InfiniteAdeleRing F)) × Fin n)
  let b := E0.reindex σ
  let w' : Fin (Fintype.card (Fin (Module.finrank ℝ (InfiniteAdeleRing F)) × Fin n)) → ℤ :=
    fun k => w (σ.symm k).2
  have hb : ∀ k, b k = BG.symm (bA (σ.symm k).1 • e (σ.symm k).2) := fun k => by
    simp only [b, E0, Module.Basis.reindex_apply, Module.Basis.map_apply,
      Module.Basis.smulTower_apply]
  have hspan : ∀ (P : ℤ → Prop)
      (X : GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)),
      BG X ∈ Submodule.span (InfiniteAdeleRing F) (e '' {i | P (w i)}) →
        X ∈ Submodule.span ℝ (b '' {k | P (w' k)}) := by
    intro P X hX
    have h := mem_span_smulTower_map bA e BG.symm (fun i => P (w i)) hX
    rw [LinearEquiv.symm_apply_apply] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨ji, hji, rfl⟩
    refine ⟨σ ji, ?_, ?_⟩
    · show P (w (σ.symm (σ ji)).2)
      rw [Equiv.symm_apply_apply]
      exact hji
    · simp only [b, Module.Basis.reindex_apply, Equiv.symm_apply_apply]
      rfl
  let S := (algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (InfiniteAdeleRing F)))
  let u : Fˣ := Units.mk0 2 two_ne_zero
  let t : InfiniteAdelicGroupPoints F M' := M'.constantPoint (gmBasePoint u ≫ ψ.hom.hom) S
  have hιt : ιQ t = G.constantPoint (gmBasePoint u ≫ (ψ ≫ l' ≫ q).hom.hom) S := by
    simp only [ιQ, t, affinePointsTarget_apply, GroupScheme.constantPoint, Category.assoc]
    rfl
  refine ⟨t, _, b, w', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the eigenvector property
    intro k
    rw [hb]
    apply BG.injective
    rw [LinearEquiv.map_smul, LinearEquiv.apply_symm_apply]
    have h1 := tangentKernel_groupTangentConjugation F hsmooth
      (gmBasePoint u ≫ (ψ ≫ l' ≫ q).hom.hom) (BG.symm (bA (σ.symm k).1 • e (σ.symm k).2))
    rw [← hιt] at h1
    refine h1.trans ?_
    have h2 : Additive.ofMul (tangentKernel F hsmooth
        (BG.symm (bA (σ.symm k).1 • e (σ.symm k).2))) = bA (σ.symm k).1 • e (σ.symm k).2 :=
      BG.apply_symm_apply _
    rw [h2, map_smul]
    have h3 : G.constantPoint (gmBasePoint u ≫ (ψ ≫ l' ≫ q).hom.hom) S =
        GroupScheme.constantPoint (Gm (Spec (CommRingCat.of F))).toGrp (gmBasePoint u) S ≫
          (ψ ≫ l' ≫ q).hom.hom := by
      simp only [GroupScheme.constantPoint, Category.assoc]
    rw [hιt, h3, he_eig, characterValue_powerHom_constantPoint_gmBasePoint,
      units_map_two_zpow]
    exact smul_comm _ _ _
  · -- the tangent map of the Levi subgroup is injective
    have : IsClosedImmersion q.hom.hom.left := hq.isClosedSubgroup
    have : Mono q.hom.hom := Over.mono_of_mono_left _
    have : IsClosedImmersion l'.hom.hom.left := hl.isClosedSubgroup
    have : Mono l'.hom.hom := Over.mono_of_mono_left _
    have hmono : Mono (l' ≫ q).hom.hom := by
      rw [Grp.comp_hom_hom]
      infer_instance
    intro Y₁ Y₂ hY
    apply (tangentKernel_bijective F hsmooth').1
    apply Additive.ofMul.injective
    apply Lie.targetMapLinear_injective (l' ≫ q) (InfiniteAdeleRing F)
    rw [← tangentKernel_pointTangent F hsmooth' hsmooth (l' ≫ q) Y₁,
      ← tangentKernel_pointTangent F hsmooth' hsmooth (l' ≫ q) Y₂]
    exact congrArg (fun X => Additive.ofMul (tangentKernel F hsmooth X)) hY
  · -- weight-zero vectors are tangent vectors of the Levi subgroup
    intro k hk
    obtain ⟨y, hy⟩ : bA (σ.symm k).1 • e (σ.symm k).2 ∈
        LinearMap.range (Lie.targetMapLinear (l' ≫ q) (InfiniteAdeleRing F)) :=
      Submodule.smul_mem _ _ (he0 _ hk)
    obtain ⟨Y, hY⟩ := (tangentKernel_bijective F hsmooth').2 (Additive.toMul y)
    refine ⟨Y, ?_⟩
    rw [hb]
    apply BG.injective
    rw [LinearEquiv.apply_symm_apply, ← hy]
    refine (tangentKernel_pointTangent F hsmooth' hsmooth (l' ≫ q) Y).trans ?_
    rw [hY]
    rfl
  · -- tangent vectors of the Levi subgroup are combinations of weight-zero vectors
    intro Y
    have hmem : BG (mfderiv 𝓘(ℝ, smoothModel F d') 𝓘(ℝ, smoothModel F d) ιQ 1 Y) ∈
        Submodule.span (InfiniteAdeleRing F) (e '' {i | w i = 0}) :=
      he0le ⟨Additive.ofMul (tangentKernel F hsmooth' Y),
        (tangentKernel_pointTangent F hsmooth' hsmooth (l' ≫ q) Y).symm⟩
    exact hspan (fun m => m = 0) _ hmem
  · -- positive-weight vectors are velocities of curves in the unipotent radical
    intro k hk
    obtain ⟨y, hy⟩ : bA (σ.symm k).1 • e (σ.symm k).2 ∈
        LinearMap.range (Lie.targetMapLinear (iV ≫ q) (InfiniteAdeleRing F)) :=
      Submodule.smul_mem _ _ (hepos _ hk)
    obtain ⟨Y, hY⟩ := (tangentKernel_bijective F hsmoothV).2 (Additive.toMul y)
    let := smoothChartedSpace F V hsmoothV
    have := smoothIsManifold F V hsmoothV
    obtain ⟨cV, hcV, hcV0, -, hcV'⟩ :=
      Langlands.Geometry.Manifold.InvolutionFixedCurve.exists_contMDiff_curve_fixed
        (E := smoothModel F dV) (M := InfiniteAdelicGroupPoints F V) id contMDiff_id
        (fun _ => rfl) 1 rfl Y (by rw [mfderiv_id]; rfl)
    let ιV := V.affinePointsTarget (iV ≫ q) Ainf
    have hιV : ContMDiff 𝓘(ℝ, smoothModel F dV) 𝓘(ℝ, smoothModel F d) ∞ ιV :=
      contMDiff_affinePointsTarget F hsmoothV hsmooth (iV ≫ q)
    have hcomp : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, smoothModel F d) ∞ (ιV ∘ cV) := hιV.comp hcV
    refine ⟨ιV ∘ cV, hcomp, ?_, fun s => ⟨cV s, rfl⟩, ?_⟩
    · show ιV (cV 0) = 1
      rw [hcV0]
      exact map_one _
    · have hchain := mfderiv_comp_apply_of_eq' (g := ιV) (f := cV)
        (hιV.mdifferentiable (by simp) 1) (hcV.mdifferentiable (by simp) 0) hcV0 (1 : ℝ)
      refine hchain.trans ?_
      rw [hcV', hb]
      apply BG.injective
      rw [LinearEquiv.apply_symm_apply, ← hy]
      refine (tangentKernel_pointTangent F hsmoothV hsmooth (iV ≫ q) Y).trans ?_
      rw [hY]
      rfl
  · -- velocities of curves in the unipotent radical are combinations of positive vectors
    intro c hc hc0 hcV
    have : IsClosedImmersion iV.hom.hom.left := hV.1.isClosedSubgroup
    have : IsClosedImmersion q.hom.hom.left := hq.isClosedSubgroup
    have : IsClosedImmersion (iV ≫ q).hom.hom.left := by
      change IsClosedImmersion (iV.hom.hom.left ≫ q.hom.hom.left)
      infer_instance
    have hmem := tangentKernel_curve_mem_range F hsmooth (iV ≫ q) c hc hc0 hcV
    exact hspan (fun m => 0 < m) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, smoothModel F d) c 0 (1 : ℝ))
      (heposle hmem)

end Langlands.Global
