import Langlands.Global.InfiniteAdelicRadicalDerivative
import Langlands.Global.InfiniteAdelicTangentKernelBracket
import Langlands.Global.InfiniteAdelicTangentKernelNaturality

/-! # The derivative of the normalizing factor as a real trace on the radical directions

Let `Q = M ⋉ V` be a parabolic of a connected reductive group `G` over a number field, and let
`V_ℝ` be a real subspace of the Lie algebra of `G(F_∞)` that `tangentKernel` carries onto the
image of `Lie V ⊗ F_∞`. For a morphism `c : H ⟶ M` and a tangent vector `Y` of `H(F_∞)`, the
derivative at the identity of `m ↦ δ_Q(c(m))^{-1/2}` along `Y` is `-1/2` times the real trace
of `ad (dι Y)` on `V_ℝ`, where `ι = c ≫ l ≫ q`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology AdelicGroupPoints

attribute [local instance] Lie.kernelLieRingOfField Lie.kernelLieAlgebraOfField

variable (F : Type u) [Field F] [NumberField F]

section Inverse

variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] {d : ℕ}
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)

/-- The inverse of the bijection `tangentKernel`. -/
def tangentKernelInv (x : Additive (lieKernel G (InfiniteAdeleRing F))) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) :=
  (Equiv.ofBijective _ (tangentKernel_bijective F hsmooth)).symm x.toMul

theorem tangentKernel_tangentKernelInv (x : Additive (lieKernel G (InfiniteAdeleRing F))) :
    tangentKernel F hsmooth (tangentKernelInv F hsmooth x) = x.toMul :=
  (Equiv.ofBijective _ (tangentKernel_bijective F hsmooth)).apply_symm_apply x.toMul

theorem tangentKernelInv_tangentKernel
    (X : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) :
    tangentKernelInv F hsmooth (Additive.ofMul (tangentKernel F hsmooth X)) = X :=
  (Equiv.ofBijective _ (tangentKernel_bijective F hsmooth)).symm_apply_apply X

theorem tangentKernelInv_add (x y : Additive (lieKernel G (InfiniteAdeleRing F))) :
    tangentKernelInv F hsmooth (x + y) =
      tangentKernelInv F hsmooth x + tangentKernelInv F hsmooth y := by
  apply (tangentKernel_bijective F hsmooth).1
  rw [tangentKernel_add, tangentKernel_tangentKernelInv, tangentKernel_tangentKernelInv,
    tangentKernel_tangentKernelInv]
  rfl

theorem tangentKernelInv_smul (r : ℝ) (x : Additive (lieKernel G (InfiniteAdeleRing F))) :
    tangentKernelInv F hsmooth (realAdele F r • x) = r • tangentKernelInv F hsmooth x := by
  apply (tangentKernel_bijective F hsmooth).1
  rw [tangentKernel_smul, tangentKernel_tangentKernelInv, tangentKernel_tangentKernelInv]
  rfl

end Inverse


section Radical

variable {G Q V : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine V.X.left]
  {q : Q ⟶ G} {iV : V ⟶ Q} {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

/-- The real directions of `G(F_∞)` given by `Lie V ⊗ F_∞`: `w ↦ B⁻¹(Lie (iV ≫ q) w)`. -/
def radicalTangent (w : Additive (lieKernel V (InfiniteAdeleRing F))) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) :=
  tangentKernelInv F hsmooth (Lie.targetMapLinear (iV ≫ q) (InfiniteAdeleRing F) w)

theorem tangentKernel_radicalTangent (w : Additive (lieKernel V (InfiniteAdeleRing F))) :
    Additive.ofMul (tangentKernel F hsmooth (radicalTangent F (q := q) (iV := iV) hsmooth w)) =
      Lie.targetMapLinear (iV ≫ q) (InfiniteAdeleRing F) w :=
  congrArg Additive.ofMul (tangentKernel_tangentKernelInv F hsmooth _)

theorem radicalTangent_add (w w' : Additive (lieKernel V (InfiniteAdeleRing F))) :
    radicalTangent F (q := q) (iV := iV) hsmooth (w + w') =
      radicalTangent F (q := q) (iV := iV) hsmooth w +
        radicalTangent F (q := q) (iV := iV) hsmooth w' := by
  rw [radicalTangent, map_add, tangentKernelInv_add]
  rfl

theorem radicalTangent_smul (r : ℝ) (w : Additive (lieKernel V (InfiniteAdeleRing F))) :
    radicalTangent F (q := q) (iV := iV) hsmooth (realAdele F r • w) =
      r • radicalTangent F (q := q) (iV := iV) hsmooth w := by
  rw [radicalTangent, map_smul, tangentKernelInv_smul]
  rfl

theorem radicalTangent_injective [Mono q.hom.hom] [Mono iV.hom.hom] :
    Function.Injective (radicalTangent F (q := q) (iV := iV) hsmooth) := by
  intro w w' h
  have : Mono (iV ≫ q).hom.hom := by
    rw [Grp.comp_hom_hom]
    infer_instance
  apply Lie.targetMapLinear_injective (iV ≫ q) (InfiniteAdeleRing F)
  rw [← tangentKernel_radicalTangent, ← tangentKernel_radicalTangent, h]

end Radical

section Span

variable {G Q V : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine V.X.left]
  {q : Q ⟶ G} {iV : V ⟶ Q} {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (VR : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    Submodule ℝ (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)))
  (hVR : ∀ X, X ∈ VR ↔ Additive.ofMul (tangentKernel F hsmooth X) ∈
    LinearMap.range (Lie.targetMapLinear (iV ≫ q) (InfiniteAdeleRing F)))

include hVR in
theorem radicalTangent_mem (w : Additive (lieKernel V (InfiniteAdeleRing F))) :
    radicalTangent F (q := q) (iV := iV) hsmooth w ∈ VR :=
  (hVR _).mpr ⟨w, (tangentKernel_radicalTangent F hsmooth w).symm⟩

include hVR in
theorem exists_radicalTangent_eq {X} (hX : X ∈ VR) :
    ∃ w, radicalTangent F (q := q) (iV := iV) hsmooth w = X := by
  obtain ⟨w, hw⟩ := (hVR X).mp hX
  exact ⟨w, by rw [radicalTangent, hw, tangentKernelInv_tangentKernel]⟩

end Span

section Trace

variable {G Q M V H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  [IsAffine V.X.left] [LocallyOfFiniteType V.X.hom] [IsAffine H.X.left]
  {q : Q ⟶ G} {iV : V ⟶ Q} {l : M ⟶ Q}
  {d e : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hsmoothH : SmoothOfRelativeDimension e H.X.hom)

omit [LocallyOfFiniteType M.X.hom] in
set_option maxRecDepth 8192 in
/-- `radicalTangent` intertwines `ad` on `Lie V ⊗ F_∞` with `ad (dι Y)`, `ι = c ≫ l ≫ q`. -/
theorem radicalTangent_normalAdjoint (hV : (SubgroupFunctor.range iV).IsNormal)
    [Mono iV.hom.hom] (c : H ⟶ M)
    (Y : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F H hsmoothH
      GroupLieAlgebra 𝓘(ℝ, smoothModel F e) (InfiniteAdelicGroupPoints F H))
    (w : Additive (lieKernel V (InfiniteAdeleRing F))) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F G hsmooth
    letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3) (InfiniteAdelicGroupPoints F G) :=
      LieGroup.of_le (n := ∞) (by simp)
    radicalTangent F (q := q) (iV := iV) hsmooth
        (Lie.normalAdjoint iV hV (InfiniteAdeleRing F)
          (Lie.targetMapLinear l (InfiniteAdeleRing F)
            (Lie.targetMapLinear c (InfiniteAdeleRing F)
              (Additive.ofMul (tangentKernel F hsmoothH Y)))) w) =
      ⁅pointTangent F hsmoothH hsmooth (c ≫ l ≫ q) Y,
        radicalTangent F (q := q) (iV := iV) hsmooth w⁆ := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3) (InfiniteAdelicGroupPoints F G) :=
    LieGroup.of_le (n := ∞) (by simp)
  have key : Additive.ofMul (tangentKernel F hsmooth (radicalTangent F (q := q) (iV := iV) hsmooth
        (Lie.normalAdjoint iV hV (InfiniteAdeleRing F)
          (Lie.targetMapLinear l (InfiniteAdeleRing F)
            (Lie.targetMapLinear c (InfiniteAdeleRing F)
              (Additive.ofMul (tangentKernel F hsmoothH Y)))) w))) =
      Additive.ofMul (tangentKernel F hsmooth ⁅pointTangent F hsmoothH hsmooth (c ≫ l ≫ q) Y,
        radicalTangent F (q := q) (iV := iV) hsmooth w⁆) := by
    rw [tangentKernel_lie, tangentKernel_pointTangent, tangentKernel_radicalTangent,
      tangentKernel_radicalTangent,
      targetMapLinear_comp_apply (InfiniteAdeleRing F) iV q,
      targetMapLinear_comp_apply (InfiniteAdeleRing F) iV q,
      targetMapLinear_comp_apply (InfiniteAdeleRing F) c (l ≫ q),
      targetMapLinear_comp_apply (InfiniteAdeleRing F) l q,
      Lie.targetMapLinear_normalAdjoint, Lie.targetMapLinear_lie]
  exact (tangentKernel_bijective F hsmooth).1 (Additive.ofMul.injective key)

omit [LocallyOfFiniteType M.X.hom] in
set_option maxRecDepth 8192 in
/-- `ad (dι Y)` preserves a real subspace `V_ℝ` that `tangentKernel` carries onto the image of
`Lie V ⊗ F_∞`. -/
theorem pointTangent_lie_mem (hV : (SubgroupFunctor.range iV).IsNormal) [Mono iV.hom.hom]
    (c : H ⟶ M)
    (VR : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      Submodule ℝ (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)))
    (hVR : ∀ X, X ∈ VR ↔ Additive.ofMul (tangentKernel F hsmooth X) ∈
      LinearMap.range (Lie.targetMapLinear (iV ≫ q) (InfiniteAdeleRing F)))
    (Y : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F H hsmoothH
      GroupLieAlgebra 𝓘(ℝ, smoothModel F e) (InfiniteAdelicGroupPoints F H)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F G hsmooth
    letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3) (InfiniteAdelicGroupPoints F G) :=
      LieGroup.of_le (n := ∞) (by simp)
    ∀ X ∈ VR, LieAlgebra.ad ℝ _ (pointTangent F hsmoothH hsmooth (c ≫ l ≫ q) Y) X ∈ VR := by
  intro X hX
  obtain ⟨w, rfl⟩ := exists_radicalTangent_eq F hsmooth VR hVR hX
  rw [LieAlgebra.ad_apply, ← radicalTangent_normalAdjoint F hsmooth hsmoothH hV c Y w]
  exact radicalTangent_mem F hsmooth VR hVR _

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
/-- The derivative at the identity of the normalizing factor `m ↦ δ_Q(c(m))^{-1/2}` along `Y` is
`-1/2` times the real trace of `ad (dι Y)` on `V_ℝ`, for `ι = c ≫ l ≫ q` and any real subspace
`V_ℝ` that `tangentKernel` carries onto the image of `Lie V ⊗ F_∞`. -/
theorem identityDerivative_halfModulus_eq_radicalTrace
    (hG : IsConnectedReductive G) (hq : IsParabolicSubgroup q)
    (hV : LeviSubgroup.IsGeometricUnipotentRadical iV) (hl : IsRationalLeviSubgroup l)
    [Mono q.hom.hom] [Mono iV.hom.hom] (c : H ⟶ M)
    (VR : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      Submodule ℝ (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)))
    (hVR : ∀ X, X ∈ VR ↔ Additive.ofMul (tangentKernel F hsmooth X) ∈
      LinearMap.range (Lie.targetMapLinear (iV ≫ q) (InfiniteAdeleRing F)))
    (Y : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F H hsmoothH
      GroupLieAlgebra 𝓘(ℝ, smoothModel F e) (InfiniteAdelicGroupPoints F H)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F G hsmooth
    letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3) (InfiniteAdelicGroupPoints F G) :=
      LieGroup.of_le (n := ∞) (by simp)
    identityDerivative F hsmoothH (fun m => parameterPower F Q (-halfModulusParameter F Q)
        (map F H Q (c ≫ l) (ofInfinite F H m))) Y =
      (-1 / 2 : ℂ) * ((LinearMap.trace ℝ VR
        ((LieAlgebra.ad ℝ _ (pointTangent F hsmoothH hsmooth (c ≫ l ≫ q) Y)).restrict
          (pointTangent_lie_mem F hsmooth hsmoothH hV.1.isNormal c VR hVR Y)) : ℝ) : ℂ) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3) (InfiniteAdelicGroupPoints F G) :=
    LieGroup.of_le (n := ∞) (by simp)
  have hd := mfderiv_halfModulus_one_eq_radicalTrace F hsmoothH hG hq hV hl c Y
  refine Eq.trans ?_ (hd.trans ?_)
  · rfl
  congr 2
  let W := Additive (lieKernel V (InfiniteAdeleRing F))
  let := realAlgebra F
  let : Module ℝ W := Module.compHom W (algebraMap ℝ (InfiniteAdeleRing F))
  have hM : IsScalarTower ℝ (InfiniteAdeleRing F) W :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  obtain ⟨_, _⟩ := Lie.free_finite_lieKernel (k := F) (InfiniteAdeleRing F) V
  rw [← trace_restrictScalars_eq_sum F hM]
  let f : W →ₗ[ℝ] VR :=
    { toFun := fun w => ⟨radicalTangent F (q := q) (iV := iV) hsmooth w,
        radicalTangent_mem F hsmooth VR hVR w⟩
      map_add' := fun w w' => Subtype.ext (radicalTangent_add F hsmooth w w')
      map_smul' := fun r w => Subtype.ext (radicalTangent_smul F hsmooth r w) }
  have hf : Function.Bijective f := by
    refine ⟨fun w w' h => radicalTangent_injective F hsmooth (congrArg Subtype.val h), ?_⟩
    rintro ⟨X, hX⟩
    obtain ⟨w, hw⟩ := exists_radicalTangent_eq F hsmooth VR hVR hX
    exact ⟨w, Subtype.ext hw⟩
  let eV := LinearEquiv.ofBijective f hf
  have := hM
  rw [← LinearMap.trace_conj' _ eV]
  congr 1
  apply LinearMap.ext
  intro x
  obtain ⟨w, rfl⟩ := eV.surjective x
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  exact radicalTangent_normalAdjoint F hsmooth hsmoothH hV.1.isNormal c Y w

end Trace

end Langlands.Global.InfiniteAdelicGroupPoints
