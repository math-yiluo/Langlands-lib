import Langlands.GroupScheme.RelativeUnipotent.Basic
import Langlands.AlgebraicGeometry.Modules.PullbackAffineSections
import Langlands.AlgebraicGeometry.Modules.SectionPullbackBridge

/-! # Canonical tensor coordinates for affine pullback sections -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

namespace Langlands.GroupScheme.RelativeUnipotent.AffineSectionCoordinates

open Langlands.SchemeModule Langlands.Scheme.Modules

variable {S : Scheme.{u}} (M : S.Modules)

/-- Tensor coordinates with the actual structural map on global functions. -/
abbrev Points (T : Over S) :=
  (ModuleCat.extendScalars (T.hom.appLE ⊤ ⊤ le_top).hom).obj
    (ModuleCat.of Γ(S, ⊤) (GlobalSections M))

/-- The canonical tensor map induced by the module-pullback unit. -/
def toSection (T : Over S) :
    Points M T →+ GlobalSections ((Scheme.Modules.pullback T.hom).obj M) :=
  (pullbackTensorMap T.hom M (show ⊤ ≤ T.hom ⁻¹ᵁ ⊤ from le_top)).hom.toAddMonoidHom

@[simp]
lemma toSection_tmul (T : Over S) (s : Γ(T.left, ⊤)) (m : GlobalSections M) :
    toSection M T (s ⊗ₜ[Γ(S, ⊤), (T.hom.appLE ⊤ ⊤ le_top).hom] m) =
      s • pullbackSection T.hom M m := by
  change pullbackTensorMap T.hom M _ _ = _
  rw [pullbackTensorMap_tmul, pullbackSection_eq_sectionPullback]
  exact congrArg (s • ·) (sectionPullbackLE_self T.hom M ⊤ m)

/-- The canonical tensor map is bijective when both schemes are affine. -/
lemma toSection_bijective [IsAffine S] [M.IsQuasicoherent]
    (T : Over S) [IsAffine T.left] : Function.Bijective (toSection M T) :=
  pullbackTensorMap_bijective T.hom M _ (isAffineOpen_top T.left) (isAffineOpen_top S)

/-- Sections on an affine test scheme in their canonical tensor coordinates. -/
def equiv [IsAffine S] [M.IsQuasicoherent] (T : Over S) [IsAffine T.left] :
    Points M T ≃+ GlobalSections ((Scheme.Modules.pullback T.hom).obj M) :=
  AddEquiv.ofBijective (toSection M T) (toSection_bijective M T)

/-- The actual map on global functions is linear for the two structural algebras. -/
def scalarMap {T W : Over S} (a : W ⟶ T) :
    letI := (T.hom.appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI := (W.hom.appLE ⊤ ⊤ le_top).hom.toAlgebra
    Γ(T.left, ⊤) →ₗ[Γ(S, ⊤)] Γ(W.left, ⊤) := by
  letI := (T.hom.appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI := (W.hom.appLE ⊤ ⊤ le_top).hom.toAlgebra
  exact
    { toFun := a.left.appTop
      map_add' := map_add a.left.appTop.hom
      map_smul' := fun r s => by
        change a.left.appTop (T.hom.appLE ⊤ ⊤ le_top r * s) =
          W.hom.appLE ⊤ ⊤ le_top r * a.left.appTop s
        have hT : T.hom.appLE ⊤ ⊤ le_top = T.hom.appTop := by
          simp [Scheme.Hom.appLE]
        have hW : W.hom.appLE ⊤ ⊤ le_top = W.hom.appTop := by
          simp [Scheme.Hom.appLE]
        rw [hT, hW, map_mul]
        congr 1
        exact congrArg (fun f => f.appTop r) (Over.w a) }

/-- Restriction on the first tensor factor, keeping the coefficient section fixed. -/
def pullback {T W : Over S} (a : W ⟶ T) : Points M T →+ Points M W := by
  letI := (T.hom.appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI := (W.hom.appLE ⊤ ⊤ le_top).hom.toAlgebra
  exact (TensorProduct.map (scalarMap a) LinearMap.id).toAddMonoidHom

@[simp]
lemma pullback_tmul {T W : Over S} (a : W ⟶ T)
    (s : Γ(T.left, ⊤)) (m : GlobalSections M) :
    pullback M a (s ⊗ₜ[Γ(S, ⊤), (T.hom.appLE ⊤ ⊤ le_top).hom] m) =
      a.left.appTop s ⊗ₜ[Γ(S, ⊤), (W.hom.appLE ⊤ ⊤ le_top).hom] m := rfl

/-- Canonical comparison maps identify iterated pullback of a coefficient section. -/
lemma sectionPullback_pullbackSection {T W : Over S} (a : W ⟶ T)
    (m : GlobalSections M) :
    RelativeUnipotent.sectionPullback M a (pullbackSection T.hom M m) =
      pullbackSection W.hom M m := by
  have htop {X Y : Scheme.{u}} (f : X ⟶ Y) (N : Y.Modules) (n : GlobalSections N) :
      pullbackSection f N n = sectionPullbackLE f N (show ⊤ ≤ f ⁻¹ᵁ ⊤ from le_top) n := by
    rw [pullbackSection_eq_sectionPullback]
    exact (sectionPullbackLE_self f N ⊤ n).symm
  unfold RelativeUnipotent.sectionPullback
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    htop]
  rw [pullbackComp_hom_sectionPullbackLE a.left T.hom M le_top le_top le_top m]
  exact pullbackCongr_hom_sectionPullbackLE (Over.w a) M le_top le_top m

/-- Canonical pullback of relative sections preserves addition. -/
lemma sectionPullback_add {T W : Over S} (a : W ⟶ T)
    (s t : GlobalSections ((Scheme.Modules.pullback T.hom).obj M)) :
    RelativeUnipotent.sectionPullback M a (s + t) =
      RelativeUnipotent.sectionPullback M a s +
        RelativeUnipotent.sectionPullback M a t := by
  simp only [RelativeUnipotent.sectionPullback, pullbackSection_eq_sectionPullback, map_add]

/-- Canonical pullback of relative sections preserves zero. -/
lemma sectionPullback_zero {T W : Over S} (a : W ⟶ T) :
    RelativeUnipotent.sectionPullback M a 0 = 0 := by
  simp only [RelativeUnipotent.sectionPullback, pullbackSection_eq_sectionPullback, map_zero]

/-- Canonical pullback of relative sections is semilinear for the actual ring map. -/
lemma sectionPullback_smul {T W : Over S} (a : W ⟶ T) (r : Γ(T.left, ⊤))
    (s : GlobalSections ((Scheme.Modules.pullback T.hom).obj M)) :
    RelativeUnipotent.sectionPullback M a (r • s) =
      a.left.appTop r • RelativeUnipotent.sectionPullback M a s := by
  simp only [RelativeUnipotent.sectionPullback, pullbackSection_eq_sectionPullback,
    LinearMap.map_smulₛₗ, Scheme.Modules.Hom.app_smul]
  rfl

/-- The tensor comparison is natural for canonical section pullback. -/
lemma toSection_natural {T W : Over S} (a : W ⟶ T) (z : Points M T) :
    toSection M W (pullback M a z) =
      RelativeUnipotent.sectionPullback M a (toSection M T z) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' =>
      rw [map_add, map_add, map_add, sectionPullback_add, hz, hz']
  | tmul r m =>
      rw [pullback_tmul, toSection_tmul, toSection_tmul, sectionPullback_smul,
        sectionPullback_pullbackSection]

/-- Inverse affine coordinates also commute with canonical section pullback. -/
lemma equiv_symm_natural [IsAffine S] [M.IsQuasicoherent]
    {T W : Over S} [IsAffine T.left] [IsAffine W.left] (a : W ⟶ T)
    (s : GlobalSections ((Scheme.Modules.pullback T.hom).obj M)) :
    (equiv M W).symm (RelativeUnipotent.sectionPullback M a s) =
      pullback M a ((equiv M T).symm s) := by
  apply (equiv M W).injective
  rw [AddEquiv.apply_symm_apply]
  change _ = toSection M W (pullback M a ((equiv M T).symm s))
  rw [toSection_natural]
  exact congrArg (RelativeUnipotent.sectionPullback M a)
    ((equiv M T).apply_symm_apply s).symm

end Langlands.GroupScheme.RelativeUnipotent.AffineSectionCoordinates
