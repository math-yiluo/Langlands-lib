import Langlands.BruhatTits.IntegralModels.TorusRootModelComparison
import Langlands.BruhatTits.IntegralModels.RootDepthKernelStatement
import Langlands.GroupScheme.KernelIsoGeometry
import Langlands.GroupScheme.KernelOrderedProductChart

/-! # Kernels for actual torus/root comparison maps -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels.TorusRootModelFamilyData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
  [IsAffineHom G.X.hom]
  {C : MaximalUnramified.BuildingData F G} {E : UnramifiedZeroDatum F G}
  {x : C.Apartment} {Ω Ω' : Set C.Apartment}
  {N N' : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G}
  (A : TorusRootModelFamilyData C E x Ω N)
  (B : TorusRootModelFamilyData C E x Ω' N')
  (hext : IntegralModel.HasSmoothHomExtension
    (R := fixedFieldIntegers F) (L := inertiaFixedField F))
  (hdepth : ∀ a : relativeRoots C.i,
    C.apartment.rootFixerDepth a x Ω ≤ C.apartment.rootFixerDepth a x Ω')

/-- The actual special-fibre kernel of the comparison at a torus/root index. -/
def comparisonKernel (j : Option (relativeRoots C.i)) :
    GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))) :=
  kernel (A.comparisonHom B hext hdepth j).specialFibreMap

/-- Every comparison kernel is affine, independently of the root-kernel
smoothness and connectedness input. -/
theorem comparisonKernel_isAffineHom (j : Option (relativeRoots C.i)) :
    IsAffineHom (A.comparisonKernel B hext hdepth j).X.hom := by
  have : IsAffineHom (B.model j).specialFibre.X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd
      (B.model j).group.X.hom (IntegralModel.residueBaseMap (fixedFieldIntegers F)))
    exact MorphismProperty.pullback_snd _ _ (B.model j).affine
  have : IsAffineHom (A.model j).specialFibre.X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd
      (A.model j).group.X.hom (IntegralModel.residueBaseMap (fixedFieldIntegers F)))
    exact MorphismProperty.pullback_snd _ _ (A.model j).affine
  change IsAffineHom (kernel (A.comparisonHom B hext hdepth j).specialFibreMap).X.hom
  rw [← Over.w (kernelι (A.comparisonHom B hext hdepth j).specialFibreMap).hom.hom]
  infer_instance

/-- The torus kernel is trivial and the root-depth input supplies the actual
root-factor geometry. No root-depth theorem is assumed implicitly. -/
theorem comparisonKernel_smooth_affine_connected
    (hroot : UnramifiedRootDepthKernelStatement.{u})
    (j : Option (relativeRoots C.i)) :
    Smooth (A.comparisonKernel B hext hdepth j).X.hom ∧
      IsAffineHom (A.comparisonKernel B hext hdepth j).X.hom ∧
      ConnectedSpace (A.comparisonKernel B hext hdepth j).X.left := by
  have haff := A.comparisonKernel_isAffineHom B hext hdepth j
  cases j with
  | none =>
    have hiso : IsIso (A.comparisonHom B hext hdepth none).specialFibreMap := by
      rw [← A.torusSpecialFibreComparisonIso_hom B hext hdepth]
      infer_instance
    exact ⟨(smooth_isAffineHom_kernel_of_isIso
      (A.comparisonHom B hext hdepth none).specialFibreMap).1,
      haff, connectedSpace_kernel_of_isIso
        (A.comparisonHom B hext hdepth none).specialFibreMap⟩
  | some a =>
    have h := hroot F G C x a _ _ (hdepth a) (A.rootModel a) (B.rootModel a)
      ((B.rootModel a).genericIso (A.rootModel a)).hom
      ((B.rootModel a).genericIso_hom_comp (A.rootModel a))
      ((A.rootModel a).comparisonHom (B.rootModel a) hext (hdepth a))
    exact ⟨h.1, haff, h.2.1⟩

variable {n : ℕ} (e : Fin n → Option (relativeRoots C.i))
  (ψ : N'.Hom N (𝟙 G))

/-- Reindex the actual family comparison by any finite list of torus/root
indices. Monomorphic ordered charts and a full-kernel lift identify the
ambient special-fibre kernel with the product of actual factor kernels. -/
def orderedComparisonKernelIso
    [Mono (RelativeRoot.orderedMultiplication
      (fun i => (B.modelMap (e i)).hom))]
    [Mono (RelativeRoot.orderedMultiplication
      (fun i => (A.modelMap (e i)).hom))]
    (l : (kernel ψ.specialFibreMap).X ⟶
      (Over.pullback (IntegralModel.residueBaseMap (fixedFieldIntegers F))).obj
        (∏ᶜ fun i => (B.model (e i)).group).X)
    (hl : l ≫ (Over.pullback (IntegralModel.residueBaseMap (fixedFieldIntegers F))).map
      (RelativeRoot.orderedMultiplication (fun i => (B.modelMap (e i)).hom)) =
      (kernelι ψ.specialFibreMap).hom.hom) :
    (∏ᶜ fun i => A.comparisonKernel B hext hdepth (e i)).X ≅
      (kernel ψ.specialFibreMap).X :=
  RelativeRoot.orderedMultiplicationKernelIso_baseChange
    (IntegralModel.residueBaseMap (fixedFieldIntegers F))
    (fun i => (B.modelMap (e i)).hom) (fun i => (A.modelMap (e i)).hom)
    ψ.hom (fun i => (A.comparisonHom B hext hdepth (e i)).hom)
    (fun i => (A.comparisonHom_comp B hext hdepth ψ (e i)).symm) l hl

include hext hdepth in
/-- The root-depth result, monomorphic integral ordered charts and a lift of
the entire special-fibre kernel give ambient smoothness and connectedness. -/
theorem smooth_connected_kernel_of_orderedCharts
    (hroot : UnramifiedRootDepthKernelStatement.{u})
    [Mono (RelativeRoot.orderedMultiplication
      (fun i => (B.modelMap (e i)).hom))]
    [Mono (RelativeRoot.orderedMultiplication
      (fun i => (A.modelMap (e i)).hom))]
    (l : (kernel ψ.specialFibreMap).X ⟶
      (Over.pullback (IntegralModel.residueBaseMap (fixedFieldIntegers F))).obj
        (∏ᶜ fun i => (B.model (e i)).group).X)
    (hl : l ≫ (Over.pullback (IntegralModel.residueBaseMap (fixedFieldIntegers F))).map
      (RelativeRoot.orderedMultiplication (fun i => (B.modelMap (e i)).hom)) =
      (kernelι ψ.specialFibreMap).hom.hom) :
    Smooth (kernel ψ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel ψ.specialFibreMap).X.left :=
  RelativeRoot.smooth_connected_orderedMultiplicationKernel_baseChange
    (IntegralModel.residueBaseMap (fixedFieldIntegers F))
    (fun i => (B.modelMap (e i)).hom) (fun i => (A.modelMap (e i)).hom)
    ψ.hom (fun i => (A.comparisonHom B hext hdepth (e i)).hom)
    (fun i => (A.comparisonHom_comp B hext hdepth ψ (e i)).symm) l hl
    (fun i => A.comparisonKernel_smooth_affine_connected B hext hdepth hroot (e i))

end Langlands.BruhatTits.IntegralModels.TorusRootModelFamilyData
