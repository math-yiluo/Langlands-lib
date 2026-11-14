import Langlands.BruhatTits.IntegralModels.TorusRootModelKernel
import Langlands.GroupScheme.IntegralModel.SpecialFibreKernelOpenContainment
import Langlands.Galois.Local.SeparableUnramifiedArithmeticProof

/-! # Ordered open charts for the full special-fibre kernel -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
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
  {n : ℕ} (e : Fin n → Option (relativeRoots C.i))
  (ψ : N'.Hom N (𝟙 G))

/-- A closed-point range condition on killed integral sections places the
entire special-fibre kernel in the residue pullback of an ordered open chart. -/
theorem exists_orderedOpenChartKernel_lift
    [IsOpenImmersion (RelativeRoot.orderedMultiplication
      (fun i => (B.modelMap (e i)).hom)).left]
    (hN' : N'.IsSmooth)
    (hrange : ∀ s : N'.integralSections,
      N.reduction (rationalPoints.map ψ.hom s) = 1 →
        s.left (IsLocalRing.closedPoint (fixedFieldIntegers F)) ∈
          Set.range (RelativeRoot.orderedMultiplication
            (fun i => (B.modelMap (e i)).hom)).left) :
    ∃ l : (kernel ψ.specialFibreMap).X ⟶
      (Over.pullback (IntegralModel.residueBaseMap (fixedFieldIntegers F))).obj
        (∏ᶜ fun i => (B.model (e i)).group).X,
      l ≫ (Over.pullback (IntegralModel.residueBaseMap (fixedFieldIntegers F))).map
        (RelativeRoot.orderedMultiplication (fun i => (B.modelMap (e i)).hom)) =
          (kernelι ψ.specialFibreMap).hom.hom := by
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  let : Algebra 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (residueToFixedField F).toAlgebra
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).isAlgClosed
  exact ψ.exists_specialFibreKernel_lift hN'
    (RelativeRoot.orderedMultiplication (fun i => (B.modelMap (e i)).hom)) hrange

variable
  (hext : IntegralModel.HasSmoothHomExtension
    (R := fixedFieldIntegers F) (L := inertiaFixedField F))
  (hdepth : ∀ a : relativeRoots C.i,
    C.apartment.rootFixerDepth a x Ω ≤ C.apartment.rootFixerDepth a x Ω')

/-- The full ambient special-fibre kernel is the product of the actual factor
kernels when the source ordered chart is open and contains the closed points
of all killed integral sections, and the target ordered chart is monomorphic. -/
def orderedOpenChartKernelIso
    [IsOpenImmersion (RelativeRoot.orderedMultiplication
      (fun i => (B.modelMap (e i)).hom)).left]
    [Mono (RelativeRoot.orderedMultiplication
      (fun i => (A.modelMap (e i)).hom))]
    (hN' : N'.IsSmooth)
    (hrange : ∀ s : N'.integralSections,
      N.reduction (rationalPoints.map ψ.hom s) = 1 →
        s.left (IsLocalRing.closedPoint (fixedFieldIntegers F)) ∈
          Set.range (RelativeRoot.orderedMultiplication
            (fun i => (B.modelMap (e i)).hom)).left) :
    (∏ᶜ fun i => A.comparisonKernel B hext hdepth (e i)).X ≅
      (kernel ψ.specialFibreMap).X := by
  letI : Mono (RelativeRoot.orderedMultiplication
      (fun i => (B.modelMap (e i)).hom)) := Over.mono_of_mono_left _
  let h := B.exists_orderedOpenChartKernel_lift e ψ hN' hrange
  exact A.orderedComparisonKernelIso B hext hdepth e ψ
    (Classical.choose h) (Classical.choose_spec h)

include hext hdepth in
/-- Smoothness and connectedness follow from the explicit root-depth theorem
and the closed-point range condition for an ordered open source chart. -/
theorem smooth_connected_kernel_of_orderedOpenCharts
    (hroot : UnramifiedRootDepthKernelStatement.{u})
    [IsOpenImmersion (RelativeRoot.orderedMultiplication
      (fun i => (B.modelMap (e i)).hom)).left]
    [Mono (RelativeRoot.orderedMultiplication
      (fun i => (A.modelMap (e i)).hom))]
    (hN' : N'.IsSmooth)
    (hrange : ∀ s : N'.integralSections,
      N.reduction (rationalPoints.map ψ.hom s) = 1 →
        s.left (IsLocalRing.closedPoint (fixedFieldIntegers F)) ∈
          Set.range (RelativeRoot.orderedMultiplication
            (fun i => (B.modelMap (e i)).hom)).left) :
    Smooth (kernel ψ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel ψ.specialFibreMap).X.left := by
  let : Mono (RelativeRoot.orderedMultiplication
      (fun i => (B.modelMap (e i)).hom)) := Over.mono_of_mono_left _
  obtain ⟨l, hl⟩ := B.exists_orderedOpenChartKernel_lift e ψ hN' hrange
  exact A.smooth_connected_kernel_of_orderedCharts B hext hdepth e ψ hroot l hl

end Langlands.BruhatTits.IntegralModels.TorusRootModelFamilyData
