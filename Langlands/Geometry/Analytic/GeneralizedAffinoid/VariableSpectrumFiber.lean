import Langlands.Geometry.Analytic.GeneralizedAffinoid.VariableActionFiber
import Langlands.Geometry.Analytic.GeneralizedAffinoid.VariableSpectrumFibered
import Langlands.Topology.GroupAction.VariableContinuousActionFiber
import Mathlib.CategoryTheory.Whiskering

/-! # Actual quotient spectra on the operator-group fibers -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.VariableActionSpace

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

/-- Apply the actual spectrum construction inside each standard group fiber. -/
def spectrumFiberFunctor (G : Langlands.Topology.TopologicalGroup.{v}) :
    Functor.Fiber (groupForget (K := K)) G ⥤
      Functor.Fiber Langlands.Topology.VariableContinuousAction.groupForget G :=
  Functor.Fiber.inducedFunctor
    (show ((Functor.Fiber.fiberInclusion :
        Functor.Fiber (groupForget (K := K)) G ⥤ _) ⋙ spectrumFunctor) ⋙
          Langlands.Topology.VariableContinuousAction.groupForget =
        (Functor.const (Functor.Fiber (groupForget (K := K)) G)).obj G by
      rw [Functor.assoc, spectrumFunctor_comp_groupForget,
        Functor.Fiber.fiberInclusion_comp_eq_const])

@[simp]
theorem spectrumFiberFunctor_comp_inclusion (G : Langlands.Topology.TopologicalGroup.{v}) :
    spectrumFiberFunctor (K := K) G ⋙ Functor.Fiber.fiberInclusion =
      Functor.Fiber.fiberInclusion ⋙ spectrumFunctor := rfl

@[simp]
theorem spectrumFiberFunctor_obj_val (G : Langlands.Topology.TopologicalGroup.{v})
    (X : Functor.Fiber (groupForget (K := K)) G) :
    ((spectrumFiberFunctor G).obj X).val = spectrumFunctor.obj X.val := rfl

@[simp]
theorem spectrumFiberFunctor_map_val (G : Langlands.Topology.TopologicalGroup.{v})
    {X Y : Functor.Fiber (groupForget (K := K)) G} (f : X ⟶ Y) :
    ((spectrumFiberFunctor G).map f).val = spectrumFunctor.map f.val := rfl

/-- The fixed-group fiber equivalences identify the spectrum functors strictly. -/
theorem ofFixedToFiber_comp_spectrumFiberFunctor
    (G : Langlands.Topology.TopologicalGroup.{v}) :
    ofFixedToFiber (K := K) G ⋙ spectrumFiberFunctor G =
      NormContinuousAction.spectrumFunctor ⋙
        Langlands.Topology.VariableContinuousAction.ofFixedToFiber G := rfl

/-- On every fiber arrow the continuous map is the original seminorm pullback. -/
@[simp]
theorem spectrumFiberFunctor_map_apply (G : Langlands.Topology.TopologicalGroup.{v})
    {X Y : Functor.Fiber (groupForget (K := K)) G} (f : X ⟶ Y)
    (x : BanachSpectrum X.val.algebraAction.obj.V)
    (a : Y.val.algebraAction.obj.V) :
    BanachSpectrum.toMulRingSeminorm
        (((spectrumFiberFunctor G).map f).val.spaceMap x) a =
      x (f.val.algebraMap a) := rfl

/-- Recovering a fixed-group arrow from either fiber commutes with spectra. -/
theorem spectrumFunctor_ofFixedFiberPreimage
    (G : Langlands.Topology.TopologicalGroup.{v})
    {X Y : NormContinuousSpace K G}
    (f : (ofFixedToFiber G).obj X ⟶ (ofFixedToFiber G).obj Y) :
    NormContinuousAction.spectrumFunctor.map (ofFixedFiberPreimage G f) =
      Langlands.Topology.VariableContinuousAction.ofFixedFiberPreimage G
        ((spectrumFiberFunctor G).map f) := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  rfl

/-- The direct functor on standard fibers agrees with transport of the existing
fixed-group spectrum functor through the constructed equivalences. -/
def spectrumFiberComparison (G : Langlands.Topology.TopologicalGroup.{v}) :
    spectrumFiberFunctor (K := K) G ≅
      (fixedGroupFiberEquivalence (K := K) G).inverse ⋙
        NormContinuousAction.spectrumFunctor ⋙
          (Langlands.Topology.VariableContinuousAction.fixedGroupFiberEquivalence G).functor :=
  (Functor.leftUnitor (spectrumFiberFunctor G)).symm ≪≫
    Functor.isoWhiskerRight (fixedGroupFiberEquivalence (K := K) G).counitIso.symm
      (spectrumFiberFunctor G)

end Langlands.Analytic.PresentedAffinoidAlgebra.VariableActionSpace
