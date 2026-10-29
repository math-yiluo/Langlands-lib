import Langlands.Algebra.LocalFiberInjectivityStatement
import Langlands.Algebra.LocalApproximationResidueFiber
import Langlands.Algebra.LocalApproximationResidueInjectivity
import Langlands.Algebra.DirectedModuleFlatnessAscent
import Langlands.Algebra.LocalApproximationCokernel
import Langlands.Algebra.LocalApproximationMap
import Langlands.Algebra.LocalCompatibleMapApproximation
import Langlands.Algebra.NoetherianLocalFiberInjectivity
import Langlands.Algebra.LocalCompatibleMapApproximationExistence
import Langlands.Algebra.LocalApproximationFlatnessDescent
import Langlands.Algebra.LocalApproximationFlatnessPropagation
import Mathlib.RingTheory.Localization.Submodule

open scoped TensorProduct Langlands.Algebra.LocalModuleSystem
open IsLocalRing

universe uI uA uB uE uF uR uS uM uN

namespace Langlands.Algebra

/-- A compatible scalar tower identifies the given base action with canonical restriction. -/
theorem flat_compHom_of_isScalarTower
    {R : Type uR} {S : Type uS} {N : Type uN}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (h : Module.Flat R N) :
    letI : Module R N := Module.compHom N (algebraMap R S)
    Module.Flat R N := by
  have hmod : (inferInstance : Module R N) = Module.compHom N (algebraMap R S) :=
    Module.ext' _ _ fun r n ↦ (algebraMap_smul S r n).symm
  exact hmod ▸ h

namespace LocalModuleSystem

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
  {D : LocalAlgebraSystem.{uI, uA, uB} ι R S}
  {M : Type uM} {N : Type uN} [AddCommGroup M] [AddCommGroup N]
  [Module S M] [Module S N]

/-- Eventual component injectivity passes to a map of the specified colimit cocones. -/
theorem injective_of_eventually_injective
    (E : LocalModuleSystem.{uI, uA, uB, uE, uR, uS, uM} D M)
    (F : LocalModuleSystem.{uI, uA, uB, uF, uR, uS, uN} D N)
    (f : M →ₗ[S] N) (φ : CompatibleMap E F f)
    (hE : Function.Surjective E.moduleColimitMap)
    (hF : Function.Injective F.moduleColimitMap)
    (hg : ∃ i₀, ∀ j, i₀ ≤ j → Function.Injective (φ.component j)) :
    Function.Injective f := by
  classical
  have : DirectedSystem F.obj
      (fun {i j} h ↦ (F.map i j h).toAddMonoidHom) := F.directed
  obtain ⟨i₀, hg⟩ := hg
  rw [injective_iff_map_eq_zero]
  intro m
  obtain ⟨z, rfl⟩ := hE m
  induction z using AddCommGroup.DirectLimit.induction_on with
  | ih i x =>
    rw [E.moduleColimitMap_of]
    intro hx
    have hz : AddCommGroup.DirectLimit.of F.obj
        (fun i j h ↦ (F.map i j h).toAddMonoidHom) i (φ.component i x) = 0 := by
      apply hF
      rw [F.moduleColimitMap_of, map_zero, φ.ιM_comm]
      exact hx
    obtain ⟨j, hij, hj⟩ := AddCommGroup.DirectLimit.of.zero_exact i (φ.component i x) hz
    change F.map i j hij (φ.component i x) = 0 at hj
    obtain ⟨k, hjk, hi₀k⟩ := exists_ge_ge j i₀
    have hk : φ.component k (E.map i k (hij.trans hjk) x) = 0 := by
      rw [φ.map_comm, ← F.directed.map_map hij hjk, hj, map_zero]
    have hxk : E.map i k (hij.trans hjk) x = 0 :=
      hg k hi₀k (hk.trans (map_zero (φ.component k)).symm)
    rw [← E.ιM_compat i k (hij.trans hjk) x, hxk, map_zero]

variable [Module R M] [Module R N] [IsScalarTower R S M] [IsScalarTower R S N]

/-- Descent and the actual approximation transition maps give a flatness tail.
Adapted from Worker 214's fibrewise-flatness assembly. -/
theorem eventually_flat_of_descent_and_propagation
    (F : LocalModuleSystem.{uI, uA, uB, uF, uR, uS, uN} D N)
    (hRS : EssFinitePresentation R S)
    (hN : Module.FinitePresentation S N)
    (hF : F.IsApproximation)
    (hflat : Module.Flat R N) :
    ∃ i₀, ∀ j, i₀ ≤ j → Module.Flat (D.base j) (F.obj j) := by
  obtain ⟨i, hi⟩ := localApproximationFlatnessDescent
    ι R S N D F hRS hN hF (flat_compHom_of_isScalarTower hflat)
  refine ⟨i, fun j hij ↦ ?_⟩
  exact localApproximationFlatnessPropagation ι R S N D F i j hij
    (hF.2.2.2.2.1 i j hij) (hF.2.2.2.2.2 i j hij) hi

/-- Tensor base change of a component map commutes with the actual residue cocones. -/
theorem residueFiberι_lTensor
    (E : LocalModuleSystem.{uI, uA, uB, uE, uR, uS, uM} D M)
    (F : LocalModuleSystem.{uI, uA, uB, uF, uR, uS, uN} D N)
    (f : M →ₗ[S] N) (i : ι) (g : E.obj i →ₗ[D.alg i] F.obj i)
    (hcocone : ∀ x, f (E.ιM i x) = F.ιM i (g x)) (x : E.ResidueFiber i) :
    F.residueFiberι i (LinearMap.lTensor (ResidueField (D.base i))
      (g.restrictScalars (D.base i)) x) =
      LinearMap.lTensor (ResidueField R) (f.restrictScalars R) (E.residueFiberι i x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a m => simp [hcocone]
  | add x y hx hy => simp_all

/-- Injectivity of the ambient fibre map and source fibre cocone gives component injectivity. -/
theorem residue_lTensor_injective_of_cocone
    (E : LocalModuleSystem.{uI, uA, uB, uE, uR, uS, uM} D M)
    (F : LocalModuleSystem.{uI, uA, uB, uF, uR, uS, uN} D N)
    (f : M →ₗ[S] N) (i : ι) (g : E.obj i →ₗ[D.alg i] F.obj i)
    (hcocone : ∀ x, f (E.ιM i x) = F.ιM i (g x))
    (hE : Function.Injective (E.residueFiberι i))
    (hf : Function.Injective (LinearMap.lTensor (ResidueField R) (f.restrictScalars R))) :
    Function.Injective (LinearMap.lTensor (ResidueField (D.base i))
      (g.restrictScalars (D.base i))) := by
  intro x y hxy
  apply hE
  apply hf
  rw [← residueFiberι_lTensor E F f i g hcocone x,
    ← residueFiberι_lTensor E F f i g hcocone y, hxy]

omit [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] in
/-- The two actual range quotients have equivalent flatness over the base ring. -/
theorem flat_range_restrictScalars_iff (f : M →ₗ[S] N) :
    Module.Flat R (N ⧸ LinearMap.range (f.restrictScalars R)) ↔
      Module.Flat R (N ⧸ LinearMap.range f) :=
  Module.Flat.equiv_iff (Submodule.Quotient.restrictScalarsEquiv R (LinearMap.range f))

/-- The component step of 046Y using the published Noetherian lifting theorem. -/
theorem eventually_injective_and_flat_cokernel_of_noetherian_lifting
    (E : LocalModuleSystem.{uI, uA, uB, uE, uR, uS, uM} D M)
    (F : LocalModuleSystem.{uI, uA, uB, uF, uR, uS, uN} D N)
    (f : M →ₗ[S] N) (φ : CompatibleMap E F f)
    (hE : E.IsApproximation)
    (hNflat : ∃ i₀, ∀ j, i₀ ≤ j → Module.Flat (D.base j) (F.obj j))
    (hf : Function.Injective (LinearMap.lTensor (ResidueField R) (f.restrictScalars R))) :
    ∃ i₀, ∀ j, i₀ ≤ j →
      Function.Injective (φ.component j) ∧
        Module.Flat (D.base j) (F.obj j ⧸ LinearMap.range (φ.component j)) := by
  obtain ⟨iN, hN⟩ := hNflat
  obtain ⟨iE, hEres⟩ := localApproximationResidueInjectivity ι R S D M E hE
  obtain ⟨i₀, hNi₀, hEi₀⟩ := exists_ge_ge iN iE
  refine ⟨i₀, fun j hij ↦ ?_⟩
  have : _root_.Algebra.EssFiniteType ℤ (D.base j) := hE.2.1 j
  have : IsNoetherianRing (D.base j) :=
    _root_.Algebra.EssFiniteType.isNoetherianRing ℤ (D.base j)
  have : _root_.Algebra.EssFiniteType (D.base j) (D.alg j) := hE.2.2.1 j
  have : IsNoetherianRing (D.alg j) :=
    _root_.Algebra.EssFiniteType.isNoetherianRing (D.base j) (D.alg j)
  have : Module.Finite (D.alg j) (E.obj j) := hE.2.2.2.1 j
  have : IsLocalHom (algebraMap (D.base j) (D.alg j)) := D.structure_local j
  have hgj := residue_lTensor_injective_of_cocone E F f j (φ.component j)
    (fun x ↦ (φ.ιM_comm j x).symm)
    (hEres j (hEi₀.trans hij)).2 hf
  have hj := noetherianLocalFiberInjectivity (D.base j) (D.alg j) (E.obj j) (F.obj j)
    ((φ.component j).restrictScalars (D.base j)) (hN j (hNi₀.trans hij)) hgj
  exact ⟨hj.1, (flat_range_restrictScalars_iff (R := D.base j) (φ.component j)).mp hj.2⟩


/-- Conditional final assembly with the actual cokernel diagram and published flatness ascent. -/
theorem injective_and_flat_cokernel_of_noetherian_lifting
    (E : LocalModuleSystem.{uI, uA, uB, uE, uR, uS, uM} D M)
    (F : LocalModuleSystem.{uI, uA, uB, uF, uR, uS, uN} D N)
    (f : M →ₗ[S] N) (φ : CompatibleMap E F f)
    (hEF : φ.IsApproximation)
    (hNflat : ∃ i₀, ∀ j, i₀ ≤ j → Module.Flat (D.base j) (F.obj j))
    (hf : Function.Injective (LinearMap.lTensor (ResidueField R) (f.restrictScalars R))) :
    Function.Injective f ∧ Module.Flat R (N ⧸ LinearMap.range (f.restrictScalars R)) := by
  obtain ⟨i₀, hi₀⟩ := eventually_injective_and_flat_cokernel_of_noetherian_lifting
    E F f φ hEF.1 hNflat hf
  have hinj : Function.Injective f := injective_of_eventually_injective E F f φ
    hEF.1.1.2.2 hEF.2.1.2.1 ⟨i₀, fun j hij ↦ (hi₀ j hij).1⟩
  have hC : φ.cokernelSystem.IsColimit :=
    ⟨hEF.1.1.1, φ.cokernelSystem_moduleColimitMap_bijective hEF.1.1.2.2 hEF.2.1.2⟩
  have hflat : Module.Flat R (N ⧸ LinearMap.range f) :=
    flat_of_eventually_flat φ.cokernelSystem hC ⟨i₀, fun j hij ↦ (hi₀ j hij).2⟩
  exact ⟨hinj, (flat_range_restrictScalars_iff (R := R) f).mpr hflat⟩

end LocalModuleSystem

/-- Stacks Project, Lemma 10.128.4 (046Y), for four independent ambient universes. -/
theorem localFiberInjectivity :
    LocalFiberInjectivityStatement.{uR, uS, uM, uN} := by
  intro R S M N _ _ _ _ _ _ _ _ _ _ _ _ _ _ f hRS hM hN hflat hf
  obtain ⟨ι, _, _, _, D, E, F, φ, hφ⟩ :=
    localCompatibleMapApproximationExistence R S M N hRS hM hN f
  exact LocalModuleSystem.injective_and_flat_cokernel_of_noetherian_lifting
    E F f φ hφ
    (LocalModuleSystem.eventually_flat_of_descent_and_propagation F hRS hN hφ.2 hflat) hf

end Langlands.Algebra
