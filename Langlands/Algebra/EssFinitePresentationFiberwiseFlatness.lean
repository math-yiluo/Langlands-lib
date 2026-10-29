import Langlands.Algebra.EssFinitePresentationFiberwiseFlatnessStatement
import Langlands.Algebra.LocalFiberInjectivity
import Langlands.Algebra.LocalTowerResidueFiberRings
import Langlands.Algebra.LocalTowerResidueFiberSystem
import Langlands.Algebra.ResidueFiberFinitenessProof
import Langlands.Algebra.DirectedModuleFlatnessAscent
import Langlands.Algebra.RingAdditiveColimit
import Langlands.Algebra.NoetherianFiberwiseFlatness
import Langlands.Algebra.LocalApproximationFlatnessDescent
import Langlands.Algebra.LocalApproximationFlatnessPropagation
import Langlands.Algebra.EssFinitePresentationTowerCancellationProof
import Langlands.Algebra.LocalModuleTowerApproximationExistenceProof
import Langlands.Algebra.LocalTowerResidueFiberApproximationProof

/-! # Fibrewise flatness for essentially finitely presented local algebras

Stacks Project, Lemma 10.128.8, tag 00R7. Two applications of flatness descent,
the Noetherian fibrewise criterion, and varying-base colimit ascent prove the
published statement with four independent ambient universes.
-/

open scoped TensorProduct
open scoped Langlands.Algebra.LocalModuleSystem
open scoped Langlands.Algebra.LocalModuleTowerSystem
open scoped Langlands.Algebra.ResidueFiberTensor

universe uI uA uB uC uN uR uS uT uM

namespace Langlands.Algebra
namespace EssFinitePresentationFiberwiseFlatnessProof

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]

/-- A representative of a fixed nonzero target element stays nonzero at every later stage. -/
theorem eventually_nontrivial
    {D : LocalAlgebraSystem.{uI, uA, uB} ι R S}
    {M : Type uM} [AddCommGroup M] [Module S M] [Nontrivial M]
    (E : LocalModuleSystem.{uI, uA, uB, uN} D M)
    (hE : Function.Surjective E.moduleColimitMap) :
    ∃ i₀ : ι, ∀ j, i₀ ≤ j → Nontrivial (E.obj j) := by
  classical
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨z, hz⟩ := hE m
  induction z using AddCommGroup.DirectLimit.induction_on with
  | ih i x =>
    have hx : E.ιM i x = m := by
      simpa only [LocalModuleSystem.moduleColimitMap_of] using hz
    refine ⟨i, fun j hij ↦ ⟨⟨E.map i j hij x, 0, ?_⟩⟩⟩
    intro hzero
    apply hm
    rw [← hx, ← E.ιM_compat i j hij x, hzero, map_zero]

variable {T : Type uT} [CommRing T] [IsLocalRing T]
  [Algebra S T] [Algebra R T] [IsScalarTower R S T]
  [IsLocalHom (algebraMap S T)]
  {D : LocalAlgebraTowerSystem.{uI, uA, uB, uC} ι R S T}
  {M : Type uM} [AddCommGroup M] [Module T M]
  (E : LocalModuleTowerSystem.{uI, uA, uB, uC, uN} D M)

/-- The synchronized approximation supplies the ordinary composite-arrow approximation. -/
theorem rtModule_isApproximation (hE : E.IsApproximation) :
    letI := LocalAlgebraTowerSystem.composite_local R S T
    E.rtModule.IsApproximation := by
  let := LocalAlgebraTowerSystem.composite_local R S T
  obtain ⟨hD, hM, hfinite, hbc⟩ := hE
  obtain ⟨hrs, hst, hupper, hlocST, hlocRT⟩ := hD
  refine ⟨⟨⟨hrs.1.1, hst.2⟩, hM⟩, hrs.2.1, ?_, hfinite, hlocRT, hbc⟩
  intro i
  let := hrs.2.2.1 i
  let := hupper i
  exact _root_.Algebra.EssFiniteType.comp (D.rs.base i) (D.rs.alg i) (D.top i)

/-- The first 00R6 application uses the actual composite-arrow approximation. -/
theorem eventually_flat_over_base
    [Module R M] [IsScalarTower R T M]
    (hRT : EssFinitePresentation R T)
    (hM : Module.FinitePresentation T M)
    (hE : E.IsApproximation)
    (hflat : Module.Flat R M) :
    ∃ i₀, ∀ j, i₀ ≤ j → Module.Flat (D.rs.base j) (E.stModule.obj j) := by
  let := LocalAlgebraTowerSystem.composite_local R S T
  exact LocalModuleSystem.eventually_flat_of_descent_and_propagation E.rtModule
    hRT hM (rtModule_isApproximation E hE) hflat

/-- The second 00R6 application uses the actual packaged residue-fibre diagram. -/
theorem eventually_flat_over_lower_fiber
    [Module R M] [Module S M]
    [IsScalarTower R S M] [IsScalarTower R T M] [IsScalarTower S T M]
    (hST : EssFinitePresentation S T)
    (hM : Module.FinitePresentation T M)
    (hE : letI := LocalAlgebraTowerSystem.composite_local R S T
      E.fiberModuleSystem.IsApproximation)
    (hflat : Module.Flat (LocalAlgebraSystem.TargetFiberRing R S)
      (LocalModuleSystem.TargetFiberModule R S M)) :
    ∃ i₀, ∀ j, i₀ ≤ j →
      Module.Flat (D.rs.FiberRing j) (E.rsModule.ResidueFiber j) := by
  let := LocalAlgebraTowerSystem.composite_local R S T
  obtain ⟨hFG, hN⟩ := residueFiberFiniteness R S T M hST hM
  let := hflat
  have hraw : Module.Flat (LocalAlgebraSystem.TargetFiberRing R S)
      (LocalModuleSystem.TargetResidueFiber R M) :=
    Module.Flat.of_linearEquiv
      (LocalModuleTowerSystem.targetLowerFiberModuleEquiv
        (R := R) (S := S) (M := M)).symm
  obtain ⟨i₀, hi₀⟩ := LocalModuleSystem.eventually_flat_of_descent_and_propagation
    E.fiberModuleSystem hFG hN hE hraw
  refine ⟨i₀, fun j hij ↦ ?_⟩
  have hj := hi₀ j hij
  change @Module.Flat (D.rs.FiberRing j) (E.rsModule.ResidueFiber j) _ _
    (LocalModuleSystem.objBaseModule E.fiberModuleSystem j) at hj
  rw [E.fiberModuleSystem_objBaseModule j] at hj
  exact hj

/-- Stagewise conclusions ascend through the two actual varying-base colimits. -/
theorem flat_of_eventually_stagewise_flat
    [Module S M] [IsScalarTower S T M]
    (hE : E.IsColimit)
    (hflat : ∃ i₀, ∀ j, i₀ ≤ j →
      Module.Flat (D.rs.base j) (D.rs.alg j) ∧
        Module.Flat (D.rs.alg j) (E.stModule.obj j)) :
    Module.Flat R S ∧ Module.Flat S M := by
  obtain ⟨i₀, hflat⟩ := hflat
  constructor
  · apply D.rs.regularModuleSystem.flat_of_eventually_flat
      (D.rs.regularModuleSystem_isColimit hE.1.1)
    refine ⟨i₀, fun j hj ↦ ?_⟩
    let := (hflat j hj).1
    exact Module.Flat.of_linearEquiv (M := D.rs.alg j)
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun r x ↦ by
          change algebraMap (D.rs.base j) (D.rs.alg j) r *
              (show D.rs.alg j from x) = r • (show D.rs.alg j from x)
          exact (Algebra.smul_def r (show D.rs.alg j from x)).symm }
  · exact E.stModule.flat_of_eventually_flat ⟨hE.1.2, hE.2⟩
      ⟨i₀, fun j hj ↦ (hflat j hj).2⟩

/-- The Noetherian criterion applies on a common tail of the two flatness tails. -/
theorem eventually_stagewise_flat_of_criterion
    [Module S M] [IsScalarTower S T M] [Nontrivial M]
    (hE : E.IsApproximation)
    (hflatR : ∃ i₀, ∀ j, i₀ ≤ j →
      Module.Flat (D.rs.base j) (E.stModule.obj j))
    (hflatF : ∃ i₀, ∀ j, i₀ ≤ j →
      Module.Flat (D.rs.FiberRing j) (E.rsModule.ResidueFiber j)) :
    ∃ i₀, ∀ j, i₀ ≤ j →
      Module.Flat (D.rs.base j) (D.rs.alg j) ∧
        Module.Flat (D.rs.alg j) (E.stModule.obj j) := by
  obtain ⟨hD, hM, hfinite, hbc⟩ := hE
  obtain ⟨hrs, hst, hupper, hlocST, hlocRT⟩ := hD
  obtain ⟨iR, hR⟩ := hflatR
  obtain ⟨iF, hF⟩ := hflatF
  obtain ⟨iN, hN⟩ := eventually_nontrivial E.stModule hM.2
  obtain ⟨k, hiRk, hiFk⟩ := exists_ge_ge iR iF
  obtain ⟨l, hkl, hiNl⟩ := exists_ge_ge k iN
  refine ⟨l, fun j hlj ↦ ?_⟩
  let := hN j (hiNl.trans hlj)
  let := hrs.2.1 j
  let := hrs.2.2.1 j
  let := hupper j
  let := _root_.Algebra.EssFiniteType.isNoetherianRing ℤ (D.rs.base j)
  let := _root_.Algebra.EssFiniteType.isNoetherianRing (D.rs.base j) (D.rs.alg j)
  let := _root_.Algebra.EssFiniteType.isNoetherianRing (D.rs.alg j) (D.top j)
  let := D.rs.structure_local j
  let := D.upper_local j
  let := hF j (hiFk.trans (hkl.trans hlj))
  have hfiber : Module.Flat (D.rs.FiberRing j) (E.rsModule.FiberModule j) :=
    Module.Flat.of_linearEquiv (E.lowerFiberModuleEquiv j)
  exact noetherianFiberwiseFlatness
    (D.rs.base j) (D.rs.alg j) (D.top j) (E.stModule.obj j)
    (hfinite j) inferInstance hfiber (hR j (hiRk.trans (hkl.trans hlj)))

/-- A fibre flatness tail combines with ordinary descent to give both conclusions. -/
theorem flat_of_fiber_tail
    [Module R M] [Module S M]
    [IsScalarTower R T M] [IsScalarTower S T M] [Nontrivial M]
    (hRT : EssFinitePresentation R T)
    (hM : Module.FinitePresentation T M)
    (hE : E.IsApproximation)
    (hflatF : ∃ i₀, ∀ j, i₀ ≤ j →
      Module.Flat (D.rs.FiberRing j) (E.rsModule.ResidueFiber j))
    (hflatR : Module.Flat R M) :
    Module.Flat R S ∧ Module.Flat S M := by
  have hcolimit : E.IsColimit :=
    ⟨⟨hE.1.1.1, hE.1.2.1⟩, hE.2.1⟩
  apply flat_of_eventually_stagewise_flat E hcolimit
  exact eventually_stagewise_flat_of_criterion E hE
    (eventually_flat_over_base E hRT hM hE hflatR) hflatF

/-- Both descent applications and varying-base ascent, for a given actual approximation. -/
theorem flat_of_actual_fiber_approximation
    [Module R M] [Module S M]
    [IsScalarTower R S M] [IsScalarTower R T M] [IsScalarTower S T M] [Nontrivial M]
    (hRT : EssFinitePresentation R T)
    (hST : EssFinitePresentation S T)
    (hM : Module.FinitePresentation T M)
    (hE : E.IsApproximation)
    (hfiberE : letI := LocalAlgebraTowerSystem.composite_local R S T
      E.fiberModuleSystem.IsApproximation)
    (hflatF : Module.Flat (LocalAlgebraSystem.TargetFiberRing R S)
      (LocalModuleSystem.TargetFiberModule R S M))
    (hflatR : Module.Flat R M) :
    Module.Flat R S ∧ Module.Flat S M := by
  apply flat_of_fiber_tail E hRT hM hE
  · exact eventually_flat_over_lower_fiber E
      hST hM hfiberE hflatF
  · exact hflatR

end EssFinitePresentationFiberwiseFlatnessProof

/-- Stacks Project, Lemma 10.128.8 (tag 00R7): fibrewise flatness for essentially
finitely presented local algebras. -/
theorem essFinitePresentationFiberwiseFlatness :
    EssFinitePresentationFiberwiseFlatnessStatement.{uR, uS, uT, uM} := by
  intro R S T M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hRS hRT hM hnontrivial hflatF hflatR
  let : Nontrivial M := hnontrivial
  have hST := essFinitePresentationTowerCancellation R S T hRS hRT
  obtain ⟨ι, pre, inhabited, directed, D, E, hE⟩ :=
    localModuleTowerApproximationExistence R S T M hRS hRT hM
  let := pre
  let := inhabited
  let := directed
  have hfiberE := localTowerResidueFiberApproximation ι R S T M D E hE
  exact EssFinitePresentationFiberwiseFlatnessProof.flat_of_actual_fiber_approximation E
    hRT hST hM hE hfiberE hflatF hflatR

end Langlands.Algebra
