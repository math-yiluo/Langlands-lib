import Langlands.Algebra.RingAdditiveColimitStatement
import Langlands.Algebra.LocalApproximationSystem
import Mathlib.LinearAlgebra.TensorProduct.Tower

universe uI uA uR

namespace Langlands.Algebra

theorem ringAdditiveColimit :
    RingAdditiveColimitStatement.{uI, uA, uR} := by
  intro ι instPre instNe instDir A instA R instR f instF g hg
  classical
  intro h
  let L := AddCommGroup.DirectLimit.lift A (fun i j h ↦ (f i j h).toAddMonoidHom)
    R (fun i ↦ (g i).toAddMonoidHom) hg
  change Function.Bijective L
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    induction z using AddCommGroup.DirectLimit.induction_on with
    | ih i a =>
      have hga : g i a = 0 := by
        dsimp only [L] at hz
        rw [AddCommGroup.DirectLimit.lift_of] at hz
        exact hz
      have hzero : Ring.DirectLimit.of A (fun i j h ↦ f i j h) i a = 0 := by
        apply h.1
        simpa only [Ring.DirectLimit.lift_of, map_zero] using hga
      obtain ⟨j, hij, haj⟩ := Ring.DirectLimit.of.zero_exact hzero
      rw [← AddCommGroup.DirectLimit.of_f hij a]
      change AddCommGroup.DirectLimit.of A
        (fun i j h ↦ (f i j h).toAddMonoidHom) j (f i j hij a) = 0
      rw [haj, map_zero]
  · intro r
    obtain ⟨z, hz⟩ := h.2 r
    obtain ⟨i, a, rfl⟩ := Ring.DirectLimit.exists_of z
    refine ⟨AddCommGroup.DirectLimit.of A
      (fun i j h ↦ (f i j h).toAddMonoidHom) i a, ?_⟩
    dsimp only [L]
    rw [AddCommGroup.DirectLimit.lift_of]
    rw [Ring.DirectLimit.lift_of] at hz
    exact hz

universe uB uS

namespace LocalAlgebraSystem

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
  (D : LocalAlgebraSystem.{uI, uA, uB} ι R S)

/-- The algebra rings of a local algebra system, regarded as modules over themselves. -/
def regularModuleSystem : LocalModuleSystem D S where
  obj := D.alg
  map i j h :=
    { (D.algMap i j h).toAddMonoidHom with
      map_smul' := fun s t ↦ (D.algMap i j h).map_mul s t }
  directed := D.alg_directed
  ιM i :=
    { (D.algι i).toAddMonoidHom with
      map_smul' := fun s t ↦ (D.algι i).map_mul s t }
  ιM_compat := D.algι_compat

/-- The regular-module additive comparison is the lift of the original ring cocone. -/
theorem regularModuleSystem_moduleColimitMap :
    D.regularModuleSystem.moduleColimitMap =
      @AddCommGroup.DirectLimit.lift ι _ D.alg _
        (fun i j h ↦ (D.algMap i j h).toAddMonoidHom) (Classical.decEq ι)
        S _ (fun i ↦ (D.algι i).toAddMonoidHom) D.algι_compat := rfl

/-- A ring colimit cocone supplies the additive colimit for its regular modules. -/
theorem regularModuleSystem_isColimit (hD : D.IsColimit) :
    D.regularModuleSystem.IsColimit := by
  refine ⟨hD, ?_⟩
  exact ringAdditiveColimit ι D.alg S D.algMap D.algι D.algι_compat hD.2

/-- The regular-module tensor transition is the canonical tensor-unit equivalence. -/
theorem regularModuleSystem_moduleBaseChangeMap {i j : ι} (h : i ≤ j) :
    letI := (D.algMap i j h).toAlgebra
    D.regularModuleSystem.moduleBaseChangeMap h =
      (TensorProduct.AlgebraTensorModule.rid (D.alg i) (D.alg j) (D.alg j)).toLinearMap := by
  let := (D.algMap i j h).toAlgebra
  dsimp only [regularModuleSystem]
  apply TensorProduct.AlgebraTensorModule.ext
  intro s t
  change s * D.algMap i j h t = D.algMap i j h t * s
  exact mul_comm _ _

/-- Every tensor transition of the regular modules is bijective. -/
theorem regularModuleSystem_moduleBaseChangeMap_bijective {i j : ι} (h : i ≤ j) :
    Function.Bijective (D.regularModuleSystem.moduleBaseChangeMap h) := by
  let := (D.algMap i j h).toAlgebra
  rw [D.regularModuleSystem_moduleBaseChangeMap h]
  exact (TensorProduct.AlgebraTensorModule.rid (D.alg i) (D.alg j) (D.alg j)).bijective

/-- Ring approximation gives module approximation for the regular modules. -/
theorem regularModuleSystem_isApproximation (hD : D.IsApproximation) :
    D.regularModuleSystem.IsApproximation :=
  ⟨D.regularModuleSystem_isColimit hD.1, hD.2.1, hD.2.2.1,
    fun i ↦ by change Module.Finite (D.alg i) (D.alg i); infer_instance, hD.2.2.2,
    fun _ _ h ↦ D.regularModuleSystem_moduleBaseChangeMap_bijective h⟩

end LocalAlgebraSystem

end Langlands.Algebra
