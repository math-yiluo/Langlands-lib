import Langlands.CommutativeAlgebra.FiniteTensorIdealModel
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-! # Faithfully flat contraction and finite coefficient models of prime tensor ideals -/

noncomputable section

universe u v w z

open TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace Langlands.CommutativeAlgebra.TensorIdealDescent

open DVRAlgebraicBaseChange (stageMap)

variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]
variable (A : Type w) [CommRing A] [Algebra K A]

/-- Extension along any intermediate field induces a faithfully flat tensor map. -/
theorem stageMap_faithfullyFlat (E : IntermediateField K L) :
    RingHom.FaithfullyFlat (R := E ⊗[K] A) (S := L ⊗[K] A)
      (stageMap K L A E).toRingHom := by
  let : Algebra K E := E.algebra'
  let : CommRing (E ⊗[K] A) := inferInstance
  let : Algebra (E ⊗[K] A) (L ⊗[K] A) := (stageMap K L A E).toRingHom.toAlgebra
  change Module.FaithfullyFlat (E ⊗[K] A) (L ⊗[K] A)
  let e : (E ⊗[K] A) ⊗[E] L ≃ₐ[E] L ⊗[K] A :=
    (Algebra.TensorProduct.comm E (E ⊗[K] A) L).trans
      (Algebra.TensorProduct.cancelBaseChange K E E L A)
  have he (x : E ⊗[K] A) : e (x ⊗ₜ[E] (1 : L)) = stageMap K L A E x := by
    induction x with
    | tmul a b => simp [e, DVRAlgebraicBaseChange.stageMap, Algebra.smul_def]
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  let e' : (E ⊗[K] A) ⊗[E] L ≃ₐ[E ⊗[K] A] L ⊗[K] A :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun x => he x)
  exact Module.FaithfullyFlat.of_linearEquiv (E ⊗[K] A) ((E ⊗[K] A) ⊗[E] L)
    e'.symm.toLinearEquiv

/-- Every ideal is the contraction of its extension along an intermediate-field tensor map. -/
theorem stageMap_comap_map (E : IntermediateField K L) (J : Ideal (E ⊗[K] A)) :
    (J.map (stageMap K L A E).toRingHom).comap (stageMap K L A E).toRingHom = J := by
  let : Algebra K E := E.algebra'
  let : CommRing (E ⊗[K] A) := inferInstance
  let : Algebra (E ⊗[K] A) (L ⊗[K] A) := (stageMap K L A E).toRingHom.toAlgebra
  have : Module.FaithfullyFlat (E ⊗[K] A) (L ⊗[K] A) := stageMap_faithfullyFlat K L A E
  exact Ideal.comap_map_eq_self_of_faithfullyFlat (A := E ⊗[K] A) (B := L ⊗[K] A) J

namespace FiniteTensorIdealModel

variable {K L A} {ι : Type z} {I : ι → Ideal (L ⊗[K] A)}

/-- The ideals in every finite coefficient model are exactly the contractions of the originals. -/
theorem ideal_eq_comap (M : FiniteTensorIdealModel K L A I) (i : ι) :
    M.ideal i = (I i).comap (stageMap K L A M.fieldStage).toRingHom := by
  rw [← M.map_eq i, stageMap_comap_map]

/-- A model ideal of a prime ideal remains prime. -/
theorem isPrime (M : FiniteTensorIdealModel K L A I) (i : ι) [(I i).IsPrime] :
    (M.ideal i).IsPrime := by
  rw [M.ideal_eq_comap i]
  infer_instance

end FiniteTensorIdealModel

/-- A common finite coefficient model of prime ideals, including the exact contraction identities. -/
structure FiniteTensorPrimeModel {ι : Type z} (I : ι → Ideal (L ⊗[K] A))
    extends FiniteTensorIdealModel K L A I where
  prime : ∀ i, (ideal i).IsPrime
  comap_eq : ∀ i, ideal i = (I i).comap (stageMap K L A fieldStage).toRingHom

namespace FiniteTensorPrimeModel

variable {K L A} {ι : Type z} [Finite ι] [Algebra.IsAlgebraic K L]
variable (I : ι → Ideal (L ⊗[K] A)) (hfg : ∀ i, (I i).FG) (hprime : ∀ i, (I i).IsPrime)

/-- Choose one finite intermediate field defining finitely many finitely generated prime ideals. -/
def construct : FiniteTensorPrimeModel K L A I :=
  let M := FiniteTensorIdealModel.construct I hfg
  { M with
    prime := fun i => @FiniteTensorIdealModel.isPrime K _ L _ _ A _ _ ι I M i (hprime i)
    comap_eq := M.ideal_eq_comap }

end FiniteTensorPrimeModel

end Langlands.CommutativeAlgebra.TensorIdealDescent
