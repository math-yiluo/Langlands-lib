import Langlands.AlgebraicGeometry.GroupoidCoactionExact
import Langlands.AlgebraicGeometry.GroupoidCoactionInvariants
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Cokernel coactions and surjectivity of invariant maps -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}
variable {M N : Type v} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]

/-- The semilinear map on the cokernel of an equivariant map. -/
def cokernelSemilinearMap (θM : GroupoidCoaction t M) (θN : GroupoidCoaction t N)
    (f : M →ₗ[B] N) (hf : θM.IsHom θN f) :
    N ⧸ LinearMap.range f →ₛₗ[t] C ⊗[B] (N ⧸ LinearMap.range f) :=
  (LinearMap.range f).liftQ
    ((AlgebraTensorModule.lTensor C C (LinearMap.range f).mkQ).comp θN.semilinearMap)
    (by
      rintro _ ⟨m, rfl⟩
      change LinearMap.lTensor C (LinearMap.range f).mkQ (θN.coaction (f m)) = 0
      rw [hf m, ← LinearMap.lTensor_comp_apply]
      have hq : (LinearMap.range f).mkQ.comp f = 0 := by
        ext m
        exact (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self f m)
      rw [hq]
      simp)

@[simp]
lemma cokernelSemilinearMap_mkQ (θM : GroupoidCoaction t M) (θN : GroupoidCoaction t N)
    (f : M →ₗ[B] N) (hf : θM.IsHom θN f) (n : N) :
    cokernelSemilinearMap θM θN f hf ((LinearMap.range f).mkQ n) =
      LinearMap.lTensor C (LinearMap.range f).mkQ (θN.coaction n) :=
  rfl

/-- The quotient coaction on the cokernel of an equivariant map. -/
def cokernel (θM : GroupoidCoaction t M) (θN : GroupoidCoaction t N)
    (f : M →ₗ[B] N) (hf : θM.IsHom θN f) :
    GroupoidCoaction t (N ⧸ LinearMap.range f) :=
  ofSurjective θN (LinearMap.range f).mkQ (LinearMap.range f).mkQ_surjective
    (cokernelSemilinearMap θM θN f hf).toAddMonoidHom
    (fun b n => (cokernelSemilinearMap θM θN f hf).map_smulₛₗ b n)
    (cokernelSemilinearMap_mkQ θM θN f hf)

lemma cokernel_mkQ_isHom (θM : GroupoidCoaction t M) (θN : GroupoidCoaction t N)
    (f : M →ₗ[B] N) (hf : θM.IsHom θN f) :
    θN.IsHom (cokernel θM θN f hf) (LinearMap.range f).mkQ :=
  cokernelSemilinearMap_mkQ θM θN f hf

/-- Acyclicity of all coactions implies that every equivariant surjection is
surjective on invariants. All modules here have the same universe. -/
lemma invariantsMap_surjective
    (hE : RingEtaleEquivalenceRelation t)
    (hacyclic : ∀ (K : Type v) [AddCommGroup K] [Module B K]
      (θK : GroupoidCoaction t K), θK.IsAcyclic)
    (θM : GroupoidCoaction t M) (θN : GroupoidCoaction t N)
    (f : M →ₗ[B] N) (hf : θM.IsHom θN f) (hsurj : Function.Surjective f) :
    Function.Surjective (θM.invariantsMap θN f hf) := by
  let θK := kernel hE θM θN f hf
  exact invariantsMap_surjective_of_isAcyclic θK θM θN
    (LinearMap.ker f).subtype f (kernel_subtype_isHom hE θM θN f hf) hf
    (LinearMap.ker f).subtype_injective hsurj
    (Submodule.range_subtype (LinearMap.ker f)) (hacyclic _ θK)

end Langlands.AlgebraicGeometry.GroupoidCoaction
