import Langlands.Algebra.LocalFiberRankOne
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Reflection of rank one along a fibrewise flat local map -/

noncomputable section

universe uR uA uB uM

open scoped TensorProduct

namespace Langlands.Algebra.LocalFiberRankOne

variable (R : Type uR) (A : Type uA) (B : Type uB) (M : Type uM)
  [CommRing R] [CommRing A] [CommRing B]
  [IsLocalRing R] [IsLocalRing A] [IsLocalRing B]
  [Algebra R A] [Algebra A B]
  [IsLocalHom (algebraMap R A)] [IsLocalHom (algebraMap A B)]
  [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
  [Module.FinitePresentation A M] [Module.Flat R M]

omit [IsLocalRing A] in
/-- The residue base change of a local ring map is local, expressed as an
iterated tensor product over the middle local ring. -/
lemma isLocalRing_iteratedResidueTensor :
    IsLocalRing ((A ⊗[R] IsLocalRing.ResidueField R) ⊗[A] B) := by
  let : Algebra R B := ((algebraMap A B).comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A B := .of_algebraMap_eq' rfl
  have : IsLocalHom (algebraMap R B) := RingHom.isLocalHom_comp _ _
  let e :=
    (Algebra.TensorProduct.comm A (A ⊗[R] IsLocalRing.ResidueField R) B).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange R A B B
        (IsLocalRing.ResidueField R)).toRingEquiv
  exact e.symm.isLocalRing

attribute [local instance] isLocalRing_iteratedResidueTensor

omit [IsLocalRing A] in
/-- The actual inclusion of the original residue fibre into the iterated
residue base change is a local homomorphism. -/
lemma isLocalHom_iteratedResidueTensor :
    IsLocalHom (algebraMap (A ⊗[R] IsLocalRing.ResidueField R)
      ((A ⊗[R] IsLocalRing.ResidueField R) ⊗[A] B)) := by
  let F := A ⊗[R] IsLocalRing.ResidueField R
  let C := F ⊗[A] B
  have : IsLocalRing C := isLocalRing_iteratedResidueTensor R A B
  let i : B →+* C := (Algebra.TensorProduct.includeRight (R := A) (A := F)).toRingHom
  have hi : Function.Surjective i :=
    Algebra.TensorProduct.includeRight_surjective B
      (ResidueFiberTensor.includeLeft_surjective R A)
  have : IsLocalHom i := IsLocalHom.of_surjective i hi
  have : IsLocalHom (i.comp (algebraMap A B)) := RingHom.isLocalHom_comp _ _
  exact ResidueFiberTensor.isLocalHom_of_tmul_one _
    (i.comp (algebraMap A B)) (fun a => by
      change (algebraMap A F a) ⊗ₜ[A] (1 : B) =
        (1 : F) ⊗ₜ[A] algebraMap A B a
      simpa only [Algebra.smul_def, mul_one]
        using TensorProduct.smul_tmul a (1 : F) (1 : B))

/-- A finitely presented, base-flat module over an essentially finitely
presented local algebra is rank one if its extension to a second local ring
is rank one and the induced map on the original residue fibre is flat. -/
def linearEquivOfFiberwiseFlatBaseChange
    (hRA : EssFinitePresentation R A)
    [Module.Flat (A ⊗[R] IsLocalRing.ResidueField R)
      ((A ⊗[R] IsLocalRing.ResidueField R) ⊗[A] B)]
    (e : (B ⊗[A] M) ≃ₗ[B] B) : M ≃ₗ[A] A := by
  let F := A ⊗[R] IsLocalRing.ResidueField R
  let C := F ⊗[A] B
  have : IsLocalRing C := isLocalRing_iteratedResidueTensor R A B
  have : IsLocalHom (algebraMap F C) := isLocalHom_iteratedResidueTensor R A B
  let : Algebra B C := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower A B C := inferInstance
  let eC : (C ⊗[A] M) ≃ₗ[C] C :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C M).symm ≪≫ₗ
      LinearEquiv.baseChange B C _ _ e ≪≫ₗ TensorProduct.AlgebraTensorModule.rid B C C
  exact linearEquivOfResidueFiberBaseChange R A M C hRA
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A F C C M ≪≫ₗ eC)

end Langlands.Algebra.LocalFiberRankOne
