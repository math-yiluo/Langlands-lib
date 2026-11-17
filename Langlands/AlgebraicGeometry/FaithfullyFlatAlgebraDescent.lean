import Langlands.AlgebraicGeometry.FaithfullyFlatCoalgebraDescent
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Smooth.Flat

/-! # Faithfully flat descent of a commutative algebra coaction -/

noncomputable section

universe u

open CategoryTheory ModuleCat TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

namespace Langlands.AlgebraicGeometry.FaithfullyFlatAlgebraDescent

open FaithfullyFlatCoalgebraDescent

variable {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
  (φ : R →+* B) (F : B →+* C)

/-- A multiplicative coaction with the counit and coassociativity laws of
 the extension/restriction-of-scalars comonad. -/
structure Coaction where
  map :
    letI := φ.toAlgebra
    letI := F.toAlgebra
    letI := (F.comp φ).toAlgebra
    C →ₐ[B] B ⊗[R] C
  counit :
    letI := φ.toAlgebra
    letI := F.toAlgebra
    letI := (F.comp φ).toAlgebra
    ModuleCat.ofHom map.toLinearMap ≫
      (descentComonad φ).ε.app (ModuleCat.of B C) = 𝟙 _
  coassoc :
    letI := φ.toAlgebra
    letI := F.toAlgebra
    letI := (F.comp φ).toAlgebra
    ModuleCat.ofHom map.toLinearMap ≫
      (descentComonad φ).δ.app (ModuleCat.of B C) =
    ModuleCat.ofHom map.toLinearMap ≫
      (descentComonad φ).map (ModuleCat.ofHom map.toLinearMap)

namespace Coaction

variable {φ F} (a : Coaction φ F)

/-- Forget multiplication to obtain a module descent coalgebra. -/
def coalgebra : (descentComonad φ).Coalgebra :=
  letI := F.toAlgebra
  { A := ModuleCat.of B C
    a := ModuleCat.ofHom a.map.toLinearMap
    counit := a.counit
    coassoc := a.coassoc }

/-- The invariant subalgebra consists of the elements with coaction `1 ⊗ c`. -/
def invariants :
    letI := (F.comp φ).toAlgebra
    Subalgebra R C := by
  letI := φ.toAlgebra
  letI := F.toAlgebra
  letI := (F.comp φ).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact a.map.restrictScalars R |>.equalizer Algebra.TensorProduct.includeRight

@[simp]
theorem mem_invariants (c : C) :
    letI := φ.toAlgebra
    letI := F.toAlgebra
    letI := (F.comp φ).toAlgebra
    c ∈ a.invariants ↔ a.map c = (1 : B) ⊗ₜ[R] c := Iff.rfl

/-- The invariant algebra and the coinvariant module have the same elements. -/
def invariantsLinearEquiv :
    letI := (F.comp φ).toAlgebra
    a.invariants ≃ₗ[R] coinvariants φ a.coalgebra := by
  letI := (F.comp φ).toAlgebra
  exact
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The scalar-extension map sends `b ⊗ c` to `F b * c`. -/
def descentHom :
    letI := φ.toAlgebra
    letI := F.toAlgebra
    letI := (F.comp φ).toAlgebra
    B ⊗[R] a.invariants →ₐ[B] C := by
  letI := φ.toAlgebra
  letI := F.toAlgebra
  letI := (F.comp φ).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact AlgHom.liftEquiv R B a.invariants C a.invariants.val

@[simp]
theorem descentHom_tmul (b : B) (c : a.invariants) :
    letI := φ.toAlgebra
    letI := F.toAlgebra
    letI := (F.comp φ).toAlgebra
    a.descentHom (b ⊗ₜ[R] c) = F b * (c : C) := rfl

/-- The algebra descent map is bijective by effective module descent. -/
theorem bijective_descentHom (hφ : φ.FaithfullyFlat) :
    Function.Bijective a.descentHom := by
  letI := φ.toAlgebra
  letI := F.toAlgebra
  letI := (F.comp φ).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let e : B ⊗[R] a.invariants ≃ₗ[B] C :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
      a.invariantsLinearEquiv).trans
      (LinearEquiv.ofBijective (descentMap φ a.coalgebra).hom
        (bijective_descentMap φ hφ a.coalgebra))
  have he : e.toLinearMap = a.descentHom.toLinearMap := by
    exact TensorProduct.AlgebraTensorModule.ext (fun _ _ => rfl)
  change Function.Bijective a.descentHom.toLinearMap
  rw [← he]
  exact e.bijective

/-- A commutative algebra coaction is recovered from its invariant subalgebra
 after a faithfully flat scalar extension. -/
def descentEquiv (hφ : φ.FaithfullyFlat) :
    letI := φ.toAlgebra
    letI := F.toAlgebra
    letI := (F.comp φ).toAlgebra
    B ⊗[R] a.invariants ≃ₐ[B] C := by
  letI := φ.toAlgebra
  letI := F.toAlgebra
  letI := (F.comp φ).toAlgebra
  exact AlgEquiv.ofBijective a.descentHom (a.bijective_descentHom hφ)

@[simp]
theorem descentEquiv_tmul (hφ : φ.FaithfullyFlat) (b : B) (c : a.invariants) :
    letI := φ.toAlgebra
    letI := F.toAlgebra
    letI := (F.comp φ).toAlgebra
    a.descentEquiv hφ (b ⊗ₜ[R] c) = F b * (c : C) := rfl

/-- Module finiteness of the supplied algebra descends to the invariants. -/
theorem finite_invariants (hφ : φ.FaithfullyFlat) (hF : F.Finite) :
    letI := (F.comp φ).toAlgebra
    Module.Finite R a.invariants := by
  letI := φ.toAlgebra
  letI := F.toAlgebra
  letI := (F.comp φ).toAlgebra
  haveI : Module.FaithfullyFlat R B := hφ
  haveI : Module.Finite B C := hF
  haveI : Module.Finite B (B ⊗[R] a.invariants) :=
    Module.Finite.equiv (a.descentEquiv hφ).symm.toLinearEquiv
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B

/-- Étaleness of the supplied algebra descends to the invariants. -/
theorem etale_invariants (hφ : φ.FaithfullyFlat) (hF : F.Etale) :
    letI := (F.comp φ).toAlgebra
    Algebra.Etale R a.invariants := by
  letI := φ.toAlgebra
  letI := F.toAlgebra
  letI := (F.comp φ).toAlgebra
  haveI : Module.FaithfullyFlat R B := hφ
  haveI : Algebra.Etale B C := hF
  haveI : Algebra.Etale B (B ⊗[R] a.invariants) :=
    Algebra.Etale.of_equiv (a.descentEquiv hφ).symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat B

/-- The invariants of a finite étale algebra are projective over the base. -/
theorem projective_invariants (hφ : φ.FaithfullyFlat) (hfin : F.Finite)
    (het : F.Etale) :
    letI := (F.comp φ).toAlgebra
    Module.Projective R a.invariants := by
  letI := (F.comp φ).toAlgebra
  haveI := a.finite_invariants hφ hfin
  haveI := a.etale_invariants hφ het
  haveI : Module.FinitePresentation R a.invariants :=
    Module.FinitePresentation.of_finite_of_finitePresentation R a.invariants
  exact Module.Flat.projective_of_finitePresentation

end Coaction

end Langlands.AlgebraicGeometry.FaithfullyFlatAlgebraDescent
