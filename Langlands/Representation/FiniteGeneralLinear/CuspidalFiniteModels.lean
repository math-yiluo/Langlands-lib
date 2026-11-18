import Langlands.Representation.Finite.VirtualCharacterProof
import Langlands.Representation.FiniteGeneralLinear.Cuspidal
import Langlands.Representation.Category.UniverseLift
import Langlands.Representation.Smooth.IsotypicProjector
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite-dimensional models for cuspidal classes

The arbitrary carrier universe in the definition of cuspidal classes can be
replaced by the finite-dimensional model used in ordinary character theory.
-/

noncomputable section

namespace Langlands.FiniteRep

/-- An irreducible complex representation of a finite group is finite dimensional. -/
theorem finiteDimensional_of_isIrreducible {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (hρ : ρ.IsIrreducible) :
    FiniteDimensional ℂ V := by
  let : Module.Finite ℂ (MonoidAlgebra ℂ G) :=
    Module.Finite.equiv
      ((Finsupp.linearEquivFunOnFinite ℂ ℂ G).symm.trans
        (MonoidAlgebra.coeffLinearEquiv ℂ).symm)
  let := moduleFinite_asModule_of_isIrreducible ρ hρ
  let : Module.Finite ℂ ρ.asModule := Module.Finite.trans (MonoidAlgebra ℂ G) ρ.asModule
  exact Module.Finite.equiv ρ.asModuleEquiv

/-- The irreducible class of a finite-dimensional representation on any carrier. -/
def irreducibleClassOfRepresentation {G V : Type*} [Group G] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (hρ : ρ.IsIrreducible) : IrreducibleClass G :=
  ⟨classOfRepresentation ρ, ofRepresentation ρ, rfl,
    (isIrreducible_iff_of_equiv (modelEquiv ρ)).mp hρ⟩

end Langlands.FiniteRep

namespace Langlands.FiniteGeneralLinear

open FiniteRep

universe u w

variable {n : ℕ} {k : Type u} [Field k]

/-- The irreducible classes whose chosen finite-dimensional representatives are cuspidal. -/
def CuspidalModelClass (n : ℕ) (k : Type u) [Field k] :=
  {a : IrreducibleClass (GeneralLinear n k) // IsCuspidal (VirtualCharacter.rep a).ρ}

namespace CuspidalModelClass

/-- A finite-dimensional irreducible cuspidal representation gives a model class. -/
def ofRepresentation {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (GeneralLinear n k) V) (hρ : ρ.IsIrreducible)
    (hc : IsCuspidal ρ) : CuspidalModelClass n k := by
  let a := irreducibleClassOfRepresentation ρ hρ
  refine ⟨a, ?_⟩
  have h : classOf (VirtualCharacter.rep a) = classOfRepresentation ρ :=
    VirtualCharacter.classOf_rep a
  obtain ⟨e⟩ := (classOf_eq_iff _ _).mp h.symm
  exact hc.of_equiv ((modelEquiv ρ).trans (FiniteRep.equivOfIso e))

theorem ofRepresentation_eq_iff {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (GeneralLinear n k) V)
    (σ : Representation ℂ (GeneralLinear n k) W)
    (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible) (hcρ : IsCuspidal ρ) (hcσ : IsCuspidal σ) :
    ofRepresentation ρ hρ hcρ = ofRepresentation σ hσ hcσ ↔ Nonempty (ρ.Equiv σ) := by
  rw [← classOfRepresentation_eq_iff]
  exact ⟨fun h => congrArg (fun a : CuspidalModelClass n k => a.1.1) h,
    fun h => Subtype.ext (Subtype.ext h)⟩

variable [Finite k]

/-- The finite-dimensional model attached to a cuspidal object in any universe. -/
def ofCuspidalRep (A : CuspidalRep.{u, w} n k) : CuspidalModelClass n k :=
  letI := finiteDimensional_of_isIrreducible A.obj.ρ A.isIrreducible
  ofRepresentation A.obj.ρ A.isIrreducible A.isCuspidal

theorem ofCuspidalRep_eq_iff (A B : CuspidalRep.{u, w} n k) :
    ofCuspidalRep A = ofCuspidalRep B ↔ A.isoClass = B.isoClass := by
  let := finiteDimensional_of_isIrreducible A.obj.ρ A.isIrreducible
  let := finiteDimensional_of_isIrreducible B.obj.ρ B.isIrreducible
  rw [CuspidalRep.isoClass_eq_iff]
  exact ofRepresentation_eq_iff _ _ _ _ _ _

/-- Compare the arbitrary-universe quotient with the ordinary finite-dimensional classes. -/
def equivCuspidalClass : CuspidalClass.{u, w} n k ≃ CuspidalModelClass n k := by
  let f : CuspidalClass.{u, w} n k → CuspidalModelClass n k :=
    Quotient.lift ofCuspidalRep fun A B h =>
      (ofCuspidalRep_eq_iff A B).mpr (Quotient.sound h)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro ⟨A⟩ ⟨B⟩ h
    exact (ofCuspidalRep_eq_iff A B).mp h
  · intro a
    let V := VirtualCharacter.rep a.1
    let e := universeLiftEquiv.{w} V.ρ
    let A : CuspidalRep.{u, w} n k := CuspidalRep.of
      (universeLiftRepresentation.{w} V.ρ)
      ((isIrreducible_iff_of_equiv e).mp (VirtualCharacter.isIrreducible_rep a.1))
      (a.2.of_equiv e)
    refine ⟨A.isoClass, Subtype.ext (Subtype.ext ?_)⟩
    let := finiteDimensional_of_isIrreducible A.obj.ρ A.isIrreducible
    change classOfRepresentation A.obj.ρ = a.1.1
    exact (classOfRepresentation_congr e.symm).trans
      ((classOfRepresentation_rho V).trans (VirtualCharacter.classOf_rep a.1))

end CuspidalModelClass

end Langlands.FiniteGeneralLinear
