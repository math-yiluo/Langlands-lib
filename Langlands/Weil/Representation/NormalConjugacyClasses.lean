import Langlands.Weil.Representation.Restriction
import Langlands.Weil.Representation.Predicates
import Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Conjugation on irreducible classes with open kernel
-/

noncomputable section

namespace Langlands.FiniteRepresentation

universe uG uV

variable (H : Type uG) [Group H] [TopologicalSpace H]

/-- An irreducible complex representation with open kernel in the supplied group. -/
def OpenKernelIrreducibleProperty (A : FiniteRepresentation.{0, uG, uV} ℂ H) : Prop :=
  A.IsIrreducible ∧ IsOpen (A.representation.ker : Set H)

/-- The actual isomorphism classes of the open-kernel irreducible objects. -/
abbrev OpenKernelIrreducibleClasses :=
  IsomorphismClassesWith (OpenKernelIrreducibleProperty.{uG, uV} H)

/-- The dimension on the class quotient, retaining the independent carrier universe. -/
def openKernelIrreducibleRank (c : OpenKernelIrreducibleClasses.{uG, uV} H) : ℕ :=
  classRank (forgetPropertyClass (OpenKernelIrreducibleProperty H) c)

section Normal

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (N : Subgroup G) [N.Normal]

/-- Pull an object on `N` back by conjugation by `g⁻¹`, so that the action is a
left action of `G` on the resulting classes. -/
def conjugateOpenKernelIrreducible (g : G)
    (A : {A // OpenKernelIrreducibleProperty.{uG, uV} N A}) :
    {B // OpenKernelIrreducibleProperty.{uG, uV} N B} := by
  let α : MulAut N := MulAut.conjNormal g⁻¹
  let B := restrict α.toMonoidHom A.1
  refine ⟨B, ?_, ?_⟩
  · let : A.1.IsIrreducible := A.2.1
    exact Langlands.CuspidalSupport.isIrreducible_comp_of_surjective A.1.representation
      α.toMonoidHom α.surjective
  · have hα : Continuous α := by
      refine Continuous.subtype_mk ?_ _
      change Continuous (fun n : N => g⁻¹ * (n : G) * (g⁻¹)⁻¹)
      fun_prop
    change IsOpen (α ⁻¹' (A.1.representation.ker : Set N))
    exact A.2.2.preimage hα

/-- Conjugation preserves actual linear intertwiners, so it descends. -/
def conjugateOpenKernelClass (g : G) :
    OpenKernelIrreducibleClasses.{uG, uV} N → OpenKernelIrreducibleClasses.{uG, uV} N :=
  Quotient.map (conjugateOpenKernelIrreducible N g) fun _ _ ⟨e⟩ =>
    ⟨restrictEquiv (MulAut.conjNormal (H := N) g⁻¹).toMonoidHom e⟩

instance normalConjugationMulAction : MulAction G (OpenKernelIrreducibleClasses.{uG, uV} N) where
  smul := conjugateOpenKernelClass N
  one_smul c := Quotient.inductionOn c fun A => by
    apply Quotient.sound
    change IsIsomorphic (restrict (MulAut.conjNormal (H := N) (1 : G)⁻¹).toMonoidHom A.1) A.1
    refine ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ A.1) fun n => ?_⟩
    ext v
    change A.1.representation (MulAut.conjNormal (H := N) (1 : G)⁻¹ n) v = A.1.representation n v
    rw [inv_one, map_one]
    rfl
  mul_smul g h c := Quotient.inductionOn c fun A => by
    apply Quotient.sound
    change IsIsomorphic (restrict (MulAut.conjNormal (H := N) (g * h)⁻¹).toMonoidHom A.1)
      (restrict (MulAut.conjNormal (H := N) g⁻¹).toMonoidHom
        (restrict (MulAut.conjNormal (H := N) h⁻¹).toMonoidHom A.1))
    refine ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ A.1) fun n => ?_⟩
    ext v
    change A.1.representation (MulAut.conjNormal (H := N) (g * h)⁻¹ n) v =
      A.1.representation (MulAut.conjNormal h⁻¹ (MulAut.conjNormal g⁻¹ n)) v
    rw [mul_inv_rev, map_mul]
    rfl

/-- Group conjugation leaves the underlying vector space unchanged. -/
@[simp] theorem openKernelIrreducibleRank_smul (g : G)
    (c : OpenKernelIrreducibleClasses.{uG, uV} N) :
    openKernelIrreducibleRank N (g • c) = openKernelIrreducibleRank N c :=
  Quotient.inductionOn c fun _ => rfl

/-- The inner action of the subgroup on its own isomorphism classes is trivial. -/
@[simp] theorem openKernelClass_inner_smul (n : N)
    (c : OpenKernelIrreducibleClasses.{uG, uV} N) : (n : G) • c = c :=
  Quotient.inductionOn c fun A => by
    apply Quotient.sound
    change IsIsomorphic (restrict (MulAut.conjNormal (H := N) (n : G)⁻¹).toMonoidHom A.1) A.1
    let ρ := A.1.representation
    let e := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom n)
    refine ⟨Representation.Equiv.mk e fun h => ?_⟩
    change ρ n * ρ (MulAut.conjNormal (H := N) (n : G)⁻¹ h) = ρ h * ρ n
    have hh : MulAut.conjNormal (H := N) (n : G)⁻¹ h = n⁻¹ * h * n := by
      apply Subtype.ext
      change (n : G)⁻¹ * (h : G) * (n : G)⁻¹⁻¹ = (n : G)⁻¹ * h * n
      rw [inv_inv]
    rw [hh, ← map_mul, ← map_mul]
    simp [mul_assoc]

end Normal

end Langlands.FiniteRepresentation
