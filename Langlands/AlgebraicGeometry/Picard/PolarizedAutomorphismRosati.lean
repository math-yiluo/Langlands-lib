import Langlands.AlgebraicGeometry.Picard.PolarizedAutomorphisms
import Langlands.AlgebraicGeometry.Picard.Rosati
import Langlands.AbelianScheme.Tate.IntegralReflectionAlgebra

/-! # Rosati norm identities for actual polarized automorphisms -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.Rosati

variable (P : Prerequisites.{u}) {S : Scheme.{u}}
  {A : AbelianScheme S} (W : DualData A) (hadd : W.Additivity P)
  (lam : A ⟶ W.dual P) [HasRationalInverse P W lam]

local notation "AutLam" => AbelianScheme.polarizedAutGroup P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability W.hasDual
  W.geometry W.inversePoincare W.evaluation lam

/-- The actual polarized automorphism's rational hom has left Rosati norm one. -/
theorem polarizedAut_involution_mul (f : AutLam) :
    involution P W hadd lam (homToHom0 f.val.hom) *
      endToEnd0 A f.val.hom = 1 := by
  change comp0 A A A (homToHom0 f.val.hom)
    (involution P W hadd lam (homToHom0 f.val.hom)) = id0 A
  have h := polarizedAutRationalization_preserves P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability W.hasDual
    W.geometry W.inversePoincare W.evaluation hadd lam f
  change comp0 A (W.dual P) (W.dual P)
    (comp0 A A (W.dual P) (homToHom0 f.val.hom) (homToHom0 lam))
    (W.dual0 P hadd (homToHom0 f.val.hom)) = homToHom0 lam at h
  have h' := congrArg (fun t => comp0 A (W.dual P) A t (polarizationInverse P W lam)) h
  simpa only [involution_apply, comp0_assoc, polarization_comp_inverse] using h'

/-- For the actual polarized automorphism, Rosati conjugation is its rational inverse. -/
theorem polarizedAut_involution_eq_inv (f : AutLam) :
    involution P W hadd lam (homToHom0 f.val.hom) = homToHom0 f.val.inv := by
  let r := polarizedAutRationalization P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability W.hasDual W.geometry
    W.inversePoincare W.evaluation lam f
  have h : r.hom ≫ involution P W hadd lam (homToHom0 f.val.hom) = 𝟙 _ :=
    polarizedAut_involution_mul P W hadd lam f
  change involution P W hadd lam (homToHom0 f.val.hom) = r.inv
  apply (cancel_epi r.hom).mp
  exact h.trans r.hom_inv_id.symm

/-- The actual polarized automorphism's rational hom also has right Rosati norm one. -/
theorem polarizedAut_mul_involution (f : AutLam) :
    endToEnd0 A f.val.hom *
      involution P W hadd lam (homToHom0 f.val.hom) = 1 := by
  rw [polarizedAut_involution_eq_inv P W hadd lam, endToEnd0_apply, end0_mul,
    comp0_homToHom0,
    f.val.inv_hom_id, homToHom0_id]
  rfl

variable {k : Type u} [Field k]
  {A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}

/-- Restriction of the actual rational Rosati trace form to integral endomorphisms. -/
def integralTraceForm (W : DualData A) (hadd : W.Additivity P) (lam : A ⟶ W.dual P)
    [HasRationalInverse P W lam] :
    CategoryTheory.End A →ₗ[ℤ] CategoryTheory.End A →ₗ[ℤ] ℚ :=
  ((traceForm P W hadd lam).restrictScalars₁₂ ℤ ℤ).compl₁₂ homToHom0 homToHom0

@[simp] theorem integralTraceForm_apply (W : DualData A) (hadd : W.Additivity P)
    (lam : A ⟶ W.dual P) [HasRationalInverse P W lam] (a b : CategoryTheory.End A) :
    integralTraceForm P W hadd lam a b =
      traceForm P W hadd lam (homToHom0 a) (homToHom0 b) := rfl

/-- Every actual polarized automorphism has the same actual trace-form length. -/
theorem polarizedAut_integralTraceForm_self (W : DualData A) (hadd : W.Additivity P)
    (lam : A ⟶ W.dual P) [HasRationalInverse P W lam]
    (f : AbelianScheme.polarizedAutGroup P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability W.hasDual W.geometry
      W.inversePoincare W.evaluation lam) :
    integralTraceForm P W hadd lam f.val.hom f.val.hom =
      geometricEndomorphismTrace A 1 := by
  simpa only [integralTraceForm_apply, traceForm_apply, endToEnd0_apply] using
    congrArg (geometricEndomorphismTrace A) (polarizedAut_mul_involution P W hadd lam f)

/-- Canonical rationalization of actual homomorphisms is injective in characteristic zero. -/
theorem homToHom0_injective_of_charZero [CharZero k]
    (A B : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))) :
    Function.Injective (homToHom0 (A := A) (B := B)) := by
  apply Tate.ofHom_injective
  intro n
  have hn : (n.val : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt n.property.1)
  simpa using (Ne.isUnit hn).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

/-- The actual polarized automorphism group injects into its canonical rationalization. -/
theorem polarizedAutRationalization_injective [CharZero k]
    (W : DualData A) (lam : A ⟶ W.dual P) :
    Function.Injective (polarizedAutRationalization P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability W.hasDual
      W.geometry W.inversePoincare W.evaluation lam) := by
  intro f g h
  apply Subtype.ext
  apply Iso.ext
  apply homToHom0_injective_of_charZero A A
  exact congrArg (fun e : Aut (Langlands.Rationalization.of A) => e.hom) h

end Langlands.AbelianScheme.Rosati
