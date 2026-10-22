import Langlands.FieldTheory.AlgClosedAutomorphismExtensionStatement
import Mathlib.FieldTheory.IsAlgClosed.Classification

/-! # Extending base-field automorphisms -/

namespace Langlands.FieldTheory

universe uF uOmega

/-- Every base-field automorphism extends to an algebraically closed extension. -/
theorem algClosedAutomorphismExtension :
    AlgClosedAutomorphismExtensionStatement.{uF, uOmega} := by
  classical
  intro F _ Ω _ _ _ e
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F Ω
  let A := Algebra.adjoin F (Set.range ((↑) : s → Ω))
  let p : MvPolynomial s F ≃ₐ[F] A := hs.1.aevalEquiv
  let eA : A ≃+* A := p.symm.toRingEquiv.trans
    ((MvPolynomial.mapEquiv s e).trans p.toRingEquiv)
  let : IsAlgClosure A Ω :=
    IsAlgClosed.isAlgClosure_of_transcendence_basis ((↑) : s → Ω) hs
  refine ⟨IsAlgClosure.equivOfEquiv Ω Ω eA, ?_⟩
  intro x
  have heA : eA (algebraMap F A x) = algebraMap F A (e x) := by
    simp [eA, MvPolynomial.algebraMap_eq]
    exact p.commutes (e x)
  calc
    IsAlgClosure.equivOfEquiv Ω Ω eA (algebraMap F Ω x) =
        IsAlgClosure.equivOfEquiv Ω Ω eA
          (algebraMap A Ω (algebraMap F A x)) := by
            rw [IsScalarTower.algebraMap_apply F A Ω]
    _ = algebraMap A Ω (eA (algebraMap F A x)) :=
      IsAlgClosure.equivOfEquiv_algebraMap Ω Ω eA _
    _ = algebraMap F Ω (e x) := by
      rw [heA, IsScalarTower.algebraMap_apply F A Ω]

end Langlands.FieldTheory
