import Langlands.ClassFieldTheory.Local.ReciprocitySystem
import Langlands.Galois.Local.AbsoluteDefinitions
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Prime-degree norm surjectivity over the actual inertia fixed field -/

namespace Langlands.LocalClassField

universe u

/-- A compositum `E ⊔ D` of intermediate fields is finite-dimensional over `E`,
for the algebra given by the inclusion `E ≤ E ⊔ D`, whenever `D` is
finite-dimensional over the common base. -/
theorem finiteDimensional_sup_left {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E D : IntermediateField K L) [FiniteDimensional K D] :
    letI : Algebra E (E ⊔ D : IntermediateField K L) :=
      (IntermediateField.inclusion le_sup_left).toAlgebra
    FiniteDimensional E (E ⊔ D : IntermediateField K L) := by
  let _ : Algebra E (E ⊔ D : IntermediateField K L) :=
    (IntermediateField.inclusion le_sup_left).toAlgebra
  have hA : FiniteDimensional E (IntermediateField.adjoin E (D : Set L)) :=
    Module.rank_lt_aleph0_iff.mp <|
      (IntermediateField.adjoin_rank_le_of_isAlgebraic_right E D).trans_lt
        (Module.rank_lt_aleph0 K D)
  have h : (IntermediateField.adjoin E (D : Set L)).restrictScalars K = E ⊔ D := by
    rw [IntermediateField.restrictScalars_adjoin_eq_sup, IntermediateField.adjoin_self]
  let f : IntermediateField.adjoin E (D : Set L) ≃ₗ[E] (E ⊔ D : IntermediateField K L) :=
    { toFun := fun x => ⟨x.1, (SetLike.ext_iff.mp h x.1).mp x.2⟩
      invFun := fun y => ⟨y.1, (SetLike.ext_iff.mp h y.1).mpr y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact LinearEquiv.finiteDimensional f

/-- For a totally ramified Galois extension `D/F` of prime degree, the
determinant norm from the compositum `U ⊔ D` to the actual canonical inertia
fixed field `U` is surjective on multiplicative groups. -/
def PrimeNormOverInertiaFixedField : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (D : FiniteIntermediateExtension F.Carrier) [IsGalois F.Carrier D.field],
    let ell := Module.finrank F.Carrier D.field
    Nat.Prime ell →
      (D.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
          ell * F.canonicalTopologicalData.ramificationIndex →
        let U := IntermediateField.fixedField (F.absoluteInertia F.canonicalTopologicalData)
        let V := U ⊔ D.field
        letI : Algebra U V := (IntermediateField.inclusion le_sup_left).toAlgebra
        letI : FiniteDimensional U V := finiteDimensional_sup_left U D.field
        Function.Surjective (normUnits U V)

end Langlands.LocalClassField
