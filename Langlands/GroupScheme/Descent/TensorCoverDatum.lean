import Langlands.GroupScheme.Descent.FieldComponentCoverLifts
import Langlands.GroupScheme.Descent.TensorComponents
import Langlands.GroupScheme.Descent.TripleComponents
import Mathlib.Data.Fintype.EquivFin

/-! # Actual cover descent datum from a finite tensor decomposition -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.Descent

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

section SmallIndex

variable {I : Type} [Finite I]
variable (e : (L ⊗[k] L) ≃ₐ[L] (I → L)) (s : I → L ≃ₐ[k] L)
    (he : ∀ a b i, e (a ⊗ₜ[k] b) i = a * s i b)
variable {C H : GroupScheme (Spec (CommRingCat.of L))} {π : C ⟶ H}

/-- Lift a supplied target datum through a supplied cover using a finite tensor decomposition. -/
def Datum.liftFromTensorComponents (D : Datum (fieldMap k L) H)
    (hπ : IsSimplyConnectedCover π) : Datum (fieldMap k L) C := by
  letI : ∀ i, IsIso (tensorComponent e i ≫ snd (fieldMap k L)) :=
    fun i => tensorComponent_snd_isIso e s he i
  exact D.liftOnFieldComponents (tensorComponent e)
    (tripleComponent (fieldMap k L) (tensorComponent e)) hπ

/-- The tensor-component lift makes the original covering homomorphism compatible. -/
theorem Datum.compatible_liftFromTensorComponents (D : Datum (fieldMap k L) H)
    (hπ : IsSimplyConnectedCover π) :
    Compatible (D.liftFromTensorComponents e s he hπ) D π := by
  let : ∀ i, IsIso (tensorComponent e i ≫ snd (fieldMap k L)) :=
    fun i => tensorComponent_snd_isIso e s he i
  exact D.compatible_liftOnFieldComponents (tensorComponent e)
    (tripleComponent (fieldMap k L) (tensorComponent e)) hπ

end SmallIndex

section ArbitraryIndex

variable {J : Type v} [Fintype J]

/-- Reindex a tensor decomposition to a small finite type without changing the field universe. -/
def finiteTensorEquiv (e : (L ⊗[k] L) ≃ₐ[L] (J → L)) :
    (L ⊗[k] L) ≃ₐ[L] (Fin (Fintype.card J) → L) :=
  e.trans (AlgEquiv.piCongrLeft' L (fun _ : J => L) (Fintype.equivFin J))

@[simp]
theorem finiteTensorEquiv_apply (e : (L ⊗[k] L) ≃ₐ[L] (J → L))
    (x : L ⊗[k] L) (i : Fin (Fintype.card J)) :
    finiteTensorEquiv e x i = e x ((Fintype.equivFin J).symm i) := rfl

variable (e : (L ⊗[k] L) ≃ₐ[L] (J → L)) (s : J → L ≃ₐ[k] L)
    (he : ∀ a b i, e (a ⊗ₜ[k] b) i = a * s i b)
variable {C H : GroupScheme (Spec (CommRingCat.of L))} {π : C ⟶ H}

/-- An actual compatible cover datum, allowing the finite index in an arbitrary universe. -/
def Datum.liftWithTensorDecomposition (D : Datum (fieldMap k L) H)
    (hπ : IsSimplyConnectedCover π) : Datum (fieldMap k L) C :=
  D.liftFromTensorComponents (finiteTensorEquiv e)
    (fun i => s ((Fintype.equivFin J).symm i))
    (fun a b i => by simpa using he a b ((Fintype.equivFin J).symm i)) hπ

/-- Compatibility of the arbitrary-index tensor decomposition construction. -/
theorem Datum.compatible_liftWithTensorDecomposition (D : Datum (fieldMap k L) H)
    (hπ : IsSimplyConnectedCover π) :
    Compatible (D.liftWithTensorDecomposition e s he hπ) D π :=
  D.compatible_liftFromTensorComponents (finiteTensorEquiv e)
    (fun i => s ((Fintype.equivFin J).symm i))
    (fun a b i => by simpa using he a b ((Fintype.equivFin J).symm i)) hπ

end ArbitraryIndex

end Langlands.GroupScheme.Descent
