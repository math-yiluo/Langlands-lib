import Langlands.GroupScheme.RelativeLevi.ModuliValue
import Langlands.AbelianScheme.Tate.BaseChangeCoherence

/-! # Ambient transport and identity comparison of relative Levi images -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeLevi.LeviImage

variable {S : Scheme.{u}} {P P' P'' : GroupScheme S}

@[simp]
theorem mapIso_refl (F : LeviImage P) : F.mapIso (Iso.refl P) = F := by
  apply ext
  exact SubgroupFunctor.comap_id F.val

/-- Ambient transport follows composition of actual isomorphisms. -/
theorem mapIso_trans (e : P ≅ P') (e' : P' ≅ P'') (F : LeviImage P) :
    F.mapIso (e ≪≫ e') = (F.mapIso e).mapIso e' := by
  apply ext
  exact SubgroupFunctor.comap_comp _ _ _

/-- An ambient isomorphism gives an equivalence of actual Levi subgroup images. -/
def mapIsoEquiv (e : P ≅ P') : LeviImage P ≃ LeviImage P' where
  toFun := mapIso e
  invFun := mapIso e.symm
  left_inv F := by
    rw [← mapIso_trans]
    simpa using mapIso_refl F
  right_inv F := by
    rw [← mapIso_trans]
    simpa using mapIso_refl F

/-- The identity pullback carries exactly the original relative Levi images. -/
def baseChangeIdEquiv (P : GroupScheme S) :
    LeviImage ((GroupScheme.baseChange (𝟙 S)).obj P) ≃ LeviImage P :=
  mapIsoEquiv (baseChangeIdIso P)

/-- A point of the identity-pullback moduli problem gives an actual Levi over the
original base, without an extra existence hypothesis. -/
theorem exists_presentation_of_identity_point (P : GroupScheme S)
    (F : LeviImage ((GroupScheme.baseChange (𝟙 S)).obj P)) :
    ∃ (L : GroupScheme S) (l : L ⟶ P), IsRelativeLeviSubgroup l ∧
      SubgroupFunctor.range l = (baseChangeIdEquiv P F).val :=
  (baseChangeIdEquiv P F).exists_presentation

end Langlands.GroupScheme.RelativeLevi.LeviImage
