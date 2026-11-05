import Langlands.Sheaf.Renard.PresheafAbelianStatements
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Abelianness of Renard's normalized basis presheaves
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

universe u v

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X] (B : OpenBasis X)

/-- Empty-value normalization contains the zero presheaf. -/
instance isNormalized_containsZero :
    ObjectProperty.ContainsZero (IsNormalized.{u,v} (B := B)) where
  exists_zero := ⟨0, isZero_zero _, fun U _ =>
    AddCommGrpCat.subsingleton_of_isZero
      (((evaluation _ _).obj (op U)).map_isZero (isZero_zero _))⟩

/-- A subpresheaf of a normalized presheaf is normalized. -/
instance isNormalized_isClosedUnderSubobjects :
    ObjectProperty.IsClosedUnderSubobjects (IsNormalized.{u,v} (B := B)) where
  prop_of_mono {_F _G} f _ hG U hU :=
    AddCommGrpCat.subsingleton_of_isZero
      (IsZero.of_mono (f.app (op U))
        (AddCommGrpCat.isZero_iff_subsingleton.mpr (hG U hU)))

/-- A quotient presheaf of a normalized presheaf is normalized. -/
instance isNormalized_isClosedUnderQuotients :
    ObjectProperty.IsClosedUnderQuotients (IsNormalized.{u,v} (B := B)) where
  prop_of_epi {_F _G} f _ hF U hU :=
    AddCommGrpCat.subsingleton_of_isZero
      (IsZero.of_epi (f.app (op U))
        (AddCommGrpCat.isZero_iff_subsingleton.mpr (hF U hU)))

/-- Finite products preserve the empty-value normalization. -/
instance isNormalized_isClosedUnderFiniteProducts :
    ObjectProperty.IsClosedUnderFiniteProducts (IsNormalized.{u,v} (B := B)) where
  isClosedUnderLimitsOfShape J := {
    limitsOfShape_le := by
      rintro F ⟨c⟩ U hU
      apply AddCommGrpCat.subsingleton_of_isZero
      apply (isLimitOfPreserves ((evaluation _ _).obj (op U)) c.isLimit).isZero_pt
      exact (Functor.isZero_iff _).mpr (fun j =>
        AddCommGrpCat.isZero_iff_subsingleton.mpr (c.prop_diag_obj j U hU))
  }

/-- The unchanged full category of normalized basis presheaves is abelian. -/
instance presheafAbelian : Abelian (Presheaf.{u,v} B) :=
  inferInstanceAs (Abelian (ObjectProperty.FullSubcategory (IsNormalized.{u,v} (B := B))))

/-- Renard A.VI.1, with the original independent section universe. -/
theorem presheafAbelianStatement :
    PresheafAbelianStatement.{u,v} B :=
  ⟨presheafAbelian B⟩

/-- The same abelianness assertion in the published source-axiom interface. -/
theorem presheafAbelianAxiomsStatement :
    PresheafAbelianAxiomsStatement.{u,v} B :=
  (Langlands.Renard.abelianAxioms_iff_nonempty_abelian (Presheaf.{u,v} B)).mpr
    (presheafAbelianStatement B)

end Langlands.Sheaf.Renard
