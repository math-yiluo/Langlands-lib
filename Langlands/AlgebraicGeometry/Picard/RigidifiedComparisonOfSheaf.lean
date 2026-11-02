import Langlands.AlgebraicGeometry.Picard.RigidifiedForgetLocallySurjective
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # The canonical Picard comparison from the rigidified sheaf condition -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.SchemeModule.RigidifiedModule

variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X)
  (section_eq : ε ≫ f = 𝟙 S)

/-- Forgetting rigidification is locally injective on the actual class presheaf. -/
lemma forgetClassNatTrans_isLocallyInjective :
    Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S)
      (forgetClassNatTrans f ε section_eq) :=
  Presheaf.isLocallyInjective_of_injective _ _
    (fun T ↦ forgetClasses_injective f ε section_eq T.unop)

/-- If the actual rigidified class presheaf is an fppf sheaf, its specified map to the
actual set-valued Picard sheaf is an isomorphism. -/
lemma toClassPicardSheaf_isIso_of_isSheaf
    (hP : Presieve.IsSheaf (Scheme.fppfTopology.over S)
      (classPresheaf pullbackCoherence f ε section_eq)) :
    IsIso (toClassPicardSheaf f ε section_eq) := by
  let P : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
    ⟨classPresheaf pullbackCoherence f ε section_eq,
      (isSheaf_iff_isSheaf_of_type _ _).mpr hP⟩
  let η : P ⟶ RelativePicard.classSheaf f := ⟨toClassPicardSheaf f ε section_eq⟩
  have := forgetClassNatTrans_isLocallyInjective f ε section_eq
  have := forgetClassNatTrans_isLocallySurjective f ε section_eq
  have hi : Sheaf.IsLocallyInjective η := by
    change Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S)
      (forgetClassNatTrans f ε section_eq ≫ RelativePicard.toClassSheaf f)
    dsimp only [RelativePicard.toClassSheaf]
    infer_instance
  have hs : Sheaf.IsLocallySurjective η := by
    change Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (forgetClassNatTrans f ε section_eq ≫ RelativePicard.toClassSheaf f)
    dsimp only [RelativePicard.toClassSheaf]
    infer_instance
  have : IsIso η := (Sheaf.isLocallyBijective_iff_isIso η).mp ⟨hi, hs⟩
  exact (sheafToPresheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map_isIso η

/-- The same sheaf condition identifies the specified canonical map to the underlying
presheaf of the actual abelian-group Picard sheaf. -/
lemma toPicardSheaf_isIso_of_isSheaf
    (hP : Presieve.IsSheaf (Scheme.fppfTopology.over S)
      (classPresheaf pullbackCoherence f ε section_eq)) :
    IsIso (toPicardSheaf f ε section_eq) := by
  have := toClassPicardSheaf_isIso_of_isSheaf f ε section_eq hP
  exact IsIso.of_isIso_fac_right
    (toPicardSheaf_forgetSheafIso_hom f ε section_eq)

/-- The canonical comparison isomorphism, conditional only on the actual rigidified
class presheaf satisfying the fppf sheaf condition. -/
def picardSheafIsoOfSheaf
    (hP : Presieve.IsSheaf (Scheme.fppfTopology.over S)
      (classPresheaf pullbackCoherence f ε section_eq)) :
    classPresheaf pullbackCoherence f ε section_eq ≅
      RelativePicard.sheafPresheaf f ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1} :=
  have := toPicardSheaf_isIso_of_isSheaf f ε section_eq hP
  asIso (toPicardSheaf f ε section_eq)

@[simp]
lemma picardSheafIsoOfSheaf_hom
    (hP : Presieve.IsSheaf (Scheme.fppfTopology.over S)
      (classPresheaf pullbackCoherence f ε section_eq)) :
    (picardSheafIsoOfSheaf f ε section_eq hP).hom =
      toPicardSheaf f ε section_eq := rfl

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
