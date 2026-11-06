import Langlands.AlgebraicGeometry.Picard.RigidifiedComparisonOfSheaf
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesAffineSheaf
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSheafGeneral
import Langlands.AlgebraicGeometry.Picard.RigidifiedRelativeIsoUniqueness
import Langlands.AlgebraicGeometry.Picard.EtaleFppfSheafComparison
import Langlands.AlgebraicGeometry.Sites.OverFppfSheaf
import Langlands.AlgebraicGeometry.Modules.LineBundleIsoDescentProof
import Langlands.AlgebraicGeometry.Modules.LineBundleDescentEffectiveProof

/-! # The etale Picard class sheaf of a rigidifiable morphism satisfies fppf descent -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.SchemeModule.RigidifiedModule

variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X)
  (section_eq : ε ≫ f = 𝟙 S)

/-- Under the universal structure-sheaf condition, the actual rigidified class
presheaf is an fppf sheaf on the entire slice. -/
lemma classPresheaf_isSheaf_fppf
    (hO : ∀ (T : Over S) (U : T.left.Opens),
      IsIso (((relativeProjection f).app T).app U)) :
    Presieve.IsSheaf (Scheme.fppfTopology.over S)
      (classPresheaf pullbackCoherence f ε section_eq) := by
  have unique := relative_iso_subsingleton f ε section_eq hO
  exact OverFppfSheaf.isSheaf_fppfTopology_over _
    (classPresheaf_isSheaf_zariski_of_unique f ε section_eq unique)
    (fun φ hf hs s ↦ classPresheaf_isSheafFor_affine f ε section_eq
      Langlands.Scheme.Modules.LineBundleIsoDescent.lineBundleIsoDescent
      Langlands.Scheme.Modules.lineBundleDescentEffective unique φ hf hs s)

/-- Forgetting rigidification is locally surjective in the etale topology. -/
lemma forgetClassNatTrans_isLocallySurjective_etale :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      (forgetClassNatTrans f ε section_eq) := by
  apply Presheaf.isLocallySurjective_of_le
    (J := Scheme.zariskiTopology.over S)
  · intro T R hR
    exact Scheme.zariskiTopology_le_etaleTopology _ hR
  · exact forgetClassNatTrans_isLocallySurjective_zariski f ε section_eq

/-- Forgetting rigidification is locally injective in the etale topology. -/
lemma forgetClassNatTrans_isLocallyInjective_etale :
    Presheaf.IsLocallyInjective (Scheme.etaleTopology.over S)
      (forgetClassNatTrans f ε section_eq) :=
  Presheaf.isLocallyInjective_of_injective _ _
    (fun T ↦ forgetClasses_injective f ε section_eq T.unop)

/-- If rigidified classes form an etale sheaf, forgetting the rigidification
followed by etale sheafification is an isomorphism of presheaves. -/
lemma forgetClassNatTrans_toEtaleClassSheaf_isIso
    (hP : Presieve.IsSheaf (Scheme.etaleTopology.over S)
      (classPresheaf pullbackCoherence f ε section_eq)) :
    IsIso (forgetClassNatTrans f ε section_eq ≫
      RelativePicard.toEtaleClassSheaf f) := by
  let P : Sheaf (Scheme.etaleTopology.over S) (Type (u + 1)) :=
    ⟨classPresheaf pullbackCoherence f ε section_eq,
      (isSheaf_iff_isSheaf_of_type _ _).mpr hP⟩
  let η : P ⟶ RelativePicard.etaleClassSheaf f :=
    ⟨forgetClassNatTrans f ε section_eq ≫ RelativePicard.toEtaleClassSheaf f⟩
  have := forgetClassNatTrans_isLocallyInjective_etale f ε section_eq
  have := forgetClassNatTrans_isLocallySurjective_etale f ε section_eq
  have hi : Sheaf.IsLocallyInjective η := by
    change Presheaf.IsLocallyInjective (Scheme.etaleTopology.over S)
      (forgetClassNatTrans f ε section_eq ≫ RelativePicard.toEtaleClassSheaf f)
    dsimp only [RelativePicard.toEtaleClassSheaf]
    infer_instance
  have hs : Sheaf.IsLocallySurjective η := by
    change Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      (forgetClassNatTrans f ε section_eq ≫ RelativePicard.toEtaleClassSheaf f)
    dsimp only [RelativePicard.toEtaleClassSheaf]
    infer_instance
  have : IsIso η := (Sheaf.isLocallyBijective_iff_isIso η).mp ⟨hi, hs⟩
  exact (sheafToPresheaf (Scheme.etaleTopology.over S) (Type (u + 1))).map_isIso η

/-- Under the universal structure-sheaf condition, forgetting the rigidification
followed by etale sheafification identifies the actual rigidified class presheaf
with the etale sheafification of ordinary line-bundle classes. -/
def rigidifiedEtaleClassIso
    (hO : ∀ (T : Over S) (U : T.left.Opens),
      IsIso (((relativeProjection f).app T).app U)) :
    classPresheaf pullbackCoherence f ε section_eq ≅
      RelativePicard.etaleClassSheafPresheaf f :=
  haveI := forgetClassNatTrans_toEtaleClassSheaf_isIso f ε section_eq
    (Presieve.isSheaf_of_le _ (Sites.etaleTopologyOver_le_fppfTopologyOver S)
      (classPresheaf_isSheaf_fppf f ε section_eq hO))
  asIso (forgetClassNatTrans f ε section_eq ≫ RelativePicard.toEtaleClassSheaf f)

lemma rigidifiedEtaleClassIso_hom
    (hO : ∀ (T : Over S) (U : T.left.Opens),
      IsIso (((relativeProjection f).app T).app U)) :
    (rigidifiedEtaleClassIso f ε section_eq hO).hom =
      forgetClassNatTrans f ε section_eq ≫ RelativePicard.toEtaleClassSheaf f :=
  rfl

/-- Under the universal structure-sheaf condition and a section, the actual
etale sheafification of ordinary line-bundle classes is an fppf sheaf. -/
theorem etaleClassSheafPresheaf_isSheaf_fppf (ε : S ⟶ X)
    (section_eq : ε ≫ f = 𝟙 S)
    (hO : ∀ (T : Over S) (U : T.left.Opens),
      IsIso (((relativeProjection f).app T).app U)) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
      (RelativePicard.etaleClassSheafPresheaf f) :=
  (Presheaf.isSheaf_of_iso_iff (rigidifiedEtaleClassIso f ε section_eq hO)).mp
    ((isSheaf_iff_isSheaf_of_type _ _).mpr (classPresheaf_isSheaf_fppf f ε section_eq hO))

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
