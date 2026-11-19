import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescent.Affine
import Langlands.GroupScheme.IdentityJetCoordinateBaseChange
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Faithfully flat pullback of actual affine identity-jet functions -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.IdentityJet

variable {S T : Scheme.{u}} (G : GroupScheme S) [IsAffineHom G.X.hom] (b : T ⟶ S)

/-- The preimage of a jet open induced from the base is induced from the
preimage of that base open. -/
theorem baseChangeMap_preimage_eq (n : ℕ) (U : S.Opens) :
    projection ((GroupScheme.baseChange b).obj G) n ⁻¹ᵁ (b ⁻¹ᵁ U) =
      baseChangeMap G b n ⁻¹ᵁ (projection G n ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, ← (baseChange_isPullback G b n).w,
    Scheme.Hom.comp_preimage]

/-- The actual pullback of jet functions defines the algebra on the pulled-back open. -/
abbrev baseChangeSectionsAlgebra (n : ℕ) (U : S.Opens) :
    Algebra Γ(scheme G n, projection G n ⁻¹ᵁ U)
      Γ(scheme ((GroupScheme.baseChange b).obj G) n,
        projection ((GroupScheme.baseChange b).obj G) n ⁻¹ᵁ (b ⁻¹ᵁ U)) :=
  (baseChangeSectionsRingMap G b n U (b ⁻¹ᵁ U) le_rfl).toAlgebra

variable [IsAffineHom b] [Flat b] [Surjective b]

/-- Pullback of actual jet functions over an affine base open is faithfully flat
under affine faithfully flat base change. -/
theorem baseChangeSectionsRingMap_faithfullyFlat (n : ℕ) (U : S.affineOpens) :
    (baseChangeSectionsRingMap G b n U (b ⁻¹ᵁ U) le_rfl).FaithfullyFlat := by
  let f := baseChangeMap G b n
  have sq := (baseChange_isPullback G b n).flip
  let : IsAffineHom f := MorphismProperty.of_isPullback (P := @IsAffineHom) sq inferInstance
  let : Flat f := MorphismProperty.of_isPullback (P := @Flat) sq inferInstance
  let : Surjective f := MorphismProperty.of_isPullback (P := @Surjective) sq inferInstance
  let : IsClosedImmersion (inclusion G n) :=
    inferInstanceAs (IsClosedImmersion (ideal G n).subschemeι)
  let : IsAffineHom (projection G n) := by
    change IsAffineHom (inclusion G n ≫ G.X.hom)
    infer_instance
  let W := projection G n ⁻¹ᵁ U
  have hW : IsAffineOpen W := U.2.preimage (projection G n)
  have hflat (V : (scheme ((GroupScheme.baseChange b).obj G) n).Opens)
      (hV : V = f ⁻¹ᵁ W) : (f.appLE W V hV.le).hom.FaithfullyFlat := by
    subst V
    rw [Scheme.Hom.appLE_eq_app]
    exact Langlands.Scheme.UnitCocycleDescent.faithfullyFlat_app f hW (hW.preimage f)
  exact hflat _ (baseChangeMap_preimage_eq G b n U)

/-- Affine faithfully flat pullback detects equality of actual jet sections. -/
theorem baseChangeSectionsRingMap_injective (n : ℕ) (U : S.affineOpens) :
    Function.Injective (baseChangeSectionsRingMap G b n U (b ⁻¹ᵁ U) le_rfl) := by
  let := baseChangeSectionsAlgebra G b n U
  let : Module.FaithfullyFlat Γ(scheme G n, projection G n ⁻¹ᵁ U)
      Γ(scheme ((GroupScheme.baseChange b).obj G) n,
        projection ((GroupScheme.baseChange b).obj G) n ⁻¹ᵁ (b ⁻¹ᵁ U)) :=
    baseChangeSectionsRingMap_faithfullyFlat G b n U
  exact FaithfulSMul.algebraMap_injective _ _

end Langlands.GroupScheme.IdentityJet
