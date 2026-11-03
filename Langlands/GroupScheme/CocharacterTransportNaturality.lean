import Langlands.GroupScheme.CocharacterTransport

/-! # Naturality of canonical descent and cocharacter transport -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b)

/-- The canonical descent comparison, naturally in every group scheme over the original base. -/
def descentBaseChangeNatIso :
    GroupScheme.baseChange b ⋙ GroupScheme.baseChange a ≅ GroupScheme.baseChange b :=
  (Functor.mapGrpNatIso (Over.pullbackComp a b) ≪≫ Functor.mapGrpCompIso).symm ≪≫
    eqToIso (congrArg GroupScheme.baseChange ha)

/-- Each component is the existing canonical descent isomorphism. -/
theorem descentBaseChangeNatIso_app (G : GroupScheme B) :
    (descentBaseChangeNatIso b a ha).app G = descentBaseChangeIso b a ha G := by
  apply Iso.ext
  simp only [descentBaseChangeNatIso, descentBaseChangeIso, Iso.app_hom,
    NatTrans.comp_app, Iso.trans_hom, Iso.symm_hom,
    baseChangeCompIso, eqToIso.hom, eqToHom_app]
  rfl

/-- Descent commutes with every group homomorphism defined over the original base. -/
theorem descentBaseChangeIso_naturality {H G : GroupScheme B} (f : H ⟶ G) :
    (GroupScheme.baseChange a).map ((GroupScheme.baseChange b).map f) ≫
        (descentBaseChangeIso b a ha G).hom =
      (descentBaseChangeIso b a ha H).hom ≫ (GroupScheme.baseChange b).map f := by
  have h := (descentBaseChangeNatIso b a ha).hom.naturality f
  change (GroupScheme.baseChange a).map ((GroupScheme.baseChange b).map f) ≫
      ((descentBaseChangeNatIso b a ha).app G).hom =
    ((descentBaseChangeNatIso b a ha).app H).hom ≫
      (GroupScheme.baseChange b).map f at h
  simpa only [descentBaseChangeNatIso_app] using h

/-- Transport commutes with postcomposition by a homomorphism from the original base. -/
theorem transportCocharacter_naturality {H G : GroupScheme B} (f : H ⟶ G)
    (χ : (Gm S).toGrp ⟶ (GroupScheme.baseChange b).obj H) :
    transportCocharacter b a ha G (χ ≫ (GroupScheme.baseChange b).map f) =
      transportCocharacter b a ha H χ ≫ (GroupScheme.baseChange b).map f := by
  simp only [transportCocharacter, Functor.map_comp, Category.assoc]
  rw [descentBaseChangeIso_naturality]

end Langlands.GroupScheme
