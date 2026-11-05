import Langlands.GroupScheme.Torus.SplitDescent

/-! # Naturality of group-scheme pullback along a section -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RadicalFieldTransport

/-- The pullback comparison along a section is natural in the group scheme. -/
theorem sectionIso_naturality {S S' : Scheme.{u}}
    (b : S' ⟶ S) (a : S ⟶ S') (ha : a ≫ b = 𝟙 S)
    {U G : GroupScheme S} (i : U ⟶ G) :
    (GroupScheme.baseChange a).map ((GroupScheme.baseChange b).map i) ≫
        (baseChangeSectionIso b a ha G).hom =
      (baseChangeSectionIso b a ha U).hom ≫ i := by
  have heq : ∀ {c d : S ⟶ S} (h : c = d),
      (GroupScheme.baseChange c).map i ≫
          (eqToIso (congrArg (fun t => (GroupScheme.baseChange t).obj G) h)).hom =
        (eqToIso (congrArg (fun t => (GroupScheme.baseChange t).obj U) h)).hom ≫
          (GroupScheme.baseChange d).map i := by
    intro c d h
    subst d
    simp
  have hc :=
    (((Functor.mapGrpNatIso (Over.pullbackComp a b)) ≪≫
      Functor.mapGrpCompIso).inv.naturality i)
  change (GroupScheme.baseChange a).map ((GroupScheme.baseChange b).map i) ≫
      (baseChangeCompIso b a G).inv =
    (baseChangeCompIso b a U).inv ≫ (GroupScheme.baseChange (a ≫ b)).map i at hc
  have hi :=
    (((Functor.mapGrpNatIso Over.pullbackId) ≪≫
      Functor.mapGrpIdIso).hom.naturality i)
  change (GroupScheme.baseChange (𝟙 S)).map i ≫ (baseChangeIdIso G).hom =
    (baseChangeIdIso U).hom ≫ i at hi
  change (GroupScheme.baseChange a).map ((GroupScheme.baseChange b).map i) ≫
      ((baseChangeCompIso b a G).inv ≫
        (eqToIso (congrArg (fun t => (GroupScheme.baseChange t).obj G) ha)).hom ≫
          (baseChangeIdIso G).hom) = _
  rw [← Category.assoc, hc, Category.assoc, ← Category.assoc _ _ (baseChangeIdIso G).hom,
    heq ha, Category.assoc, hi]
  simp only [baseChangeSectionIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]

/-- The inverse pullback comparison satisfies the same commuting square. -/
theorem sectionIso_inv_naturality {S S' : Scheme.{u}}
    (b : S' ⟶ S) (a : S ⟶ S') (ha : a ≫ b = 𝟙 S)
    {U G : GroupScheme S} (i : U ⟶ G) :
    i ≫ (baseChangeSectionIso b a ha G).inv =
      (baseChangeSectionIso b a ha U).inv ≫
        (GroupScheme.baseChange a).map ((GroupScheme.baseChange b).map i) := by
  apply (cancel_mono (baseChangeSectionIso b a ha G).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    sectionIso_naturality, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end Langlands.GroupScheme.RadicalFieldTransport
