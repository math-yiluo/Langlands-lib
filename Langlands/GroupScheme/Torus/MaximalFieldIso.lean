import Langlands.GroupScheme.SectionComparisonNaturality
import Langlands.GroupScheme.Torus.MaximalBaseChangeReflection
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.Torus.SplitDescent

/-! # Maximal tori under isomorphisms of fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

section Section

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (a : S ⟶ S') (ha : a ≫ b = 𝟙 S)

/-- Pullback along a base map followed by pullback along its section, naturally
identified with the identity on actual group schemes. -/
def baseChangeSectionComparisonNatIso :
    GroupScheme.baseChange b ⋙ GroupScheme.baseChange a ≅ 𝟭 (GroupScheme S) :=
  (Functor.mapGrpNatIso (Over.pullbackComp a b) ≪≫ Functor.mapGrpCompIso).symm ≪≫
    eqToIso (congrArg GroupScheme.baseChange ha) ≪≫
      (Functor.mapGrpNatIso Over.pullbackId ≪≫ Functor.mapGrpIdIso)

/-- The natural comparison has the existing section comparison as components. -/
theorem baseChangeSectionComparisonNatIso_app (G : GroupScheme S) :
    (baseChangeSectionComparisonNatIso b a ha).app G = baseChangeSectionIso b a ha G := by
  apply Iso.ext
  simp only [baseChangeSectionComparisonNatIso, baseChangeSectionIso, baseChangeIdIso,
    Iso.app_hom, NatTrans.comp_app, Iso.trans_hom, Iso.symm_hom,
    baseChangeCompIso, eqToIso.hom, eqToHom_app]
  rfl

end Section

section Fields

variable {k K : Type u} [Field k] [Field K]
variable {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}

/-- Pullback along a field isomorphism preserves maximality of a torus.
The proof uses inverse pullback and independent field-extension reflection. -/
theorem IsMaximalTorus.baseChange_fieldIso (hi : IsMaximalTorus i) (e : k ≃+* K) :
    IsMaximalTorus (T := (CommGroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom e.toRingHom))).obj T)
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom e.toRingHom))).map i) := by
  let b := Spec.map (CommRingCat.ofHom e.toRingHom)
  let a := Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  have ha : a ≫ b = 𝟙 (Spec (CommRingCat.of k)) := by
    dsimp [a, b]
    rw [← Spec.map_comp]
    have he : CommRingCat.ofHom e.toRingHom ≫ CommRingCat.ofHom e.symm.toRingHom =
        𝟙 (CommRingCat.of k) := by
      ext x
      exact e.symm_apply_apply x
    exact (congrArg Spec.map he).trans (Spec.map_id _)
  let : Algebra K k := e.symm.toRingHom.toAlgebra
  have hdouble : IsMaximalTorus
      (T := (CommGroupScheme.baseChange a).obj ((CommGroupScheme.baseChange b).obj T))
      ((GroupScheme.baseChange a).map ((GroupScheme.baseChange b).map i)) := by
    have hm := (hi.iso_comp
      (T' := (CommGroupScheme.baseChange a).obj ((CommGroupScheme.baseChange b).obj T))
      (baseChangeSectionIso b a ha T.toGrp)).comp_iso
        (baseChangeSectionIso b a ha G).symm
    have heq : (baseChangeSectionIso b a ha T.toGrp).hom ≫ i ≫
        (baseChangeSectionIso b a ha G).inv =
          (GroupScheme.baseChange a).map ((GroupScheme.baseChange b).map i) := by
      rw [← Category.assoc, ← RadicalFieldTransport.sectionIso_naturality b a ha i,
        Category.assoc, Iso.hom_inv_id, Category.comp_id]
    simpa only [Iso.symm_hom, Category.assoc, heq] using hm
  exact IsMaximalTorus.of_baseChange (hi.2.1.baseChange b) hdouble

end Fields

end Langlands.GroupScheme
