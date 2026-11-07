import Langlands.ClassField.Global.H1VanishingProof
import Langlands.Cohomology.Tate.TateTheoremProof

/-! # Tate cup isomorphisms for global fundamental classes

The global `H¹` vanishing theorem and a generating, restriction-compatible
class family give Tate's subgroup conditions for the actual idele classes.
-/

noncomputable section

namespace Langlands.ClassField.Global

open CategoryTheory NumberField
open scoped NumberField

universe u

set_option backward.isDefEq.respectTransparency false

variable (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E]

/-- Reindexing along the fixed-field Galois equivalence identifies the actual
relative idele-class cohomology with the cohomology restricted to a subgroup. -/
def ideleClassFixedFieldCohomologyIso (H : Subgroup (E ≃ₐ[F] E)) (n : ℕ) :
    relativeIdeleClassCohomology (IntermediateField.fixedField H) E n ≅
      groupCohomology (Rep.res H.subtype (relativeIdeleClassRepresentation F E)) n :=
  groupCohomology.mapIso (IntermediateField.subgroupEquivAlgEquiv H).symm
    (LinearEquiv.refl _ _) (fun _ => rfl) n

omit [IsGalois F E] in
/-- Restricting to a fixed field and then reindexing is the actual subgroup
restriction, with the identity map on idele-class coefficients. -/
theorem ideleClassFixedFieldCohomologyIso_restriction
    (H : Subgroup (E ≃ₐ[F] E)) (n : ℕ) :
    relativeIdeleClassRestriction F (IntermediateField.fixedField H) E n ≫
        (ideleClassFixedFieldCohomologyIso F E H n).hom =
      groupCohomology.map H.subtype
        (𝟙 (Rep.res H.subtype (relativeIdeleClassRepresentation F E))) n := by
  rw [ideleClassFixedFieldCohomologyIso, groupCohomology.mapIso_hom,
    ← groupCohomology.map_comp]
  exact groupCohomology.map_congr rfl rfl n

/-- A generating, restriction-compatible global family satisfies Tate's
conditions on every subgroup of the actual relative Galois group. -/
theorem fundamentalClass_subgroupConditions (c : FundamentalClass.ClassFamily.{u})
    (hgen : FundamentalClass.Generates c) (hres : FundamentalClass.Restriction c)
    (H : Subgroup (E ≃ₐ[F] E)) :
    Subsingleton
        (groupCohomology (Rep.res H.subtype (relativeIdeleClassRepresentation F E)) 1) ∧
      Nat.card
          (groupCohomology (Rep.res H.subtype (relativeIdeleClassRepresentation F E)) 2) =
        Nat.card H ∧
      AddSubgroup.zmultiples
          (groupCohomology.map H.subtype
            (𝟙 (Rep.res H.subtype (relativeIdeleClassRepresentation F E))) 2 (c F E)) = ⊤ := by
  let K := IntermediateField.fixedField H
  let e1 := ideleClassFixedFieldCohomologyIso F E H 1
  let e2 := ideleClassFixedFieldCohomologyIso F E H 2
  have h1 : Subsingleton (relativeIdeleClassCohomology K E 1) :=
    ideleClassH1Vanishing K E
  obtain ⟨horder, hgenerator⟩ := hgen K E
  have hr : relativeIdeleClassRestriction F K E 2 (c F E) = c K E :=
    (FundamentalClass.restriction_iff_classes c).mp hres F K E
  have hmap : groupCohomology.map H.subtype
      (𝟙 (Rep.res H.subtype (relativeIdeleClassRepresentation F E))) 2 (c F E) =
        e2.hom (c K E) := by
    rw [← hr]
    exact (ConcreteCategory.congr_hom
      (ideleClassFixedFieldCohomologyIso_restriction F E H 2) (c F E)).symm
  refine ⟨e1.toLinearEquiv.symm.injective.subsingleton, ?_, ?_⟩
  · rw [← Nat.card_congr e2.toLinearEquiv.toEquiv, ← AddSubgroup.card_top,
      ← hgenerator, Nat.card_zmultiples, horder]
    exact IntermediateField.finrank_fixedField_eq_card H
  · rw [hmap, eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := e2.toLinearEquiv.surjective y
    obtain ⟨k, rfl⟩ :=
      AddSubgroup.mem_zmultiples_iff.mp (hgenerator ▸ AddSubgroup.mem_top x)
    exact AddSubgroup.mem_zmultiples_iff.mpr
      ⟨k, (map_zsmul e2.toLinearEquiv k (c K E)).symm⟩

/-- Cup product with a generating, restriction-compatible global fundamental
class is bijective in every integer Tate degree. -/
theorem fundamentalClass_tateCup_bijective (c : FundamentalClass.ClassFamily.{u})
    (hgen : FundamentalClass.Generates c) (hres : FundamentalClass.Restriction c)
    (n : ℤ) :
    letI := Fintype.ofFinite (E ≃ₐ[F] E)
    Function.Bijective
      (Langlands.Tate.integralH2Cup (relativeIdeleClassRepresentation F E) n (c F E)) := by
  let := Fintype.ofFinite (E ≃ₐ[F] E)
  exact Langlands.Tate.tateCupIsomorphism (E ≃ₐ[F] E)
    (relativeIdeleClassRepresentation F E) (c F E)
    (fun _ _ P => fundamentalClass_subgroupConditions F E c hgen hres P.1) n

end Langlands.ClassField.Global
