import Langlands.Global.AdelicSplitCenterMeasure
import Langlands.GroupScheme.Rational.CharacterRestrictionInjective

/-! # Independence of the chosen split component -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Global

namespace LeftCosetSpace

variable {H : Type u} [Group H] {Γ Δ : Subgroup H}

/-- Equal subgroups give the identity-on-representatives quotient equivalence. -/
def congrSubgroupHomeomorph [TopologicalSpace H] (h : Γ = Δ) :
    LeftCosetSpace Γ ≃ₜ LeftCosetSpace Δ := by
  subst Δ
  exact Homeomorph.refl _

@[simp] theorem congrSubgroupHomeomorph_mk [TopologicalSpace H] (h : Γ = Δ) (x : H) :
    congrSubgroupHomeomorph h (mk Γ x) = mk Δ x := by
  subst Δ
  rfl

theorem congrSubgroupHomeomorph_rightTranslate [TopologicalSpace H] (h : Γ = Δ)
    (g : H) (q : LeftCosetSpace Γ) :
    congrSubgroupHomeomorph h (rightTranslate Γ g q) =
      rightTranslate Δ g (congrSubgroupHomeomorph h q) := by
  subst Δ
  rfl

/-- The equality comparison preserves the inherited quotient sigma algebras. -/
theorem measurable_congrSubgroupHomeomorph [TopologicalSpace H] [MeasurableSpace H]
    (h : Γ = Δ) : Measurable (congrSubgroupHomeomorph h) := by
  subst Δ
  exact measurable_id

theorem measurable_congrSubgroupHomeomorph_symm [TopologicalSpace H] [MeasurableSpace H]
    (h : Γ = Δ) : Measurable (congrSubgroupHomeomorph h).symm := by
  subst Δ
  exact measurable_id

end LeftCosetSpace

namespace PositiveRealTorus

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
variable {T T' : CommGroupScheme (Spec (CommRingCat.of F))}
variable {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G}

/-- A factorization between the actual torus maps gives containment of positive images. -/
theorem imageSubgroup_le_of_factor (f : T ⟶ T')
    (hf : CommGroupScheme.groupHom f ≫ i' = i) :
    imageSubgroup F T G i ≤ imageSubgroup F T' G i' := by
  rintro _ ⟨a, ha, rfl⟩
  refine ⟨pointMap F T.toGrp T'.toGrp (Adeles F) (CommGroupScheme.groupHom f) a,
    map_intrinsicSubgroup_le F T T' f ⟨a, ha, rfl⟩, ?_⟩
  have h := congrArg (fun z : T.toGrp ⟶ G => a ≫ z.hom.hom) hf
  simpa only [pointMap_apply, Grp.comp_hom_hom, Category.assoc] using h

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The ambient positive subgroup is independent of the chosen actual split component. -/
theorem imageSubgroup_eq_of_splitComponents (hi : IsSplitComponent i)
    (hi' : IsSplitComponent i') :
    imageSubgroup F T G i = imageSubgroup F T' G i' := by
  apply le_antisymm
  · obtain ⟨f, hf⟩ := hi'.exists_comp_eq (finiteType_coordinateAlgebra G) hi.1
    exact imageSubgroup_le_of_factor F G (Additive.ofMul f) hf
  · obtain ⟨f, hf⟩ := hi.exists_comp_eq (finiteType_coordinateAlgebra G) hi'.1
    exact imageSubgroup_le_of_factor F G (Additive.ofMul f) hf

/-- Adjoining the unchanged rational points gives the same actual subgroup. -/
theorem positiveRationalSubgroup_eq_of_splitComponents (hi : IsSplitComponent i)
    (hi' : IsSplitComponent i') :
    positiveRationalSubgroup F G T i = positiveRationalSubgroup F G T' i' := by
  unfold positiveRationalSubgroup
  rw [imageSubgroup_eq_of_splitComponents F G hi hi']

/-- Change the supplied split component without changing any quotient representative. -/
def splitComponentQuotientHomeomorph (hi : IsSplitComponent i)
    (hi' : IsSplitComponent i') :
    PositiveRationalQuotient F G T i ≃ₜ PositiveRationalQuotient F G T' i' :=
  LeftCosetSpace.congrSubgroupHomeomorph
    (positiveRationalSubgroup_eq_of_splitComponents F G hi hi')

@[simp] theorem splitComponentQuotientHomeomorph_mk (hi : IsSplitComponent i)
    (hi' : IsSplitComponent i') (x : AdelicGroupPoints F G) :
    splitComponentQuotientHomeomorph F G hi hi'
      (LeftCosetSpace.mk (positiveRationalSubgroup F G T i) x) =
        LeftCosetSpace.mk (positiveRationalSubgroup F G T' i') x :=
  LeftCosetSpace.congrSubgroupHomeomorph_mk _ x

theorem splitComponentQuotientHomeomorph_rightTranslate (hi : IsSplitComponent i)
    (hi' : IsSplitComponent i') (g : AdelicGroupPoints F G)
    (q : PositiveRationalQuotient F G T i) :
    splitComponentQuotientHomeomorph F G hi hi'
      (LeftCosetSpace.rightTranslate (positiveRationalSubgroup F G T i) g q) =
        LeftCosetSpace.rightTranslate (positiveRationalSubgroup F G T' i') g
          (splitComponentQuotientHomeomorph F G hi hi' q) :=
  LeftCosetSpace.congrSubgroupHomeomorph_rightTranslate _ g q

/-- Change of split component is also an equivalence of the inherited sigma algebras. -/
def splitComponentQuotientMeasurableEquiv (hi : IsSplitComponent i)
    (hi' : IsSplitComponent i') :
    PositiveRationalQuotient F G T i ≃ᵐ PositiveRationalQuotient F G T' i' where
  toEquiv := (splitComponentQuotientHomeomorph F G hi hi').toEquiv
  measurable_toFun := LeftCosetSpace.measurable_congrSubgroupHomeomorph _
  measurable_invFun := LeftCosetSpace.measurable_congrSubgroupHomeomorph_symm _

@[simp] theorem splitComponentQuotientMeasurableEquiv_mk (hi : IsSplitComponent i)
    (hi' : IsSplitComponent i') (x : AdelicGroupPoints F G) :
    splitComponentQuotientMeasurableEquiv F G hi hi'
      (LeftCosetSpace.mk (positiveRationalSubgroup F G T i) x) =
        LeftCosetSpace.mk (positiveRationalSubgroup F G T' i') x :=
  splitComponentQuotientHomeomorph_mk F G hi hi' x

@[simp] theorem splitComponentQuotientMeasurableEquiv_normOneToPositiveQuotient
    (hi : IsSplitComponent i) (hi' : IsSplitComponent i')
    (q : NormOneRationalQuotient F G) :
    splitComponentQuotientMeasurableEquiv F G hi hi'
      (normOneToPositiveQuotient F G T i q) =
        normOneToPositiveQuotient F G T' i' q := by
  induction q using Quotient.inductionOn with
  | _ n => exact splitComponentQuotientMeasurableEquiv_mk F G hi hi' n.val

/-- Change of split component preserves the exact fixed norm-one quotient measure. -/
theorem measurePreserving_splitComponentQuotient (hi : IsSplitComponent i)
    (hi' : IsSplitComponent i') :
    MeasurePreserving (splitComponentQuotientMeasurableEquiv F G hi hi')
      (positiveRationalQuotientHaarMeasure F G T i)
      (positiveRationalQuotientHaarMeasure F G T' i') := by
  refine ⟨(splitComponentQuotientMeasurableEquiv F G hi hi').measurable, ?_⟩
  rw [positiveRationalQuotientHaarMeasure, Measure.map_map]
  · have h : (splitComponentQuotientMeasurableEquiv F G hi hi') ∘
        normOneToPositiveQuotient F G T i =
          normOneToPositiveQuotient F G T' i' := by
      funext q
      exact splitComponentQuotientMeasurableEquiv_normOneToPositiveQuotient F G hi hi' q
    rw [h]
    rfl
  · exact (splitComponentQuotientMeasurableEquiv F G hi hi').measurable
  · exact measurable_from_quotient.mpr
      ((LeftCosetSpace.measurable_mk (positiveRationalSubgroup F G T i)).comp
        measurable_subtype_coe)

end PositiveRealTorus
end Langlands.Global
