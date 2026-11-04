import Langlands.Global.AdelicFixedModelAlgebraColimitStatement
import Langlands.Global.FiniteAdeleLevelColimitProof
import Langlands.Global.CurvePlaceAdeleLevelTopologyProof
import Langlands.Global.NumberFieldAdeleLevelTopologyProof

/-! # Proof of the actual fixed-initial-base adelic algebra colimits -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Global

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
variable (S : Finset (AlgebraicCurve.Place k F))

/-- Descend compatible fixed-base maps through the enlarged actual subring cover. -/
def curvePlaceAdeleOverRingDesc (c : Cocone (curvePlaceAdeleLevelOverDiagram k F S)) :
    CurvePlaceAdeleRing k F →+* c.pt := by
  classical
  exact SubringCover.desc (B := c.pt)
    (fun T => curvePlaceAdeleLevel k F (adelicLevelIndexEnlarge S T).val)
    (fun _ _ h => curvePlaceAdeleLevel_mono k F (adelicLevelIndexEnlarge_mono S h))
    (fun a => by
      obtain ⟨T, ha⟩ := exists_mem_curvePlaceAdeleLevel k F a
      exact ⟨T, curvePlaceAdeleLevel_mono k F Finset.subset_union_right ha⟩)
    (fun T => (c.ι.app (adelicLevelIndexEnlarge S T)).hom.toRingHom)
    (fun _ _ h => congrArg (fun f => f.hom.toRingHom)
      (c.w (homOfLE (adelicLevelIndexEnlarge_mono S h))))

/-- The descended map agrees with the original component at every actual stage. -/
theorem curvePlaceAdeleOverRingDesc_apply (c : Cocone (curvePlaceAdeleLevelOverDiagram k F S))
    (T : AdelicLevelIndexAbove S) (a : curvePlaceAdeleLevelOver k F S T) :
    curvePlaceAdeleOverRingDesc k F S c a.val = (c.ι.app T).hom a := by
  classical
  let U := adelicLevelIndexEnlarge S T.val
  let a' : curvePlaceAdeleLevel k F U.val :=
    ⟨a.val, curvePlaceAdeleLevel_mono k F Finset.subset_union_right a.property⟩
  have hdesc : curvePlaceAdeleOverRingDesc k F S c a.val = (c.ι.app U).hom a' :=
    SubringCover.desc_apply
      (fun V => curvePlaceAdeleLevel k F (adelicLevelIndexEnlarge S V).val) _ _ _ _ T.val a'
  have hcompat := congrArg (fun f => f.hom a)
    (c.w (homOfLE (show T ≤ U from Finset.subset_union_right)))
  exact hdesc.trans hcompat

/-- The descended ring map is an algebra map for the original integer scalar action. -/
def curvePlaceAdeleOverDesc (c : Cocone (curvePlaceAdeleLevelOverDiagram k F S)) :
    curvePlaceAdeleOver k F S ⟶ c.pt := by
  let f : curvePlaceAdeleOver k F S →ₐ[curvePlaceSIntegers k F S] c.pt :=
    { toRingHom := curvePlaceAdeleOverRingDesc k F S c
      commutes' := by
        intro r
        let T : AdelicLevelIndexAbove S := ⟨S, Finset.Subset.refl S⟩
        have hr := curvePlaceAdeleOverRingDesc_apply k F S c T
          (algebraMap (curvePlaceSIntegers k F S) (curvePlaceAdeleLevelOver k F S T) r)
        exact hr.trans ((c.ι.app T).hom.commutes r) }
  exact ConcreteCategory.ofHom (C := CommAlgCat (curvePlaceSIntegers k F S)) f

/-- The literal full-adele cocone has the exact fixed-base algebra universal property. -/
def curvePlaceAdeleOverIsColimit : IsColimit (curvePlaceAdeleOverCocone k F S) where
  desc c := curvePlaceAdeleOverDesc k F S c
  fac c T := by
    ext a
    exact curvePlaceAdeleOverRingDesc_apply k F S c T a
  uniq c m hm := by
    classical
    ext a
    obtain ⟨T, ha⟩ := exists_mem_curvePlaceAdeleLevel k F a
    let U := adelicLevelIndexEnlarge S T
    let b : curvePlaceAdeleLevelOver k F S U :=
      ⟨a, curvePlaceAdeleLevel_mono k F Finset.subset_union_right ha⟩
    have h := congrArg (fun f => f.hom b) (hm U)
    exact h.trans (curvePlaceAdeleOverRingDesc_apply k F S c U b).symm

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K]
variable (S : Finset (FinitePlace K))

/-- Descend compatible fixed-base maps through the enlarged actual subring cover. -/
def numberFieldAdeleOverRingDesc (c : Cocone (numberFieldAdeleLevelOverDiagram K S)) :
    Adeles K →+* c.pt := by
  classical
  exact SubringCover.desc (B := c.pt)
    (fun T => numberFieldAdeleLevel K (adelicLevelIndexEnlarge S T).val)
    (fun _ _ h => numberFieldAdeleLevel_mono K (adelicLevelIndexEnlarge_mono S h))
    (fun a => by
      obtain ⟨T, ha⟩ := exists_mem_numberFieldAdeleLevel K a
      exact ⟨T, numberFieldAdeleLevel_mono K Finset.subset_union_right ha⟩)
    (fun T => (c.ι.app (adelicLevelIndexEnlarge S T)).hom.toRingHom)
    (fun _ _ h => congrArg (fun f => f.hom.toRingHom)
      (c.w (homOfLE (adelicLevelIndexEnlarge_mono S h))))

/-- The descended map agrees with the original component at every actual stage. -/
theorem numberFieldAdeleOverRingDesc_apply (c : Cocone (numberFieldAdeleLevelOverDiagram K S))
    (T : AdelicLevelIndexAbove S) (a : numberFieldAdeleLevelOver K S T) :
    numberFieldAdeleOverRingDesc K S c a.val = (c.ι.app T).hom a := by
  classical
  let U := adelicLevelIndexEnlarge S T.val
  let a' : numberFieldAdeleLevel K U.val :=
    ⟨a.val, numberFieldAdeleLevel_mono K Finset.subset_union_right a.property⟩
  have hdesc : numberFieldAdeleOverRingDesc K S c a.val = (c.ι.app U).hom a' :=
    SubringCover.desc_apply
      (fun V => numberFieldAdeleLevel K (adelicLevelIndexEnlarge S V).val) _ _ _ _ T.val a'
  have hcompat := congrArg (fun f => f.hom a)
    (c.w (homOfLE (show T ≤ U from Finset.subset_union_right)))
  exact hdesc.trans hcompat

/-- The descended ring map is an algebra map for the original integer scalar action. -/
def numberFieldAdeleOverDesc (c : Cocone (numberFieldAdeleLevelOverDiagram K S)) :
    numberFieldAdeleOver K S ⟶ c.pt := by
  let f : numberFieldAdeleOver K S →ₐ[((S : Set (FinitePlace K)).integer K)] c.pt :=
    { toRingHom := numberFieldAdeleOverRingDesc K S c
      commutes' := by
        intro r
        let T : AdelicLevelIndexAbove S := ⟨S, Finset.Subset.refl S⟩
        have hr := numberFieldAdeleOverRingDesc_apply K S c T
          (algebraMap (((S : Set (FinitePlace K)).integer K)) (numberFieldAdeleLevelOver K S T) r)
        exact hr.trans ((c.ι.app T).hom.commutes r) }
  exact ConcreteCategory.ofHom (C := CommAlgCat (((S : Set (FinitePlace K)).integer K))) f

/-- The literal full-adele cocone has the exact fixed-base algebra universal property. -/
def numberFieldAdeleOverIsColimit : IsColimit (numberFieldAdeleOverCocone K S) where
  desc c := numberFieldAdeleOverDesc K S c
  fac c T := by
    ext a
    exact numberFieldAdeleOverRingDesc_apply K S c T a
  uniq c m hm := by
    classical
    ext a
    obtain ⟨T, ha⟩ := exists_mem_numberFieldAdeleLevel K a
    let U := adelicLevelIndexEnlarge S T
    let b : numberFieldAdeleLevelOver K S U :=
      ⟨a, numberFieldAdeleLevel_mono K Finset.subset_union_right ha⟩
    have h := congrArg (fun f => f.hom b) (hm U)
    exact h.trans (numberFieldAdeleOverRingDesc_apply K S c U b).symm

end NumberField

/-- Both arithmetic branches of the fixed-base algebra-colimit target. -/
theorem adelicFixedModelAlgebraColimit : AdelicFixedModelAlgebraColimitStatement.{u} := by
  constructor
  · intro k F _ _ _ S
    exact ⟨curvePlaceAdeleOverIsColimit k F S⟩
  · intro K _ _ S
    exact ⟨numberFieldAdeleOverIsColimit K S⟩

end Langlands.Global
