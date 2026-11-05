import Langlands.Global.AdelicSIntegersColimitStatement
import Langlands.Global.CurvePlaceAdeleDiagonal
import Langlands.Global.FiniteAdeleLevelColimitProof

/-! # The original fields as colimits of their actual integer rings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Global

section Curve

variable (k F : Type u) [Field k] [PerfectField k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
variable (S : Finset (AlgebraicCurve.Place k F))

/-- Finite poles give an integer stage containing any prescribed initial set. -/
theorem exists_mem_curvePlaceSIntegersAbove (x : F) :
    ∃ T : AdelicLevelIndexAbove S, x ∈ curvePlaceSIntegers k F T.val := by
  classical
  obtain ⟨T, hx⟩ := exists_mem_curvePlaceSIntegers k F x
  exact ⟨adelicLevelIndexEnlarge S T,
    curvePlaceSIntegers_mono k F Finset.subset_union_right hx⟩

/-- Descend compatible integer-stage maps through the actual field cover. -/
def curvePlaceSIntegersOverRingDesc (c : Cocone (curvePlaceSIntegersOverDiagram k F S)) :
    F →+* c.pt := by
  classical
  exact SubringCover.desc (B := c.pt)
    (fun T => curvePlaceSIntegers k F (adelicLevelIndexEnlarge S T).val)
    (fun _ _ h => curvePlaceSIntegers_mono k F (adelicLevelIndexEnlarge_mono S h))
    (fun x => by
      obtain ⟨T, hx⟩ := exists_mem_curvePlaceSIntegers k F x
      exact ⟨T, curvePlaceSIntegers_mono k F Finset.subset_union_right hx⟩)
    (fun T => (c.ι.app (adelicLevelIndexEnlarge S T)).hom.toRingHom)
    (fun _ _ h => congrArg (fun f => f.hom.toRingHom)
      (c.w (homOfLE (adelicLevelIndexEnlarge_mono S h))))

/-- The descended ring map restricts to the given map on each actual stage. -/
theorem curvePlaceSIntegersOverRingDesc_apply
    (c : Cocone (curvePlaceSIntegersOverDiagram k F S))
    (T : AdelicLevelIndexAbove S) (a : curvePlaceSIntegersOver k F S T) :
    curvePlaceSIntegersOverRingDesc k F S c a.val = (c.ι.app T).hom a := by
  classical
  let U := adelicLevelIndexEnlarge S T.val
  let a' : curvePlaceSIntegers k F U.val :=
    ⟨a.val, curvePlaceSIntegers_mono k F Finset.subset_union_right a.property⟩
  have hdesc : curvePlaceSIntegersOverRingDesc k F S c a.val = (c.ι.app U).hom a' :=
    SubringCover.desc_apply
      (fun V => curvePlaceSIntegers k F (adelicLevelIndexEnlarge S V).val) _ _ _ _ T.val a'
  have hcompat := congrArg (fun f => f.hom a)
    (c.w (homOfLE (show T ≤ U from Finset.subset_union_right)))
  exact hdesc.trans hcompat

/-- The descended map preserves the original initial integer-base action. -/
def curvePlaceSIntegersOverDesc (c : Cocone (curvePlaceSIntegersOverDiagram k F S)) :
    curvePlaceFieldOver k F S ⟶ c.pt := by
  let f : curvePlaceFieldOver k F S →ₐ[curvePlaceSIntegers k F S] c.pt :=
    { toRingHom := curvePlaceSIntegersOverRingDesc k F S c
      commutes' := by
        intro r
        let T : AdelicLevelIndexAbove S := ⟨S, Finset.Subset.refl S⟩
        have hr := curvePlaceSIntegersOverRingDesc_apply k F S c T
          (algebraMap (curvePlaceSIntegers k F S) (curvePlaceSIntegersOver k F S T) r)
        exact hr.trans ((c.ι.app T).hom.commutes r) }
  exact ConcreteCategory.ofHom (C := CommAlgCat (curvePlaceSIntegers k F S)) f

/-- The original field-valued integer cocone is a colimit over the original base. -/
def curvePlaceSIntegersOverIsColimit : IsColimit (curvePlaceSIntegersOverCocone k F S) where
  desc c := curvePlaceSIntegersOverDesc k F S c
  fac c T := by
    ext a
    exact curvePlaceSIntegersOverRingDesc_apply k F S c T a
  uniq c m hm := by
    classical
    ext a
    obtain ⟨T, ha⟩ := exists_mem_curvePlaceSIntegersAbove k F S a
    let b : curvePlaceSIntegersOver k F S T := ⟨a, ha⟩
    have h := congrArg (fun f => f.hom b) (hm T)
    exact h.trans (curvePlaceSIntegersOverRingDesc_apply k F S c T b).symm

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K]
variable (S : Finset (FinitePlace K))

/-- Outside-set integer conditions weaken when the exceptional set increases. -/
theorem numberFieldSIntegers_mono {T U : Finset (FinitePlace K)} (hTU : T ⊆ U) :
    ((T : Set (FinitePlace K)).integer K).toSubring ≤
      ((U : Set (FinitePlace K)).integer K).toSubring :=
  fun _ hx v hv => hx v (fun h => hv (hTU h))

/-- A number-field element has only finitely many nonintegral finite places. -/
theorem exists_mem_numberFieldSIntegers (x : K) :
    ∃ T : Finset (FinitePlace K), x ∈ (T : Set (FinitePlace K)).integer K := by
  classical
  let h := IsDedekindDomain.HeightOneSpectrum.Support.finite (NumberField.RingOfIntegers K) x
  refine ⟨h.toFinset, ?_⟩
  intro v hv
  apply le_of_not_gt
  intro hx
  exact hv (h.mem_toFinset.mpr hx)

/-- Enlarge the finite nonintegral support by any prescribed initial set. -/
theorem exists_mem_numberFieldSIntegersAbove (x : K) :
    ∃ T : AdelicLevelIndexAbove S, x ∈ (T.val : Set (FinitePlace K)).integer K := by
  classical
  obtain ⟨T, hx⟩ := exists_mem_numberFieldSIntegers K x
  exact ⟨adelicLevelIndexEnlarge S T,
    numberFieldSIntegers_mono K Finset.subset_union_right hx⟩

/-- Descend compatible integer-stage maps through the actual number-field cover. -/
def numberFieldSIntegersOverRingDesc (c : Cocone (numberFieldSIntegersOverDiagram K S)) :
    K →+* c.pt := by
  classical
  exact SubringCover.desc (B := c.pt)
    (fun T => (((adelicLevelIndexEnlarge S T).val : Set (FinitePlace K)).integer K).toSubring)
    (fun _ _ h => numberFieldSIntegers_mono K (adelicLevelIndexEnlarge_mono S h))
    (fun x => by
      obtain ⟨T, hx⟩ := exists_mem_numberFieldSIntegers K x
      exact ⟨T, numberFieldSIntegers_mono K Finset.subset_union_right hx⟩)
    (fun T => (c.ι.app (adelicLevelIndexEnlarge S T)).hom.toRingHom)
    (fun _ _ h => congrArg (fun f => f.hom.toRingHom)
      (c.w (homOfLE (adelicLevelIndexEnlarge_mono S h))))

/-- The descended ring map restricts to the given map on each integer stage. -/
theorem numberFieldSIntegersOverRingDesc_apply
    (c : Cocone (numberFieldSIntegersOverDiagram K S))
    (T : AdelicLevelIndexAbove S) (a : numberFieldSIntegersOver K S T) :
    numberFieldSIntegersOverRingDesc K S c a.val = (c.ι.app T).hom a := by
  classical
  let U := adelicLevelIndexEnlarge S T.val
  let a' : (U.val : Set (FinitePlace K)).integer K :=
    ⟨a.val, numberFieldSIntegers_mono K Finset.subset_union_right a.property⟩
  have hdesc : numberFieldSIntegersOverRingDesc K S c a.val = (c.ι.app U).hom a' :=
    SubringCover.desc_apply
      (fun V => (((adelicLevelIndexEnlarge S V).val : Set (FinitePlace K)).integer K).toSubring)
      _ _ _ _ T.val a'
  have hcompat := congrArg (fun f => f.hom a)
    (c.w (homOfLE (show T ≤ U from Finset.subset_union_right)))
  exact hdesc.trans hcompat

/-- The descended map preserves the original initial integer-base action. -/
def numberFieldSIntegersOverDesc (c : Cocone (numberFieldSIntegersOverDiagram K S)) :
    numberFieldOver K S ⟶ c.pt := by
  let f : numberFieldOver K S →ₐ[((S : Set (FinitePlace K)).integer K)] c.pt :=
    { toRingHom := numberFieldSIntegersOverRingDesc K S c
      commutes' := by
        intro r
        let T : AdelicLevelIndexAbove S := ⟨S, Finset.Subset.refl S⟩
        have hr := numberFieldSIntegersOverRingDesc_apply K S c T
          (algebraMap ((S : Set (FinitePlace K)).integer K) (numberFieldSIntegersOver K S T) r)
        exact hr.trans ((c.ι.app T).hom.commutes r) }
  exact ConcreteCategory.ofHom (C := CommAlgCat ((S : Set (FinitePlace K)).integer K)) f

/-- The original number-field cocone is a colimit over the original integer base. -/
def numberFieldSIntegersOverIsColimit : IsColimit (numberFieldSIntegersOverCocone K S) where
  desc c := numberFieldSIntegersOverDesc K S c
  fac c T := by
    ext a
    exact numberFieldSIntegersOverRingDesc_apply K S c T a
  uniq c m hm := by
    classical
    ext a
    obtain ⟨T, ha⟩ := exists_mem_numberFieldSIntegersAbove K S a
    let b : numberFieldSIntegersOver K S T := ⟨a, ha⟩
    have h := congrArg (fun f => f.hom b) (hm T)
    exact h.trans (numberFieldSIntegersOverRingDesc_apply K S c T b).symm

end NumberField

/-- Exhaustion and the exact integer-algebra colimit in both arithmetic branches. -/
theorem adelicSIntegersColimit : AdelicSIntegersColimitStatement.{u} := by
  constructor
  · intro k F _ _ _ _ _ _ _ S
    exact ⟨exists_mem_curvePlaceSIntegersAbove k F S, ⟨curvePlaceSIntegersOverIsColimit k F S⟩⟩
  · intro K _ _ S
    exact ⟨exists_mem_numberFieldSIntegersAbove K S, ⟨numberFieldSIntegersOverIsColimit K S⟩⟩

end Langlands.Global
