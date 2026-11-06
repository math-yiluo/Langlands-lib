import Langlands.LocalFactor.CommonClosure
import Langlands.VirtualRepresentation.ExactDeterminantInduction

/-! # Determinant transfer and the supplied common-closure reciprocity square -/

noncomputable section

universe uG uH uF uV

namespace Langlands.LocalClassField

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]

/-- Continuous character descent commutes with the induced quotient map. -/
theorem abelianizationLift_map_apply (f : G →ₜ* H) (χ : H →ₜ* ℂˣ)
    (q : TopologicalAbelianization G) :
    abelianizationLift χ (abelianizationMap f q) =
      abelianizationLift (χ.comp f) q := by
  induction q using QuotientGroup.induction_on with
  | H g => rfl

/-- Evaluation of the actual subgroup transfer by a continuous character. -/
theorem character_subgroupTransfer_apply
    {A B : Subgroup G} (h : A ≤ B) [A.FiniteIndex]
    (hA : IsOpen (A : Set G)) (χ : A →ₜ* ℂˣ) (g : B) :
    (χ.toMonoidHom.comp (subgroupOfEquiv h).toMonoidHom).transfer g =
      abelianizationLift χ
        (subgroupAbelianTransfer h hA (abelianizationProjection B g)) := by
  change _ = abelianizationLift χ
    (abelianizationMap (subgroupOfEquiv h : A.subgroupOf B →ₜ* A)
      ((abelianizationProjection (A.subgroupOf B)).toMonoidHom.transfer g))
  rw [abelianizationLift_map_apply]
  exact VirtualRepresentation.ExactGrothendieckGroup.characterTransfer_comp
    (A.subgroupOf B) (abelianizationProjection (A.subgroupOf B)).toMonoidHom
    (abelianizationLift (χ.comp (subgroupOfEquiv h : _ →ₜ* _))).toMonoidHom g

end Langlands.LocalClassField

namespace Langlands.LocalFactor.CommonClosure

open LocalClassField VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Every unit has a Weil lift for a supplied reciprocity equivalence. -/
theorem exists_reciprocityUnits_eq (e : ReciprocityFamily F) (E : Extension F)
    (a : E.fieldˣ) : ∃ w : weilSubgroup F E, reciprocityUnits F e E w = a := by
  let := (fieldData F E).topology
  obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective
    ((commutator (weilSubgroup F E)).topologicalClosure) ((e E).symm a)
  refine ⟨w, ?_⟩
  change e E (QuotientGroup.mk w) = a
  exact (congrArg (e E) hw).trans ((e E).apply_symm_apply a)

/-- The supplied transfer/inclusion square identifies transferred character
values at compatible Weil lifts. -/
theorem character_transfer_reciprocity (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e)
    (E L : Extension F) (h : E.field ≤ L.field)
    (χ : weilSubgroup F L →ₜ* ℂˣ)
    (w : weilSubgroup F E) (v : weilSubgroup F L)
    (hv : reciprocityUnits F e L v =
      E.unitsInclusion L h (reciprocityUnits F e E w)) :
    (χ.toMonoidHom.comp (nestedWeilEquiv F E L h).toMonoidHom).transfer w = χ v := by
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let := (fieldData F E).topology
  let := (fieldData F L).topology
  have hs := DFunLike.congr_fun (he.1.2.1 E L h)
    (abelianizationProjection (weilSubgroup F E) w)
  have hq : E.weilAbelianTransfer L h (Weil.Local.localResidueDegree F)
      (abelianizationProjection (weilSubgroup F E) w) =
        abelianizationProjection (weilSubgroup F L) v := by
    apply (e L).injective
    exact hs.trans hv.symm
  unfold nestedWeilEquiv
  rw [LocalClassField.character_subgroupTransfer_apply
    (weilSubgroup_antitone F E L h) (weilSubgroup_open F L)]
  change abelianizationLift χ
    (E.weilAbelianTransfer L h (Weil.Local.localResidueDegree F)
      (abelianizationProjection (weilSubgroup F E) w)) = χ v
  rw [hq]
  rfl

/-- Degree-zero actual exact induction has the same determinant at compatible
Weil lifts, conditional on the genuine Gallagher formula. -/
theorem determinant_induce_degreeZero_reciprocity
    (hgal : LocalFactor.Inductive.GallagherDeterminantStatement.{0, uF, max uF uV})
    (e : ReciprocityFamily F) (he : NormalizedReciprocity F e)
    (E L : Extension F) (h : E.field ≤ L.field)
    (x : DegreeZero.{uF, uV} F L)
    (w : weilSubgroup F E) (v : weilSubgroup F L)
    (hv : reciprocityUnits F e L v =
      E.unitsInclusion L h (reciprocityUnits F e E w)) :
    ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate F E)
        (induce F E L h x.val) w =
      ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate F L) x.val v := by
  let S := (weilSubgroup F L).subgroupOf (weilSubgroup F E)
  let φ : S →ₜ* weilSubgroup F L := nestedWeilEquiv F E L h
  let P : FiniteRepresentation.{0, uF, max uF uV} ℂ S → Prop := fun A => A.IsContinuous
  have hx : ExactGrothendieckGroup.degree P
      (ExactGrothendieckGroup.continuousRestrict φ x.val) = 0 := by
    rw [ExactGrothendieckGroup.degree_continuousRestrict]
    exact x.property
  change ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate F E)
    (ExactGrothendieckGroup.induce S P _ _
      (ExactGrothendieckGroup.continuousRestrict φ x.val)) w = _
  rw [ExactGrothendieckGroup.determinantCharacter_induce_degreeZero_of_gallagher
    S P _ hgal _ _ hx]
  change ((ExactGrothendieckGroup.determinantCharacter P
    (ExactGrothendieckGroup.restrict φ.toMonoidHom _ _ _ x.val)).transfer) w = _
  rw [ExactGrothendieckGroup.determinantCharacter_restrict]
  let χ : weilSubgroup F L →ₜ* ℂˣ :=
    { toMonoidHom := ExactGrothendieckGroup.determinantCharacter
        (ContinuousPredicate F L) x.val
      continuous_toFun := ExactGrothendieckGroup.continuous_determinantCharacter
        (ContinuousPredicate F L) (fun _ hA => hA) x.val }
  exact character_transfer_reciprocity F e he E L h χ w v hv

end Langlands.LocalFactor.CommonClosure
