import Langlands.Representation.Plancherel.DynamicCommonLeviOrderedRadicals
import Langlands.Representation.Plancherel.DynamicCommonLeviPresentationComparison

/-! # Multiplication of the opposite complements in a distance-additive triple -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.DynamicCommonLeviComposition

open DynamicOppositeStandardIntertwining StandardIntertwining
open DynamicCommonLeviPresentationComparison

/-- Change the subgroup names in a literal multiplication homeomorphism. -/
def subgroupProductChartOfEq {H : Type*} [Group H] [TopologicalSpace H]
    {V W C V' W' C' : Subgroup H} (hV : V' = V) (hW : W' = W) (hC : C' = C)
    (e : V × W ≃ₜ C) (he : ∀ x : V × W, (e x : H) = x.1.val * x.2.val) :
    {e' : V' × W' ≃ₜ C' // ∀ x : V' × W', (e' x : H) = x.1.val * x.2.val} :=
  let left := subgroupHomeomorphOfEq hV
  let right := subgroupHomeomorphOfEq hW
  let out := subgroupHomeomorphOfEq hC.symm
  ⟨(left.toHomeomorph.prodCongr right.toHomeomorph).trans (e.trans out.toHomeomorph),
    fun x => (subgroupHomeomorphOfEq_coe hC.symm (e (left x.1, right x.2))).trans
      ((he (left x.1, right x.2)).trans (congrArg₂ (· * ·)
        (subgroupHomeomorphOfEq_coe hV x.1) (subgroupHomeomorphOfEq_coe hW x.2)))⟩

section Ordered

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {A B C D V W : Subgroup H} (f : OrderedSubgroupFactorization A B C V W)
  (hAD : A ⊓ D = ⊥) (hV : V ≤ D) (hW : W ≤ D)

omit [IsTopologicalGroup H] in
private theorem composite_coe (x : A.subgroupOf C × (V × W)) :
    (f.composite x : H) = x.1.val.val * (x.2.1.val * x.2.2.val) :=
  congrArg Subtype.val (f.composite_eq x)

private def orderedComplementChart : V × W ≃ₜ (D ⊓ C : Subgroup H) where
  toFun x := ⟨x.1.val * x.2.val,
    ⟨D.mul_mem (hV x.1.property) (hW x.2.property),
      C.mul_mem (f.first_le_target x.1.property) (f.second_le x.2.property)⟩⟩
  invFun y := (f.composite.symm ⟨y.val, y.property.2⟩).2
  left_inv x := by
    have hx : f.composite (1, x) = ⟨x.1.val * x.2.val,
        C.mul_mem (f.first_le_target x.1.property) (f.second_le x.2.property)⟩ :=
      Subtype.ext ((composite_coe f (1, x)).trans (one_mul _))
    exact congrArg Prod.snd ((congrArg f.composite.symm hx.symm).trans
      (f.composite.symm_apply_apply (1, x)))
  right_inv y := by
    let x := f.composite.symm (⟨y.val, y.property.2⟩ : C)
    have hx : y.val = x.1.val.val * (x.2.1.val * x.2.2.val) :=
      (congrArg Subtype.val (f.composite.apply_symm_apply ⟨y.val, y.property.2⟩)).symm.trans
        (composite_coe f x)
    have ht : x.2.1.val * x.2.2.val ∈ D :=
      D.mul_mem (hV x.2.1.property) (hW x.2.2.property)
    have ha : x.1.val.val ∈ A ⊓ D :=
      ⟨x.1.property, (D.mul_mem_cancel_right ht).mp (hx ▸ y.property.1)⟩
    have h1 : x.1.val.val = 1 := by rwa [hAD, Subgroup.mem_bot] at ha
    apply Subtype.ext
    exact ((one_mul _).symm.trans ((congrArg (fun s : H => s * _) h1.symm).trans hx.symm))
  continuous_toFun := ((continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  continuous_invFun := continuous_snd.comp
    (f.composite.symm.continuous.comp (continuous_subtype_val.subtype_mk _))

end Ordered

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
  (ψ₀ ψ₁ ψ₂ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (h₁ : Dynamic.centralizer ψ₁ = Dynamic.centralizer ψ₀)
  (h₂ : Dynamic.centralizer ψ₂ = Dynamic.centralizer ψ₀)
  (hd : IsDistanceAdditive ψ₀ ψ₁ ψ₂)

include h₁ h₂ hd in
/-- The second complement lies in the first opposite radical. -/
theorem secondComplement_le_firstOpposite :
    radical ψ₂ ⊓ oppositeRadical ψ₁ ≤ oppositeRadical ψ₀ := by
  have hd' : IsDistanceAdditive (Dynamic.inverseCocharacter ψ₂)
      (Dynamic.inverseCocharacter ψ₁) (Dynamic.inverseCocharacter ψ₀) := by
    constructor
    · change oppositeRadical ψ₂ ⊓ oppositeRadical ψ₀ ≤ oppositeRadical ψ₁
      simpa only [inf_comm] using hd.2
    · simpa only [oppositeRadical, Dynamic.inverseCocharacter_inverseCocharacter, inf_comm]
        using hd.1
  have h₁' := (centralizer_inverseCocharacter_eq ψ₀ ψ₁ h₁).trans
    (centralizer_inverseCocharacter_eq ψ₀ ψ₂ h₂).symm
  have h₀' := (Dynamic.centralizer_inverseCocharacter ψ₀).trans
    (centralizer_inverseCocharacter_eq ψ₀ ψ₂ h₂).symm
  have h := firstComplement_le_target _ _ _ h₁' h₀' hd'
  simpa only [oppositeRadical, Dynamic.inverseCocharacter_inverseCocharacter, inf_comm]
    using h

private def oppositeComplementProductData :=
  subgroupProductChartOfEq (inf_comm (oppositeRadical ψ₀) (radical ψ₁))
    (inf_comm (oppositeRadical ψ₁) (radical ψ₂))
    (rfl : oppositeRadical ψ₀ ⊓ radical ψ₂ = oppositeRadical ψ₀ ⊓ radical ψ₂)
    (orderedComplementChart (distanceAdditiveRadicalFactorizationData ψ₀ ψ₁ ψ₂ h₁ h₂ hd)
      (radical_inf_oppositeRadical ψ₀) inf_le_right
      (secondComplement_le_firstOpposite ψ₀ ψ₁ ψ₂ h₁ h₂ hd)) (fun _ => rfl)

/-- Multiplication identifies the first and second opposite complements with
the direct opposite complement in the order used by integral composition. -/
def oppositeComplementProduct :
    (oppositeRadical ψ₀ ⊓ radical ψ₁ : Subgroup (rationalPoints G)) ×
      (oppositeRadical ψ₁ ⊓ radical ψ₂ : Subgroup (rationalPoints G)) ≃ₜ
      (oppositeRadical ψ₀ ⊓ radical ψ₂ : Subgroup (rationalPoints G)) :=
  (oppositeComplementProductData ψ₀ ψ₁ ψ₂ h₁ h₂ hd).val

/-- The complement chart is literally multiplication of the two factors. -/
theorem oppositeComplementProduct_apply
    (x : (oppositeRadical ψ₀ ⊓ radical ψ₁ : Subgroup (rationalPoints G)) ×
      (oppositeRadical ψ₁ ⊓ radical ψ₂ : Subgroup (rationalPoints G))) :
    (oppositeComplementProduct ψ₀ ψ₁ ψ₂ h₁ h₂ hd x : rationalPoints G) =
      x.1.val * x.2.val :=
  (oppositeComplementProductData ψ₀ ψ₁ ψ₂ h₁ h₂ hd).property x

end Langlands.Plancherel.DynamicCommonLeviComposition
