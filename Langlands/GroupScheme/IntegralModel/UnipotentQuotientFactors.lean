import Langlands.GroupScheme.IntegralModel.UnipotentQuotientCell
import Langlands.GroupScheme.IntegralModel.DynamicCellFactors
import Langlands.GroupScheme.IntegralModel.SpecialFibreSubgroupPoints

/-! # Integral opposite-cell factors in a unipotent quotient kernel -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable {A K : Type u} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] [IsLocalRing A]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (M : IntegralModel A K G)

/-- The generic images of integral sections killed by the actual quotient
after reduction. -/
def quotientReductionKernelPoints
    {Q : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField A)))}
    (q : M.specialFibre ⟶ Q) : Subgroup (rationalPoints G) :=
  M.specialFibreSubgroupPoints (rationalPoints.map q).ker

theorem mem_quotientReductionKernelPoints
    {Q : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField A)))}
    (q : M.specialFibre ⟶ Q) (g : rationalPoints G) :
    g ∈ M.quotientReductionKernelPoints q ↔
      ∃ x : M.integralSections,
        M.reduction x ≫ q.hom.hom = 1 ∧ M.integralPointMap x = g :=
  Iff.rfl

variable [Smooth M.group.X.hom]
    [ConnectedSpace M.specialFibre.X.left]
    (χ : (Gm (Spec (CommRingCat.of A))).toGrp ⟶ M.group)
    {U P : GroupScheme (Spec (CommRingCat.of A))}
    (i : U ⟶ M.group) (p : P ⟶ M.group)
    (hi : (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).IsRepresentedBy i)
    (hp : (Dynamic.parabolic χ).IsRepresentedBy p)
    {Q V W : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField A)))}
    [Smooth Q.X.hom] [IsAffineHom Q.X.hom] [ConnectedSpace Q.X.left]
    (q : M.specialFibre ⟶ Q)
    (hqs : Smooth q.hom.hom.left) (hqsurj : Surjective q.hom.hom.left)
    [ConnectedSpace (kernel q).X.left] (hN : IsUnipotent (kernel q))
    (j : V ⟶ Q) (r : W ⟶ Q)
    (hj : (Dynamic.unipotent (Dynamic.oppositeCocharacter
      (Dynamic.baseChangeCocharacter (residueBaseMap A) χ ≫ q))).IsRepresentedBy j)
    (hr : (Dynamic.parabolic
      (Dynamic.baseChangeCocharacter (residueBaseMap A) χ ≫ q)).IsRepresentedBy r)

include hi hp hj hr hqs hqsurj hN in
/-- A section killed by the special-fibre quotient has integral opposite-cell
factors, each still killed by that same quotient. -/
theorem exists_oppositeCell_factors_of_quotient_reduction_eq_one
    (x : M.integralSections) (hx : M.reduction x ≫ q.hom.hom = 1) :
    ∃ (a : rationalPoints U) (b : rationalPoints P),
      rationalPoints.map i a * rationalPoints.map p b = x ∧
      M.reduction (rationalPoints.map i a) ≫ q.hom.hom = 1 ∧
      M.reduction (rationalPoints.map p b) ≫ q.hom.hom = 1 := by
  have : Smooth M.specialFibre.X.hom :=
    inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd
      M.group.X.hom (residueBaseMap A)))
  have : IsAffineHom M.specialFibre.X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd
      M.group.X.hom (residueBaseMap A)))
  have : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  have hunit : lift (1 : rationalPoints V) (1 : rationalPoints W) ≫
      SubgroupFunctor.cellMultiplication j r = M.reduction x ≫ q.hom.hom := by
    rw [SubgroupFunctor.lift_cellMultiplication, MonObj.one_comp,
      MonObj.one_comp, one_mul, hx]
  obtain ⟨c, hc⟩ :=
    (M.oppositeCell_section_lifts_iff_quotient_reduction χ i p hi hp q hqs hqsurj
      hN j r hj hr x).mpr ⟨_, hunit⟩
  let a : rationalPoints U := c ≫ fst U.X P.X
  let b : rationalPoints P := c ≫ snd U.X P.X
  have hprod : rationalPoints.map i a * rationalPoints.map p b = x := by
    change (a ≫ i.hom.hom) * (b ≫ p.hom.hom) = x
    simpa only [SubgroupFunctor.cellMultiplication, MonObj.comp_mul,
      Category.assoc, a, b] using hc
  have hi₀ := hi.baseChange (residueBaseMap A)
  rw [← Dynamic.unipotent_baseChange, Dynamic.oppositeCocharacter,
    Dynamic.baseChangeCocharacter_powerHom] at hi₀
  have hp₀ := hp.baseChange (residueBaseMap A)
  rw [← Dynamic.parabolic_baseChange] at hp₀
  have ha₀ : M.reduction (rationalPoints.map i a) ∈
      (Dynamic.unipotent (Dynamic.oppositeCocharacter
        (Dynamic.baseChangeCocharacter (residueBaseMap A) χ))).carrier _ := by
    change baseChangeSectionHom (residueBaseMap A) M.group (a ≫ i.hom.hom) ∈ _
    rw [baseChangeSectionHom_naturality, Dynamic.oppositeCocharacter, ← hi₀.2]
    exact SubgroupFunctor.mem_range.mpr ⟨baseChangeSectionHom (residueBaseMap A) U a, rfl⟩
  have hb₀ : M.reduction (rationalPoints.map p b) ∈
      (Dynamic.parabolic (Dynamic.baseChangeCocharacter (residueBaseMap A) χ)).carrier _ := by
    change baseChangeSectionHom (residueBaseMap A) M.group (b ≫ p.hom.hom) ∈ _
    rw [baseChangeSectionHom_naturality, ← hp₀.2]
    exact SubgroupFunctor.mem_range.mpr ⟨baseChangeSectionHom (residueBaseMap A) P b, rfl⟩
  have haQ := Dynamic.unipotent_le_comap
    (Dynamic.oppositeCocharacter (Dynamic.baseChangeCocharacter (residueBaseMap A) χ))
    q _ ha₀
  have haQ' : M.reduction (rationalPoints.map i a) ≫ q.hom.hom ∈
      (Dynamic.unipotent (Dynamic.oppositeCocharacter
        (Dynamic.baseChangeCocharacter (residueBaseMap A) χ ≫ q))).carrier _ := by
    simpa only [SubgroupFunctor.mem_comap, Dynamic.oppositeCocharacter,
      Category.assoc] using haQ
  have hbQ := Dynamic.parabolic_le_comap
    (Dynamic.baseChangeCocharacter (residueBaseMap A) χ) q _ hb₀
  have hprodQ :
      (M.reduction (rationalPoints.map i a) ≫ q.hom.hom) *
        (M.reduction (rationalPoints.map p b) ≫ q.hom.hom) = 1 := by
    rw [← MonObj.mul_comp, ← map_mul, hprod, hx]
  have ha1 : M.reduction (rationalPoints.map i a) ≫ q.hom.hom = 1 := by
    apply Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic
      (Dynamic.baseChangeCocharacter (residueBaseMap A) χ ≫ q) haQ'
    have heq : M.reduction (rationalPoints.map i a) ≫ q.hom.hom =
        (M.reduction (rationalPoints.map p b) ≫ q.hom.hom)⁻¹ :=
      eq_inv_of_mul_eq_one_left hprodQ
    rw [heq]
    exact ((Dynamic.parabolic
      (Dynamic.baseChangeCocharacter (residueBaseMap A) χ ≫ q)).carrier _).inv_mem hbQ
  refine ⟨a, b, hprod, ha1, ?_⟩
  simpa only [ha1, one_mul] using hprodQ

include hi hp hj hr hqs hqsurj hN in
/-- The full upstairs reduction-kernel image is generated by its actual
intersections with the generic opposite unipotent and parabolic subgroups. -/
theorem quotientReductionKernelPoints_eq_sup_dynamic :
    M.quotientReductionKernelPoints q =
      (M.quotientReductionKernelPoints q ⊓
        (Dynamic.unipotent (Dynamic.oppositeCocharacter
          (Dynamic.baseChangeCocharacter (Spec.algebraMap A K) χ ≫ M.genericIso.hom))).carrier
            (Over.mk (𝟙 _))) ⊔
      (M.quotientReductionKernelPoints q ⊓
        (Dynamic.parabolic
          (Dynamic.baseChangeCocharacter (Spec.algebraMap A K) χ ≫ M.genericIso.hom)).carrier
            (Over.mk (𝟙 _))) := by
  let χK := Dynamic.baseChangeCocharacter (Spec.algebraMap A K) χ ≫ M.genericIso.hom
  have hiK := M.isRepresentedBy_generic_unipotent (Dynamic.oppositeCocharacter χ) i hi
  have hiK' : (Dynamic.unipotent (Dynamic.oppositeCocharacter χK)).IsRepresentedBy
      (M.genericHom i) := by
    simpa only [χK, Dynamic.oppositeCocharacter, Dynamic.baseChangeCocharacter_powerHom,
      Category.assoc] using hiK
  have hpK := M.isRepresentedBy_generic_parabolic χ p hp
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro g hg
  obtain ⟨x, hx, rfl⟩ := (M.mem_quotientReductionKernelPoints q g).mp hg
  obtain ⟨a, b, hab, ha, hb⟩ :=
    M.exists_oppositeCell_factors_of_quotient_reduction_eq_one
      χ i p hi hp q hqs hqsurj hN j r hj hr x hx
  have haK : M.integralPointMap (rationalPoints.map i a) ∈
      (Dynamic.unipotent (Dynamic.oppositeCocharacter χK)).carrier (Over.mk (𝟙 _)) := by
    rw [← hiK'.2]
    change M.subgroupPointMap i a ∈ _
    rw [M.subgroupPointMap_apply]
    exact SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩
  have hbK : M.integralPointMap (rationalPoints.map p b) ∈
      (Dynamic.parabolic χK).carrier (Over.mk (𝟙 _)) := by
    rw [← hpK.2]
    change M.subgroupPointMap p b ∈ _
    rw [M.subgroupPointMap_apply]
    exact SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩
  rw [← hab, map_mul]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨⟨_, ha, rfl⟩, haK⟩)
    (Subgroup.mem_sup_right ⟨⟨_, hb, rfl⟩, hbK⟩)

end Langlands.GroupScheme.IntegralModel
