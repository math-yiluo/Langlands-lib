import Langlands.GroupScheme.IntegralModel.UnipotentQuotientFactors
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientProof
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.Dynamic.NestedDecomposition

/-! # Actual integral factors in a represented radical preimage -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

/-- Changing the base of a section preserves membership in any subgroup
functor after the same base change. -/
private theorem baseChangeSectionHom_mem {S S' : Scheme.{u}} (b : S' ⟶ S)
    {G : GroupScheme S} (D : SubgroupFunctor G)
    {x : Over.mk (𝟙 S) ⟶ G.X} (hx : x ∈ D.carrier _) :
    baseChangeSectionHom b G x ∈ (D.baseChange b).carrier (Over.mk (𝟙 S')) := by
  rw [mem_baseChange]
  have h := D.comp_mem (Over.homMk b (by simp) :
    (Over.map b).obj (Over.mk (𝟙 S')) ⟶ Over.mk (𝟙 S)) hx
  convert h using 1
  apply Over.OverMorphism.ext
  exact baseChangeSectionHom_fst b G x

end Langlands.GroupScheme.SubgroupFunctor

namespace Langlands.GroupScheme.IntegralModel

variable {A K : Type u} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] [IsLocalRing A]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (M : IntegralModel A K G) [Smooth M.group.X.hom]
    [ConnectedSpace M.specialFibre.X.left]
    (χ : (Gm (Spec (CommRingCat.of A))).toGrp ⟶ M.group)
    {R : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField A)))}
    (iR : R ⟶ M.specialFibre) (hR : IsUnipotentRadical iR)

include hR in
/-- Integral opposite dynamic factors of an actual radical-preimage section,
each reducing into that same represented radical. -/
theorem exists_radical_opposite_factors (x : M.integralSections)
    (hx : M.reduction x ∈ (rationalPoints.map iR).range) :
    ∃ a b : M.integralSections,
      a * b = x ∧
      a ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).carrier (Over.mk (𝟙 _)) ∧
      b ∈ (Dynamic.parabolic χ).carrier (Over.mk (𝟙 _)) ∧
      M.reduction a ∈ (rationalPoints.map iR).range ∧
      M.reduction b ∈ (rationalPoints.map iR).range := by
  have : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom
  have : Smooth M.specialFibre.X.hom :=
    inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd
      M.group.X.hom (residueBaseMap A)))
  have : IsAffineHom M.specialFibre.X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd
      M.group.X.hom (residueBaseMap A)))
  obtain ⟨Q, q, hq, hQ⟩ :=
    unipotentRadicalQuotient (IsLocalRing.ResidueField A) M.specialFibre R iR hR
  have : Smooth Q.X.hom := hQ.smooth
  have : IsAffineHom Q.X.hom := hQ.isAffineHom
  have : ConnectedSpace Q.X.left := hQ.connectedSpace
  have : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  have : IsClosedImmersion iR.hom.hom.left := hR.isClosedSubgroup
  have : Mono iR.hom.hom := Over.mono_of_mono_left _
  have : ConnectedSpace R.X.left := hR.connectedSpace
  have : ConnectedSpace (kernel q).X.left :=
    KernelRepresentative.connectedSpace q iR hq.2.2.2
  have hN : IsUnipotent (kernel q) :=
    KernelRepresentative.isUnipotent q iR hq.2.2.2 hR.isUnipotent
  have : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : QuasiCompact q.hom.hom.left :=
    QuasiCompact.of_comp q.hom.hom.left Q.X.hom
  have hqs : Smooth q.hom.hom.left :=
    hq.smooth_of_smooth_kernel ⟨inferInstance, rfl⟩ hR.smooth
  have hpoint (y : rationalPoints M.specialFibre) :
      y ∈ (rationalPoints.map iR).range ↔ y ≫ q.hom.hom = 1 := by
    change y ∈ (SubgroupFunctor.range iR).carrier _ ↔ _
    rw [← hq.2.2.2, mem_range_kernelι_iff]
  let ψ := Dynamic.baseChangeCocharacter (residueBaseMap A) χ ≫ q
  obtain ⟨a, b, hab, ha, hb⟩ :=
    M.exists_oppositeCell_factors_of_quotient_reduction_eq_one χ
      (Dynamic.Affine.unipotentHom (Dynamic.oppositeCocharacter χ))
      (Dynamic.Affine.parabolicHom χ)
      (Dynamic.Affine.isRepresentedBy_unipotentHom _)
      (Dynamic.Affine.isRepresentedBy_parabolicHom _) q hqs hq.2.1 hN
      (Dynamic.Affine.unipotentHom (Dynamic.oppositeCocharacter ψ))
      (Dynamic.Affine.parabolicHom ψ)
      (Dynamic.Affine.isRepresentedBy_unipotentHom _)
      (Dynamic.Affine.isRepresentedBy_parabolicHom _) x ((hpoint (M.reduction x)).mp hx)
  refine ⟨rationalPoints.map (Dynamic.Affine.unipotentHom (Dynamic.oppositeCocharacter χ)) a,
    rationalPoints.map (Dynamic.Affine.parabolicHom χ) b, hab, ?_, ?_,
    (hpoint _).mpr ha, (hpoint _).mpr hb⟩
  · rw [← (Dynamic.Affine.isRepresentedBy_unipotentHom
      (Dynamic.oppositeCocharacter χ)).2]
    exact SubgroupFunctor.mem_range.mpr ⟨a, rfl⟩
  · rw [← (Dynamic.Affine.isRepresentedBy_parabolicHom χ).2]
    exact SubgroupFunctor.mem_range.mpr ⟨b, rfl⟩

omit [Smooth M.group.X.hom] [ConnectedSpace M.specialFibre.X.left] in
/-- Splitting an integral parabolic section into its centralizer and
unipotent factors preserves any separated quotient reduction kernel. -/
theorem exists_centralizer_unipotent_factors_of_quotient_reduction_eq_one
    {Q : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField A)))}
    [IsSeparated Q.X.hom] (q : M.specialFibre ⟶ Q)
    (x : M.integralSections)
    (hx : M.reduction x ≫ q.hom.hom = 1)
    (hp : x ∈ (Dynamic.parabolic χ).carrier (Over.mk (𝟙 _))) :
    ∃ c d : M.integralSections,
      c * d = x ∧
      c ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) ∧
      d ∈ (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) ∧
      M.reduction c ≫ q.hom.hom = 1 ∧
      M.reduction d ≫ q.hom.hom = 1 := by
  obtain ⟨c, hc, d, hd, hcd⟩ := Dynamic.exists_centralizer_mul_unipotent χ hp
  have hc₀ : M.reduction c ∈
      (Dynamic.centralizer (Dynamic.baseChangeCocharacter (residueBaseMap A) χ)).carrier _ := by
    rw [Dynamic.centralizer_baseChange]
    exact (Dynamic.centralizer χ).baseChangeSectionHom_mem (residueBaseMap A) hc
  have hd₀ : M.reduction d ∈
      (Dynamic.unipotent (Dynamic.baseChangeCocharacter (residueBaseMap A) χ)).carrier _ := by
    rw [Dynamic.unipotent_baseChange]
    exact (Dynamic.unipotent χ).baseChangeSectionHom_mem (residueBaseMap A) hd
  let ψ := Dynamic.baseChangeCocharacter (residueBaseMap A) χ ≫ q
  have hcQ : M.reduction c ≫ q.hom.hom ∈
      (Dynamic.centralizer ψ).carrier _ :=
    Dynamic.centralizer_le_comap
      (Dynamic.baseChangeCocharacter (residueBaseMap A) χ) q _ hc₀
  have hdQ : M.reduction d ≫ q.hom.hom ∈
      (Dynamic.unipotent ψ).carrier _ :=
    Dynamic.unipotent_le_comap
      (Dynamic.baseChangeCocharacter (residueBaseMap A) χ) q _ hd₀
  have hprod : (M.reduction c ≫ q.hom.hom) * (M.reduction d ≫ q.hom.hom) = 1 := by
    rw [← MonObj.mul_comp, ← map_mul, hcd, hx]
  have hc1 : M.reduction c ≫ q.hom.hom = 1 := by
    apply Dynamic.eq_one_of_mem_centralizer_of_mem_unipotent ψ
      (fun _ _ _ _ ha hb => ha.unique ψ hb) hcQ
    rw [eq_inv_of_mul_eq_one_left hprod]
    exact ((Dynamic.unipotent ψ).carrier _).inv_mem hdQ
  exact ⟨c, d, hcd, hc, hd, hc1, by simpa only [hc1, one_mul] using hprod⟩

include hR in
/-- Every integral section reducing into a represented radical admits three
actual integral dynamic factors, each reducing into that same radical. -/
theorem exists_radical_triple_factors (x : M.integralSections)
    (hx : M.reduction x ∈ (rationalPoints.map iR).range) :
    ∃ a c d : M.integralSections,
      a * c * d = x ∧
      a ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).carrier (Over.mk (𝟙 _)) ∧
      c ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) ∧
      d ∈ (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) ∧
      M.reduction a ∈ (rationalPoints.map iR).range ∧
      M.reduction c ∈ (rationalPoints.map iR).range ∧
      M.reduction d ∈ (rationalPoints.map iR).range := by
  obtain ⟨a, b, hab, ha, hb, haR, hbR⟩ := M.exists_radical_opposite_factors χ iR hR x hx
  have : Smooth M.specialFibre.X.hom :=
    inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd
      M.group.X.hom (residueBaseMap A)))
  have : IsAffineHom M.specialFibre.X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd
      M.group.X.hom (residueBaseMap A)))
  obtain ⟨Q, q, hq, hQ⟩ :=
    unipotentRadicalQuotient (IsLocalRing.ResidueField A) M.specialFibre R iR hR
  have : IsAffineHom Q.X.hom := hQ.isAffineHom
  have hpoint (y : rationalPoints M.specialFibre) :
      y ∈ (rationalPoints.map iR).range ↔ y ≫ q.hom.hom = 1 := by
    change y ∈ (SubgroupFunctor.range iR).carrier _ ↔ _
    rw [← hq.2.2.2, mem_range_kernelι_iff]
  obtain ⟨c, d, hcd, hc, hd, hcR, hdR⟩ :=
    M.exists_centralizer_unipotent_factors_of_quotient_reduction_eq_one
      χ q b ((hpoint _).mp hbR) hb
  exact ⟨a, c, d, by rw [mul_assoc, hcd, hab], ha, hc, hd,
    haR, (hpoint _).mpr hcR, (hpoint _).mpr hdR⟩

/-- The full generic radical preimage is generated by its three intersections
with the generic opposite-unipotent, centralizer and unipotent subgroups. -/
def RadicalDynamicGeneration : Prop :=
  let B := M.specialFibreSubgroupPoints (rationalPoints.map iR).range
  let χK := Dynamic.baseChangeCocharacter (Spec.algebraMap A K) χ ≫ M.genericIso.hom
  B = (B ⊓ (Dynamic.unipotent (Dynamic.oppositeCocharacter χK)).carrier (Over.mk (𝟙 _))) ⊔
      (B ⊓ (Dynamic.centralizer χK).carrier (Over.mk (𝟙 _))) ⊔
      (B ⊓ (Dynamic.unipotent χK).carrier (Over.mk (𝟙 _)))

include hR in
/-- The radical dynamic-generation assertion follows from the integral
factorization, retaining the actual reduction and generic section maps. -/
theorem radicalDynamicGeneration : M.RadicalDynamicGeneration χ iR := by
  let B := M.specialFibreSubgroupPoints (rationalPoints.map iR).range
  let χK := Dynamic.baseChangeCocharacter (Spec.algebraMap A K) χ ≫ M.genericIso.hom
  change B = _ ⊔ _ ⊔ _
  refine le_antisymm ?_ (sup_le (sup_le inf_le_left inf_le_left) inf_le_left)
  intro g hg
  obtain ⟨x, hx, rfl⟩ := (M.mem_specialFibreSubgroupPoints _ g).mp hg
  obtain ⟨a, c, d, hacd, ha, hc, hd, haR, hcR, hdR⟩ :=
    M.exists_radical_triple_factors χ iR hR x hx
  have haK : M.integralPointMap a ∈
      (Dynamic.unipotent (Dynamic.oppositeCocharacter χK)).carrier (Over.mk (𝟙 _)) := by
    change (baseChangeSectionHom (Spec.algebraMap A K) M.group a ≫
      M.genericIso.hom.hom.hom) ∈ _
    have h := (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).baseChangeSectionHom_mem
      (Spec.algebraMap A K) ha
    have h' : baseChangeSectionHom (Spec.algebraMap A K) M.group a ∈
        (Dynamic.unipotent (Dynamic.oppositeCocharacter
          (Dynamic.baseChangeCocharacter (Spec.algebraMap A K) χ))).carrier _ := by
      simpa only [← Dynamic.unipotent_baseChange, Dynamic.oppositeCocharacter,
        Dynamic.baseChangeCocharacter_powerHom] using h
    simpa only [SubgroupFunctor.mem_comap, χK, Dynamic.oppositeCocharacter,
      Category.assoc] using
      Dynamic.unipotent_le_comap
        (Dynamic.oppositeCocharacter (Dynamic.baseChangeCocharacter (Spec.algebraMap A K) χ))
        M.genericIso.hom _ h'
  have hcK : M.integralPointMap c ∈
      (Dynamic.centralizer χK).carrier (Over.mk (𝟙 _)) := by
    have h := (Dynamic.centralizer χ).baseChangeSectionHom_mem (Spec.algebraMap A K) hc
    rw [← Dynamic.centralizer_baseChange] at h
    exact Dynamic.centralizer_le_comap
      (Dynamic.baseChangeCocharacter (Spec.algebraMap A K) χ) M.genericIso.hom _ h
  have hdK : M.integralPointMap d ∈
      (Dynamic.unipotent χK).carrier (Over.mk (𝟙 _)) := by
    have h := (Dynamic.unipotent χ).baseChangeSectionHom_mem (Spec.algebraMap A K) hd
    rw [← Dynamic.unipotent_baseChange] at h
    exact Dynamic.unipotent_le_comap
      (Dynamic.baseChangeCocharacter (Spec.algebraMap A K) χ) M.genericIso.hom _ h
  rw [← hacd, map_mul, map_mul]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left (Subgroup.mul_mem _
      (Subgroup.mem_sup_left ⟨⟨a, haR, rfl⟩, haK⟩)
      (Subgroup.mem_sup_right ⟨⟨c, hcR, rfl⟩, hcK⟩)))
    (Subgroup.mem_sup_right ⟨⟨d, hdR, rfl⟩, hdK⟩)

end Langlands.GroupScheme.IntegralModel
