import Langlands.AlgebraicGeometry.Picard.NonzeroPullbackPowerSection
import Langlands.AlgebraicGeometry.Picard.MixedEulerSectionSupport
import Langlands.AlgebraicGeometry.Picard.MixedEulerCoefficientScaling

/-! # Positive mixed Euler coefficients of nonzero homomorphism pullbacks -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable {k : Type u} [Field k]
    {A B : AbelianScheme (Spec (CommRingCat.of k))}

private theorem hom_eq_zero_of_range_subset_targetUnitSection (f : A ⟶ B)
    (hf : Set.range (hom f) ⊆ Set.range (unitSection B)) : f = 0 := by
  let : IsIntegral A.X.left := field_isIntegral A
  have h := ComponentConstancy.eq_comp_of_range_subset_range B.X.hom
    (unitSection B) (unitSection_comp B) (hom f) hf
  have hw : hom f ≫ B.X.hom = A.X.hom := (groupHom f).hom.hom.w
  rw [hw] at h
  have hzero : hom (0 : A ⟶ B) = A.X.hom ≫ unitSection B := by
    let p : A.X ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))) :=
      Over.homMk A.X.hom (by simp)
    exact congrArg (fun q : A.X ⟶ B.X => q.left)
      (MonObj.comp_one p).symm
  apply Additive.toMul.injective
  apply Grp.hom_ext
  exact Over.OverMorphism.ext (h.trans hzero.symm)

private theorem nonzero_hom_pullback_power_section
    (LB : LineBundle B.X.left) (hLB : LB.IsAmple) (f : A ⟶ B) (hf : f ≠ 0) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ s : ((LineBundle.pullback (hom f)).obj LB).powSections n,
      ((((LineBundle.pullback (hom f)).obj LB).sectionOpen s : Set A.X.left).Nonempty) ∧
        ∃ x : A.X.left, x ∉ ((LineBundle.pullback (hom f)).obj LB).sectionOpen s := by
  have hout : ∃ x : A.X.left, hom f x ∉ Set.range (unitSection B) := by
    by_contra h
    push Not at h
    apply hf
    apply hom_eq_zero_of_range_subset_targetUnitSection f
    rintro _ ⟨x, rfl⟩
    exact h x
  obtain ⟨x, hx⟩ := hout
  have hclosed : IsClosed (Set.range (unitSection B)) := by
    let : IsClosedImmersion (unitSection B) :=
      isClosedImmersion_of_comp_eq_id B.X.hom (unitSection B) (unitSection_comp B)
    exact (unitSection B).isClosedEmbedding.isClosed_range
  let W : B.X.left.Opens := ⟨(Set.range (unitSection B))ᶜ, hclosed.isOpen_compl⟩
  obtain ⟨n, hn, s, hs, hsW⟩ := ampleSectionOpenBasis_apply B.X.left LB hLB W (hom f x) hx
  refine ⟨n, hn, LB.pullbackPowSection (hom f) s, ?_, ?_⟩
  · rw [LineBundle.sectionOpen_pullbackPowSection]
    exact ⟨x, hs⟩
  · let z := IsLocalRing.closedPoint k
    refine ⟨unitSection A z, ?_⟩
    rw [LineBundle.sectionOpen_pullbackPowSection]
    intro he
    have heW := hsW he
    change hom f (unitSection A z) ∉ Set.range (unitSection B) at heW
    apply heW
    refine ⟨z, ?_⟩
    exact (congrArg (fun q => q z) (unitSection_hom f)).symm

/-- Against an ample source bundle, the pullback of an ample target bundle by
an actual nonzero homomorphism has positive mixed Euler coefficient. -/
theorem mixedLineBundleEulerCoefficient_pullback_pos_of_ne_zero
    (g : ℕ) (hg : 0 < g) (hA : A.HasRelativeDimension g)
    (LA : LineBundle A.X.left) (hLA : LA.IsAmple)
    (LB : LineBundle B.X.left) (hLB : LB.IsAmple) (f : A ⟶ B) (hf : f ≠ 0) :
    0 < mixedLineBundleEulerCoefficient A.X.hom LA
      ((LineBundle.pullback (hom f)).obj LB) g := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hg)
  let : IsIntegral A.X.left := field_isIntegral A
  let : IsNoetherian A.X.left := field_isNoetherian A
  let : A.X.left.IsSeparated := field_isSeparated A
  obtain ⟨n, hn, s, hs, hz⟩ := nonzero_hom_pullback_power_section LB hLB f hf
  let N := (LineBundle.pullback (hom f)).obj LB
  let Nn : LineBundle A.X.left :=
    ⟨tensorPow N.obj n, tensorPow_isLocallyFreeRankOne A.X.left N n⟩
  have hp := mixedLineBundleEulerCoefficient_pos_of_section A.X.hom d hA
    inferInstance LA Nn hLA s hs hz
  have hdim : topologicalKrullDim A.X.left ≤ d + 1 := by
    rw [field_topologicalKrullDim hA]
    exact le_rfl
  rw [mixedLineBundleEulerCoefficient_tensorPow A.X.hom LA N d hdim n] at hp
  exact pos_of_mul_pos_right hp (Nat.cast_nonneg n)

end Langlands.AbelianScheme
