import Langlands.AlgebraicGeometry.Picard.AmpleSectionOpenBasisProof
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof
import Langlands.AlgebraicGeometry.Picard.FieldPicardZeroComponentConstancyProof
import Langlands.AlgebraicGeometry.Picard.HomFamilyPullback
import Langlands.AbelianScheme.FieldAbelianSchemeGeometry

/-! # Power sections of nonzero endomorphism pullbacks -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {k : Type u} [Field k]
    (A : AbelianScheme (Spec (CommRingCat.of k)))

/-- A power of the actual pullback has a section with both a frame and a nonframe point. -/
def NonzeroPullbackPowerSection (L : LineBundle A.X.left) (f : A ⟶ A) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ ∃ s : ((LineBundle.pullback (hom f)).obj L).powSections n,
    ((((LineBundle.pullback (hom f)).obj L).sectionOpen s : Set A.X.left).Nonempty) ∧
      ∃ x : A.X.left, x ∉ ((LineBundle.pullback (hom f)).obj L).sectionOpen s

/-- A homomorphism with image in the unit section is zero over a field. -/
theorem eq_zero_of_range_subset_unitSection (f : A ⟶ A)
    (hf : Set.range (hom f) ⊆ Set.range (unitSection A)) : f = 0 := by
  let : IsIntegral A.X.left := field_isIntegral A
  have h := ComponentConstancy.eq_comp_of_range_subset_range A.X.hom
    (unitSection A) (unitSection_comp A) (hom f) hf
  have hw : hom f ≫ A.X.hom = A.X.hom := (groupHom f).hom.hom.w
  rw [hw] at h
  have hzero : hom (0 : A ⟶ A) = A.X.hom ≫ unitSection A := by
    let p : A.X ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))) :=
      Over.homMk A.X.hom (by simp)
    exact congrArg (fun q : A.X ⟶ A.X => q.left)
      (MonObj.comp_one p).symm
  apply Additive.toMul.injective
  apply Grp.hom_ext
  exact Over.OverMorphism.ext (h.trans hzero.symm)

/-- An ample bundle and an actual nonzero endomorphism give such a power section. -/
theorem nonzeroPullbackPowerSection (L : LineBundle A.X.left) (hL : L.IsAmple)
    (f : A ⟶ A) (hf : f ≠ 0) : NonzeroPullbackPowerSection A L f := by
  have hout : ∃ x : A.X.left, hom f x ∉ Set.range (unitSection A) := by
    by_contra h
    push Not at h
    apply hf
    apply eq_zero_of_range_subset_unitSection A f
    rintro _ ⟨x, rfl⟩
    exact h x
  obtain ⟨x, hx⟩ := hout
  have hclosed : IsClosed (Set.range (unitSection A)) := by
    let : IsClosedImmersion (unitSection A) :=
      isClosedImmersion_of_comp_eq_id A.X.hom (unitSection A) (unitSection_comp A)
    exact (unitSection A).isClosedEmbedding.isClosed_range
  let W : A.X.left.Opens := ⟨(Set.range (unitSection A))ᶜ, hclosed.isOpen_compl⟩
  obtain ⟨n, hn, s, hs, hsW⟩ := ampleSectionOpenBasis_apply A.X.left L hL W (hom f x) hx
  refine ⟨n, hn, L.pullbackPowSection (hom f) s, ?_, ?_⟩
  · rw [LineBundle.sectionOpen_pullbackPowSection]
    exact ⟨x, hs⟩
  · let z := IsLocalRing.closedPoint k
    refine ⟨unitSection A z, ?_⟩
    rw [LineBundle.sectionOpen_pullbackPowSection]
    intro he
    have heW := hsW he
    change hom f (unitSection A z) ∉ Set.range (unitSection A) at heW
    apply heW
    refine ⟨z, ?_⟩
    exact (congrArg (fun q => q z) (unitSection_hom f)).symm

end Langlands.AbelianScheme
