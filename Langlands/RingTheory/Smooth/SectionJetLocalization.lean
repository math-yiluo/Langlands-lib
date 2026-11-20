import Langlands.RingTheory.Smooth.SectionJetIsomorphismLocus
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Nilpotent.Basic

/-! # Section jets in a principal neighborhood -/

noncomputable section

universe u v

namespace Algebra.SectionJet

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (ε : A →ₐ[R] R) (a : A) (ha : IsUnit (ε a))

/-- An augmentation extends over a localization at an element whose
augmentation is a unit. -/
def awayAugmentation : Localization.Away a →ₐ[R] R :=
  IsLocalization.Away.liftAlgHom a ha

@[simp]
theorem awayAugmentation_algebraMap (x : A) :
    awayAugmentation ε a ha (algebraMap A (Localization.Away a) x) = ε x :=
  IsLocalization.Away.lift_eq a ha x

theorem awayAugmentation_comp :
    (awayAugmentation ε a ha).comp (Algebra.algHom R A (Localization.Away a)) = ε :=
  AlgHom.ext (awayAugmentation_algebraMap ε a ha)

private theorem ker_awayAugmentation :
    RingHom.ker (awayAugmentation ε a ha) =
      (RingHom.ker ε).map (algebraMap A (Localization.Away a)) := by
  rw [← IsLocalization.map_under (Submonoid.powers a) (Localization.Away a)
    (RingHom.ker (awayAugmentation ε a ha))]
  congr 1
  ext x
  change awayAugmentation ε a ha (algebraMap A (Localization.Away a) x) = 0 ↔ ε x = 0
  rw [awayAugmentation_algebraMap]

include ha in
private theorem isUnit_jet_mk (n : ℕ) :
    IsUnit (Ideal.Quotient.mk (RingHom.ker ε ^ (n + 1)) a) := by
  let q : A →+* Quotient ε n := Ideal.Quotient.mk _
  have hmem : a - algebraMap R A (ε a) ∈ RingHom.ker ε := by
    change ε (a - algebraMap R A (ε a)) = 0
    rw [map_sub, ε.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have hn : IsNilpotent (q (a - algebraMap R A (ε a))) := by
    refine ⟨n + 1, ?_⟩
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hmem _)
  have hu := ha.map (q.comp (algebraMap R A))
  change IsUnit (q a)
  change IsUnit (q (algebraMap R A (ε a))) at hu
  simpa only [← map_add, sub_add_cancel] using
    hn.isUnit_add_right_of_commute hu (Commute.all _ _)

/-- Localizing the ambient algebra in a principal neighborhood of the
entire section preserves its actual section jets. -/
def SectionJetLocalizationStatement : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    (ε : A →ₐ[R] R) (a : A) (ha : IsUnit (ε a)) (n : ℕ),
    Function.Bijective (jetMap (awayAugmentation_comp ε a ha) n)

theorem sectionJetLocalization : SectionJetLocalizationStatement.{u, v} := by
  intro R A _ _ _ ε a ha n
  let L := Localization.Away a
  let εL := awayAugmentation ε a ha
  let g := jetMap (awayAugmentation_comp ε a ha) n
  let q : A →ₐ[R] Quotient ε n := Ideal.Quotient.mkₐ R _
  let l : L →ₐ[R] Quotient ε n :=
    IsLocalization.Away.liftAlgHom a (f := q) (isUnit_jet_mk ε a ha n)
  have hl (x : A) : l (algebraMap A L x) = q x :=
    IsLocalization.Away.lift_eq a (g := q.toRingHom) (isUnit_jet_mk ε a ha n) x
  have hker : RingHom.ker εL ^ (n + 1) ≤ RingHom.ker l := by
    change RingHom.ker (awayAugmentation ε a ha) ^ (n + 1) ≤ RingHom.ker l
    rw [ker_awayAugmentation, ← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro x hx
    change l (algebraMap A L x) = 0
    rw [hl, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hx
  let inv : Quotient εL n →ₐ[R] Quotient ε n := Ideal.Quotient.liftₐ _ l hker
  have hinv (x : L) : inv (Ideal.Quotient.mk _ x) = l x := rfl
  have hleft : inv.comp g = AlgHom.id R _ := by
    apply Ideal.Quotient.algHom_ext R
    ext x
    change inv (Ideal.Quotient.mk _ (algebraMap A L x)) = q x
    rw [hinv, hl]
  have hright : g.comp inv = AlgHom.id R _ := by
    apply Ideal.Quotient.algHom_ext R
    apply IsLocalization.algHom_ext (Submonoid.powers a)
    ext x
    change g (inv (Ideal.Quotient.mk _ (algebraMap A L x))) = _
    rw [hinv, hl]
    rfl
  exact ⟨Function.LeftInverse.injective (AlgHom.congr_fun hleft),
    Function.RightInverse.surjective (AlgHom.congr_fun hright)⟩

end Algebra.SectionJet
