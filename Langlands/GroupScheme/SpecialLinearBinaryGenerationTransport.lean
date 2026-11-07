import Langlands.GroupScheme.SpecialLinearBinaryRadicalGeneration
import Langlands.GroupScheme.Rational.ParabolicWhiteheadIsomorphism

/-! # Split binary generation on specified actual models and factor images -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinear.BinaryRoot

variable {k : Type u} [Field k]
  {A G : GroupScheme (Spec (CommRingCat.of k))}

/-- Every actual model identified over the ground field with split SL₂ has full
generation by its actual rational parabolic radicals. -/
theorem parabolicElementarySubgroup_eq_top_of_iso
    (e : A ≅ SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)) :
    parabolicElementarySubgroup A = ⊤ :=
  (parabolicElementarySubgroup_eq_top_iff_iso e).mpr
    (parabolicElementarySubgroup_eq_top k)

/-- The corresponding actual parabolic Whitehead quotient is trivial. -/
theorem parabolicWhiteheadQuotient_subsingleton_of_iso
    (e : A ≅ SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)) :
    Subsingleton (parabolicWhiteheadQuotient A) :=
  (parabolicWhiteheadQuotient_subsingleton_iff A).mpr
    (parabolicElementarySubgroup_eq_top_of_iso e)

/-- Any subgroup containing all actual parabolic radical images in a specified
split binary model is the whole point group. No normality assumption is needed. -/
theorem eq_top_of_parabolic_radical_images_of_iso
    (e : A ≅ SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k))
    (N : Subgroup (rationalPoints A))
    (hN : ∀ (P U : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ A) (r : U ⟶ P),
      IsParabolicSubgroup p → LeviSubgroup.IsGeometricUnipotentRadical r →
        (rationalPoints.map (r ≫ p)).range ≤ N) : N = ⊤ := by
  apply top_unique
  rw [← parabolicElementarySubgroup_eq_top_of_iso e]
  exact (parabolicElementarySubgroup_le_iff N).mpr hN

/-- Actual rational points of an identified split binary factor lie in a
specified ambient subgroup as soon as all its parabolic radical images do. -/
theorem rationalPoints_range_le_of_iso
    (e : A ≅ SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k))
    (a : A ⟶ G) (K : Subgroup (rationalPoints G))
    (hrad : ∀ (P U : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ A) (r : U ⟶ P),
      IsParabolicSubgroup p → LeviSubgroup.IsGeometricUnipotentRadical r →
        (rationalPoints.map (r ≫ p ≫ a)).range ≤ K) :
    (rationalPoints.map a).range ≤ K := by
  have htop : K.comap (rationalPoints.map a) = ⊤ :=
    eq_top_of_parabolic_radical_images_of_iso e _ (by
      intro P U p r hp hr
      rintro _ ⟨x, rfl⟩
      change rationalPoints.map a (rationalPoints.map (r ≫ p) x) ∈ K
      simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
        using hrad P U p r hp hr ⟨x, rfl⟩)
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ K.comap (rationalPoints.map a) := by rw [htop]; trivial
  exact hx

/-- The actual rational-point map to the specified ambient subgroup, restricted
using the proved split binary generation and the listed radical containments. -/
def rationalPointsToSubgroupOfIso
    (e : A ≅ SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k))
    (a : A ⟶ G) (K : Subgroup (rationalPoints G))
    (hrad : ∀ (P U : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ A) (r : U ⟶ P),
      IsParabolicSubgroup p → LeviSubgroup.IsGeometricUnipotentRadical r →
        (rationalPoints.map (r ≫ p ≫ a)).range ≤ K) :
    rationalPoints A →* K :=
  (rationalPoints.map a).codRestrict K fun x =>
    rationalPoints_range_le_of_iso e a K hrad ⟨x, rfl⟩

@[simp] theorem rationalPointsToSubgroupOfIso_apply_coe
    (e : A ≅ SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k))
    (a : A ⟶ G) (K : Subgroup (rationalPoints G))
    (hrad : ∀ (P U : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ A) (r : U ⟶ P),
      IsParabolicSubgroup p → LeviSubgroup.IsGeometricUnipotentRadical r →
        (rationalPoints.map (r ≫ p ≫ a)).range ≤ K) (x : rationalPoints A) :
    (rationalPointsToSubgroupOfIso e a K hrad x : rationalPoints G) =
      rationalPoints.map a x := rfl

end Langlands.GroupScheme.SpecialLinear.BinaryRoot
