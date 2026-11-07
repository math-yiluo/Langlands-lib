import Langlands.Cohomology.Tate.Coinduced
import Langlands.Cohomology.Tate.ZeroProof

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- The actual group norm, descended from coinvariants to invariant vectors. -/
def coinvariantNorm (A : Rep.{u} R G) :
    A.ρ.Coinvariants →ₗ[R] A.ρ.invariants :=
  Representation.Coinvariants.lift A.ρ (normToInvariants A) (by
    intro g
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    exact A.ρ.norm_self_apply g a)

@[simp] lemma coinvariantNorm_mk (A : Rep.{u} R G) (a : A) :
    coinvariantNorm A (Representation.Coinvariants.mk A.ρ a) = normToInvariants A a := rfl

/-- Vanishing in Tate degree minus one makes the norm on coinvariants injective. -/
lemma coinvariantNorm_injective (A : Rep.{u} R G)
    (h : IsZero (tateCohomology A (-1))) :
    Function.Injective (coinvariantNorm A) := by
  have he : (minusOneShortComplex A).Exact :=
    ShortComplex.exact_of_iso (minusOneShortComplexIso A)
      ((ShortComplex.exact_iff_isZero_homology _).mpr h)
  intro x y hxy
  obtain ⟨a, rfl⟩ := Representation.Coinvariants.mk_surjective A.ρ x
  obtain ⟨b, rfl⟩ := Representation.Coinvariants.mk_surjective A.ρ y
  apply (Representation.Coinvariants.mk_eq_iff A.ρ).mpr
  rw [← groupHomology.range_d₁₀_eq_coinvariantsKer A]
  have hn : A.ρ.norm (a - b) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val hxy
  exact (ShortComplex.moduleCat_exact_iff _).mp he (a - b) hn

/-- Vanishing in Tate degree zero makes the norm on coinvariants surjective. -/
lemma coinvariantNorm_surjective (A : Rep.{u} R G)
    (h : IsZero (tateCohomology A 0)) :
    Function.Surjective (coinvariantNorm A) := by
  intro a
  have hz : zeroClass A a = 0 := (ModuleCat.isZero_iff_subsingleton.mp h).elim _ _
  have ha := (zeroClass_eq_zero_iff a).mp hz
  change ∃ b, normToInvariants A b = a at ha
  obtain ⟨b, hb⟩ := ha
  exact ⟨Representation.Coinvariants.mk A.ρ b, hb⟩

/-- Only the two Tate degrees adjacent to the norm are needed for its bijectivity. -/
lemma coinvariantNorm_bijective (A : Rep.{u} R G)
    (hm : IsZero (tateCohomology A (-1))) (hz : IsZero (tateCohomology A 0)) :
    Function.Bijective (coinvariantNorm A) :=
  ⟨coinvariantNorm_injective A hm, coinvariantNorm_surjective A hz⟩

/-- The actual norm as a linear equivalence under the two Tate vanishings. -/
def coinvariantNormEquiv (A : Rep.{u} R G)
    (hm : IsZero (tateCohomology A (-1))) (hz : IsZero (tateCohomology A 0)) :
    A.ρ.Coinvariants ≃ₗ[R] A.ρ.invariants :=
  LinearEquiv.ofBijective (coinvariantNorm A) (coinvariantNorm_bijective A hm hz)

end Langlands.Tate
