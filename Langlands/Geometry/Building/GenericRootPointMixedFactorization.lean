import Langlands.Geometry.Building.GenericPointSharpExchange

/-! # Two-point sharp-fixer factorization of an actual root point -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace KPApartmentData

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- An individual actual root point factors between the sharp fixers of any
two apartment points, with a normalizer point in the middle. -/
theorem exists_mixed_factorization_of_mem_rootGroup
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (x y : D.Apartment) {a : characterLattice S} (ha : a ∈ relativeRoots i)
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints i a) :
    ∃ p ∈ D.sharpFixer {x}, ∃ n : normalizerPoints i,
      ∃ q ∈ D.sharpFixer {y}, g = p * (n : rationalPoints G) * q := by
  by_cases hx : (0 : WithTop ℝ) ≤ x.val a g
  · exact ⟨g, D.filtration_le_sharpFixer x ha ⟨hg, hx⟩, 1, 1, one_mem _, by simp⟩
  by_cases hy : (0 : WithTop ℝ) ≤ y.val a g
  · exact ⟨1, one_mem _, 1, g, D.filtration_le_sharpFixer y ha ⟨hg, hy⟩, by simp⟩
  have hg1 : g ≠ 1 := by
    intro h
    subst g
    exact hx (x.isValuation.one_mem a ha 0).2
  have hT : IsSplitTorus S.toGrp := hi.1.1
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨p, hp⟩ :=
    ((rootRankOneFactorization k G hG S i hi a ha g hg hg1).1).exists
  have hna : -a ∈ relativeRoots i := by
    have hflip := hp.weylAction_eq_neg i hT ha.1 hg hg1
    exact hflip ▸ weylAction_mapsTo_relativeRoots i
      (⟨p.1 * g * p.2, hp.2.2⟩ : normalizerPoints i) ha
  obtain ⟨tx, htx⟩ := D.exists_val_eq_coe x ha hg hg1
  obtain ⟨ty, hty⟩ := D.exists_val_eq_coe y ha hg hg1
  have htxneg : tx < 0 := by
    rw [htx, ← WithTop.coe_zero, WithTop.coe_le_coe] at hx
    exact lt_of_not_ge hx
  have htyneg : ty < 0 := by
    rw [hty, ← WithTop.coe_zero, WithTop.coe_le_coe] at hy
    exact lt_of_not_ge hy
  have hp1val := x.isValuation.opposite a ha g hg hg1 p.1 hp.1 p.2 hp.2.1 hp.2.2
  rw [htx] at hp1val
  have hp2val := y.isValuation.opposite_snd ha hg hg1 hp.1 hp.2.1 hp.2.2
  rw [hty] at hp2val
  have hp1 : p.1 ∈ D.filtration x (-a) 0 := by
    refine ⟨hp.1, ?_⟩
    rw [withTop_eq_neg_of_add_eq_zero hp1val, WithTop.coe_le_coe]
    exact neg_nonneg.mpr htxneg.le
  have hp2 : p.2 ∈ D.filtration y (-a) 0 := by
    refine ⟨hp.2.1, ?_⟩
    rw [withTop_eq_neg_of_add_eq_zero hp2val, WithTop.coe_le_coe]
    exact neg_nonneg.mpr htyneg.le
  refine ⟨p.1⁻¹, inv_mem (D.filtration_le_sharpFixer x hna hp1),
    ⟨p.1 * g * p.2, hp.2.2⟩,
    p.2⁻¹, inv_mem (D.filtration_le_sharpFixer y hna hp2), ?_⟩
  change g = p.1⁻¹ * (p.1 * g * p.2) * p.2⁻¹
  group

end KPApartmentData

/-- The elementary mixed factorization, universally quantified over the actual
relative root groups and arbitrary apartment data. -/
def RootPointMixedFactorizationStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (S : CommGroupScheme (Spec (CommRingCat.of k)))
    (G : GroupScheme (Spec (CommRingCat.of k)))
    (i : S.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    (ω : kˣ → ℝ) (D : KPApartmentData i ω),
    IsConnectedReductive G → IsMaximalSplitTorus i →
    ∀ (x y : D.Apartment) (a : characterLattice S), a ∈ relativeRoots i →
    ∀ g ∈ rootGroupPoints i a,
      ∃ p ∈ D.sharpFixer {x}, ∃ n : normalizerPoints i,
        ∃ q ∈ D.sharpFixer {y}, g = p * (n : rationalPoints G) * q

/-- The elementary factorization follows from V5 and actual opposite pairs. -/
theorem rootPointMixedFactorization : RootPointMixedFactorizationStatement.{u} := by
  intro k _ S G i _ _ ω D hG hi x y a ha g hg
  exact D.exists_mixed_factorization_of_mem_rootGroup hG hi x y ha hg

end Langlands.Geometry.Building
