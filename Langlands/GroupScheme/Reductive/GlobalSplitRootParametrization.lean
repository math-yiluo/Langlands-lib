import Langlands.GroupScheme.Reductive.GlobalRootGroupParametrization

/-! # Actual global root parametrizations from free split root weights -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalRootGroup

open LocalSplitCell

variable {R : Type u} [CommRing R] {G : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] {I : Type u} [Fintype I]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)

/-- Every split root with a supplied free actual root weight has an actual
global root parametrization over an arbitrary commutative base. -/
theorem exists_rootParametrization_of_free_weight (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hP : IsFibrewiseRootDatumOf I G i P) (α : J)
    (hfree : Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R)) :
    ∃ v : Ga R ⟶ G, IsRootParametrization i (P.root α) v := by
  classical
  let := hG.smooth
  let : Finite J := hP.finite
  let := hP.isReduced
  obtain ⟨mu, hmu0, hmu⟩ := exists_kernel_exponent P (ULift.{u} ℚ) α
  have hex : ∃ j : I, P.root α j ≠ 0 := by
    by_contra! h
    apply P.ne_zero α
    ext j
    exact h j
  obtain ⟨j, hj⟩ := hex
  have hs : 0 < ∑ k, P.root α k * P.root α k := by
    have hle := Finset.single_le_sum
      (fun k (_ : k ∈ (Finset.univ : Finset I)) => mul_self_nonneg (P.root α k))
      (Finset.mem_univ j)
    exact lt_of_lt_of_le (mul_self_pos.mpr hj) hle
  let d : ℕ := (∑ k, P.root α k * P.root α k).toNat
  have hd : 0 < d := by dsimp [d]; omega
  have had : ∑ k, P.root α k * P.root α k = (d : ℤ) :=
    (Int.toNat_of_nonneg (le_of_lt hs)).symm
  refine exists_isRootParametrization_of_free_weight_of_fibres
    i mu (P.root α) (P.root α) hmu0 hd had (Classical.choice hfree) ?_
  intro K _ _
  have hGK := hG.isConnectedReductive_baseChange (algebraBaseMap R K)
  have hmaxK := splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hmax K
  refine exists_fibreIso i mu (P.root α) K hGK hmaxK _
    ((hP.mem_roots_iff K _).mpr ⟨α, rfl⟩) ?_ ?_ ?_
  · intro β hβ hβ0
    obtain ⟨m, rfl⟩ : ∃ m,
        splitTorus.exponentCharacter (Spec (CommRingCat.of K)) I m = β :=
      ⟨splitTorus.characterLatticeEquiv K I β, by
        rw [splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm,
          AddEquiv.symm_apply_apply]⟩
    obtain ⟨b, rfl⟩ := (hP.mem_roots_iff K m).mp hβ
    rw [splitTorus.latticePairing_exponentCharacter_exponentCocharacter] at hβ0
    rcases hmu b hβ0 with h | h
    · exact Or.inl (by rw [h])
    · refine Or.inr ?_
      rw [h, splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm,
        splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm, map_neg]
  · rw [splitTorus.latticePairing_exponentCharacter_exponentCocharacter, hmu0]
  · rw [splitTorus.latticePairing_exponentCharacter_exponentCocharacter]
    exact hs

/-- Chosen actual global parametrizations for all roots with free actual weights. -/
def rootParametrizationsOfFreeWeights (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hfree : ∀ α : J, Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R)) :
    J → (Ga R ⟶ G) :=
  fun α => (exists_rootParametrization_of_free_weight i hG hmax hP α (hfree α)).choose

/-- The chosen maps represent the actual root subgroups and are equivariant
on every scheme test. -/
theorem isRootParametrization_rootParametrizationsOfFreeWeights (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hfree : ∀ α : J, Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R))
    (α : J) :
    IsRootParametrization i (P.root α)
      (rootParametrizationsOfFreeWeights i hG hmax hP hfree α) :=
  (exists_rootParametrization_of_free_weight i hG hmax hP α (hfree α)).choose_spec

end Langlands.GroupScheme.LocalRootGroup
