import Langlands.GroupScheme.IntegralModel.GreenbergMixed.RingScheme

/-! # Elementary consequences of the Greenberg ring-scheme axioms -/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.GroupScheme.IntegralModel.GreenbergMixed.GreenbergRingScheme

variable {R : Type u} [CommRing R] [IsLocalRing R] {n : ℕ+} (ℛ : GreenbergRingScheme R n)

local notation "κ" => CommRingCat.of (IsLocalRing.ResidueField R)

/-- Points of `ℛ` are determined by their coordinates. -/
theorem ext_coord {B : CommAlgCat.{u} κ} {x y : ℛ.functor.obj B}
    (h : ∀ j, ℛ.coord B x j = ℛ.coord B y j) : x = y :=
  (ℛ.coord B).injective (funext h)

/-- Surjective coefficient maps give surjective maps of coefficient rings. -/
theorem map_surjective {B C : CommAlgCat.{u} κ} (f : B ⟶ C)
    (hf : Function.Surjective f.hom) : Function.Surjective (ℛ.functor.map f).hom := by
  intro y
  choose g hg using fun j => hf (ℛ.coord C y j)
  refine ⟨(ℛ.coord B).symm g, ℛ.ext_coord fun j => ?_⟩
  rw [ℛ.coord_map, Equiv.apply_symm_apply, hg]

/-- The reduction is natural in the coefficients. -/
theorem red_map {B C : CommAlgCat.{u} κ} (f : B ⟶ C) (x : ℛ.functor.obj B) :
    ℛ.red C ((ℛ.functor.map f).hom x) = f.hom (ℛ.red B x) := by
  obtain ⟨c, hc⟩ := ℛ.red_coord
  rw [hc, hc, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ℛ.coord_map, AlgHom.commutes]

/-- The reduction is surjective. -/
theorem red_surjective (B : CommAlgCat.{u} κ) : Function.Surjective (ℛ.red B) := by
  obtain ⟨c, hc⟩ := ℛ.red_coord
  intro b
  by_cases h : ∃ j, c j ≠ 0
  · obtain ⟨j, hj⟩ := h
    refine ⟨(ℛ.coord B).symm (Pi.single j (algebraMap (IsLocalRing.ResidueField R) B
      (c j)⁻¹ * b)), ?_⟩
    rw [hc, Finset.sum_eq_single j]
    · rw [Equiv.apply_symm_apply, Pi.single_eq_same, ← mul_assoc, ← map_mul,
        mul_inv_cancel₀ hj, map_one, one_mul]
    · intro i _ hi
      rw [Equiv.apply_symm_apply, Pi.single_eq_of_ne hi, mul_zero]
    · intro hj'
      exact absurd (Finset.mem_univ j) hj'
  · push Not at h
    have h10 : (1 : B) = 0 := by
      rw [← map_one (ℛ.red B), hc]
      simp [h]
    have : Subsingleton B := subsingleton_of_zero_eq_one h10.symm
    exact ⟨0, Subsingleton.elim _ _⟩

/-- The reduction as an `R`-algebra map, for coefficients with a compatible `R`-algebra
structure. -/
def redₐ (D : Type u) [CommRing D] [Algebra (IsLocalRing.ResidueField R) D] [Algebra R D]
    [IsScalarTower R (IsLocalRing.ResidueField R) D] :
    ℛ.functor.obj (CommAlgCat.of κ D) →ₐ[R] D where
  __ := ℛ.red (CommAlgCat.of κ D)
  commutes' r := by
    change ℛ.red (CommAlgCat.of κ D) (algebraMap R _ r) = _
    rw [ℛ.red_algebraMap, IsScalarTower.algebraMap_apply R (IsLocalRing.ResidueField R) D,
      IsLocalRing.ResidueField.algebraMap_eq]

@[simp] theorem redₐ_apply (D : Type u) [CommRing D] [Algebra (IsLocalRing.ResidueField R) D]
    [Algebra R D] [IsScalarTower R (IsLocalRing.ResidueField R) D]
    (x : ℛ.functor.obj (CommAlgCat.of κ D)) :
    ℛ.redₐ D x = ℛ.red (CommAlgCat.of κ D) x := rfl

end Langlands.GroupScheme.IntegralModel.GreenbergMixed.GreenbergRingScheme
