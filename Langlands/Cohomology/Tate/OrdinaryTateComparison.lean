import Langlands.Cohomology.Tate.ZeroProof

noncomputable section

universe u

open CategoryTheory

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- The canonical map from ordinary to Tate cohomology in every nonnegative degree. -/
def ordinaryToTate (A : Rep.{u} R G) : (n : ℕ) →
    groupCohomology A n ⟶ tateCohomology A n
  | 0 => (groupCohomology.H0Iso A).hom ≫ ModuleCat.ofHom (zeroClass A)
  | n + 1 => ((TateCohomology.isoGroupCohomology (n + 1)).app A).inv

@[simp]
lemma ordinaryToTate_zero (A : Rep.{u} R G) :
    ordinaryToTate A 0 =
      (groupCohomology.H0Iso A).hom ≫ ModuleCat.ofHom (zeroClass A) := rfl

@[simp]
lemma ordinaryToTate_pos (A : Rep.{u} R G) (n : ℕ) [NeZero n] :
    ordinaryToTate A n = ((TateCohomology.isoGroupCohomology n).app A).inv := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

/-- The comparison sends an invariant ordinary class to its actual Tate norm-quotient class. -/
@[simp]
lemma ordinaryToTate_zero_invariant (A : Rep.{u} R G) (a : A.ρ.invariants) :
    ordinaryToTate A 0 ((groupCohomology.H0Iso A).inv a) = zeroClass A a := by
  simp

/-- Coefficient maps commute with the canonical comparison, including degree zero. -/
lemma ordinaryToTate_naturality {A B : Rep.{u} R G} (f : A ⟶ B) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) f n ≫ ordinaryToTate B n =
      ordinaryToTate A n ≫ (tateCohomologyFunctor n).map f := by
  cases n with
  | zero =>
    simp only [ordinaryToTate_zero, ← Category.assoc,
      groupCohomology.map_id_comp_H0Iso_hom]
    rw [Category.assoc, ← zeroClass_naturality_hom f, Category.assoc]
    rfl
  | succ n =>
    exact (TateCohomology.isoGroupCohomology (n + 1)).inv.naturality f

/-- The canonical ordinary-to-Tate comparison as a natural transformation in coefficients. -/
def ordinaryToTateNat (n : ℕ) :
    groupCohomology.functor R G n ⟶ tateCohomologyFunctor n where
  app A := ordinaryToTate A n
  naturality := fun _ _ f => ordinaryToTate_naturality f n

/-- Every nonnegative Tate class comes from ordinary cohomology. -/
lemma ordinaryToTate_surjective (A : Rep.{u} R G) (n : ℕ) :
    Function.Surjective (ordinaryToTate A n) := by
  cases n with
  | zero =>
    intro x
    obtain ⟨a, rfl⟩ := zeroClass_surjective A x
    exact ⟨(groupCohomology.H0Iso A).inv a, ordinaryToTate_zero_invariant A a⟩
  | succ n =>
    exact ((TateCohomology.isoGroupCohomology (n + 1)).app A).symm.toLinearEquiv.surjective

/-- The degree-zero kernel consists exactly of ordinary classes represented by actual norms. -/
lemma ordinaryToTate_zero_eq_zero_iff (A : Rep.{u} R G) (x : groupCohomology A 0) :
    ordinaryToTate A 0 x = 0 ↔ (groupCohomology.H0Iso A).hom x ∈ normImage A :=
  zeroClass_eq_zero_iff _

end Langlands.Tate
