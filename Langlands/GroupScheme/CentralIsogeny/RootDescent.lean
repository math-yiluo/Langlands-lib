import Langlands.GroupScheme.CentralIsogeny.WeightDivision

/-! # Termination of characteristic division of split-torus roots -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- An integral additive coordinate vanishes on a collection closed under
division by a fixed integer greater than one. -/
theorem integer_coordinate_eq_zero_of_division
    {M : Type v} [AddCommGroup M] (S : Set M) (p : ℕ) (hp : 1 < p)
    (hdiv : ∀ x ∈ S, ∃ y ∈ S, x = (p : ℤ) • y)
    (ℓ : M →+ ℤ) :
    ∀ x ∈ S, ℓ x = 0 := by
  have h : ∀ n : ℕ, ∀ x ∈ S, (ℓ x).natAbs = n → ℓ x = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx hn
      by_contra hzero
      obtain ⟨y, hy, hxy⟩ := hdiv x hx
      have hmul : ℓ x = (p : ℤ) * ℓ y := by
        simpa only [map_zsmul, zsmul_eq_mul, Int.cast_id] using congrArg ℓ hxy
      have hyzero : ℓ y ≠ 0 := by
        intro hz
        exact hzero (by rw [hmul, hz, mul_zero])
      have hpos : 0 < (ℓ y).natAbs := Int.natAbs_pos.mpr hyzero
      have habs : (ℓ x).natAbs = p * (ℓ y).natAbs := by
        rw [hmul, Int.natAbs_mul, Int.natAbs_natCast]
      have hlt : (ℓ y).natAbs < n := by
        have hm := Nat.mul_lt_mul_of_pos_right hp hpos
        simpa only [one_mul, ← habs, hn] using hm
      exact hyzero (ih _ hlt y hy rfl)
  exact fun x hx => h _ x hx rfl

/-- A collection of nonzero characters of a split torus cannot be closed
under division by a fixed integer greater than one. -/
theorem IsSplitTorus.set_eq_empty_of_character_division
    (hT : IsSplitTorus T.toGrp) (S : Set (characterLattice T))
    (p : ℕ) (hp : 1 < p) (hzero : (0 : characterLattice T) ∉ S)
    (hdiv : ∀ χ ∈ S, ∃ ψ ∈ S, χ = (p : ℤ) • ψ) : S = ∅ := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let b := (characterLattice.comapIso
    (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) e).symm.trans
      (splitTorus.characterLatticeEquiv k I)
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro χ hχ
  have hb : b χ = 0 := by
    funext j
    let ℓ : characterLattice T →+ ℤ :=
      { toFun := fun ψ => b ψ j
        map_zero' := by simp
        map_add' := by intros; simp }
    exact integer_coordinate_eq_zero_of_division S p hp hdiv ℓ χ hχ
  have hz : χ = 0 := b.injective (by simpa only [map_zero] using hb)
  exact hzero (hz ▸ hχ)

/-- In a family of affine locally finite type targets, central isogeny
steps that kill each acting torus tangent force every such root support
to be empty. The family need not be finite. -/
theorem IsSplitTorus.roots_eq_empty_of_centralIsogeny_descent
    {J : Type v} (F : J → GroupScheme (Spec (CommRingCat.of k)))
    [∀ a, IsAffineHom (F a).X.hom]
    [∀ a, LocallyOfFiniteType (F a).X.hom]
    (hT : IsSplitTorus T.toGrp) (p : ℕ) [CharP k p] (hp : 1 < p)
    (hstep : ∀ a (i : T.toGrp ⟶ F a),
      ∃ (b : J) (q : F a ⟶ F b), IsCentralIsogeny q ∧
        ∀ X : lieKernel T.toGrp k, Lie.targetMap (i ≫ q) k X = 1) :
    ∀ a (i : T.toGrp ⟶ F a), roots i = ∅ := by
  let S : Set (characterLattice T) := {χ | ∃ (a : J) (i : T.toGrp ⟶ F a), χ ∈ roots i}
  have hzero : (0 : characterLattice T) ∉ S := by
    rintro ⟨a, i, hi⟩
    exact hi.1 rfl
  have hdiv : ∀ χ ∈ S, ∃ ψ ∈ S, χ = (p : ℤ) • ψ := by
    rintro χ ⟨a, i, hχ⟩
    obtain ⟨b, q, hq, hi⟩ := hstep a i
    obtain ⟨j, ψ, hψ, hχψ, _⟩ :=
      hq.exists_divided_root q hT p (by omega) i hi hχ
    exact ⟨ψ, ⟨b, j, hψ⟩, hχψ⟩
  have hS : S = ∅ := hT.set_eq_empty_of_character_division S p hp hzero hdiv
  intro a i
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro χ hχ
  have hχS : χ ∈ S := ⟨a, i, hχ⟩
  rw [hS] at hχS
  exact hχS

/-- Universal split-root descent for arbitrary families of targets. -/
def SplitRootDivisionTerminationStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (_ : IsSplitTorus T.toGrp)
    (p : ℕ) [CharP k p], 1 < p →
    ∀ (J : Type (u + 1))
      (F : J → GroupScheme (Spec (CommRingCat.of k)))
      [∀ a, IsAffineHom (F a).X.hom]
      [∀ a, LocallyOfFiniteType (F a).X.hom],
      (∀ a (i : T.toGrp ⟶ F a),
        ∃ (b : J) (q : F a ⟶ F b), IsCentralIsogeny q ∧
          ∀ X : lieKernel T.toGrp k, Lie.targetMap (i ≫ q) k X = 1) →
        ∀ a (i : T.toGrp ⟶ F a), roots i = ∅

theorem splitRootDivisionTermination :
    SplitRootDivisionTerminationStatement.{u} := by
  intro k _ T hT p _ hp J F _ _ hstep
  exact hT.roots_eq_empty_of_centralIsogeny_descent F p hp hstep

end Langlands.GroupScheme
