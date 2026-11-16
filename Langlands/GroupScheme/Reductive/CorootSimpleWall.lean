import Langlands.GroupScheme.Reductive.LocalSplitIsomorphismAssembly
import Langlands.GroupScheme.Rational.RootSubgroupPositive

/-! # A simple-wall cocharacter and its contracted root groups -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.LocalSplitCell

variable {I J : Type u} [Fintype I] [Finite J]
  (P : RootDatum J (I → ℤ) (I → ℤ)) [P.IsReduced] (b : P.Base)

/-- A cocharacter on the wall of a simple root vanishes on that opposite
pair and has strict chamber signs on every other root. -/
theorem exists_simpleWallCocharacter
    (hpair : ∀ x y : I → ℤ, P.toLinearMap x y = coPairing x y)
    {a : J} (ha : a ∈ b.support) :
    ∃ mu : I → ℤ,
      (∀ β, coPairing (P.root β) mu = 0 ↔
        β = a ∨ β = P.reflectionPerm a a) ∧
      (∀ β, b.IsPos β → β ≠ a → 0 < coPairing (P.root β) mu) ∧
      (∀ β, ¬ b.IsPos β → β ≠ P.reflectionPerm a a →
        coPairing (P.root β) mu < 0) := by
  obtain ⟨d, hd, ν, hν⟩ := exists_coPairing_eq_height P b
  let mu : I → ℤ := fun j => 2 * ν j - d * P.coroot a j
  have hmu (β : J) :
      coPairing (P.root β) mu =
        d * (b.height β + b.height (P.reflectionPerm a β)) := by
    have hlin : coPairing (P.root β) mu =
        2 * coPairing (P.root β) ν - d * coPairing (P.root β) (P.coroot a) := by
      simp only [coPairing, mu, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hlin, hν, ← hpair, RootPairing.root_coroot_eq_pairing,
      height_reflectionPerm_of_mem P ha]
    ring
  have hzero : coPairing (P.root a) mu = 0 := by
    have hh : b.height (P.reflectionPerm a a) = -b.height a :=
      b.height_reflectionPerm_self a
    rw [hmu, hh, add_neg_cancel, mul_zero]
  have hnegative (β : J) :
      coPairing (P.root (P.reflectionPerm β β)) mu =
        -coPairing (P.root β) mu := by
    simp only [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self,
      coPairing, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  have hpos : ∀ β, b.IsPos β → β ≠ a → 0 < coPairing (P.root β) mu := by
    intro β hβ hne
    rw [hmu]
    exact mul_pos hd (add_pos hβ (hβ.reflectionPerm ha hne))
  have hneg : ∀ β, ¬ b.IsPos β → β ≠ P.reflectionPerm a a →
      coPairing (P.root β) mu < 0 := by
    intro β hβ hne
    have hβ' : b.IsPos (P.reflectionPerm β β) :=
      (RootPairing.Base.IsPos.neg_iff_not (b := b) β).mpr hβ
    have hne' : P.reflectionPerm β β ≠ a := by
      intro h
      apply hne
      apply P.root.injective
      have hh := congrArg P.root h
      simpa only [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self,
        neg_neg] using congrArg Neg.neg hh
    have hp := hpos _ hβ' hne'
    rw [hnegative] at hp
    exact neg_pos.mp hp
  refine ⟨mu, fun β => ?_, hpos, hneg⟩
  constructor
  · intro hz
    by_cases hp : b.IsPos β
    · by_cases he : β = a
      · exact Or.inl he
      · have h := hpos β hp he
        rw [hz] at h
        exact (lt_irrefl _ h).elim
    · by_cases he : β = P.reflectionPerm a a
      · exact Or.inr he
      · have h := hneg β hp he
        rw [hz] at h
        exact (lt_irrefl _ h).elim
  · rintro (rfl | rfl)
    · exact hzero
    · rw [hnegative, hzero, neg_zero]

/-- A chosen integral cocharacter in the wall of the selected simple root. -/
def simpleWallCocharacter
    (hpair : ∀ x y : I → ℤ, P.toLinearMap x y = coPairing x y)
    {a : J} (ha : a ∈ b.support) : I → ℤ :=
  (exists_simpleWallCocharacter P b hpair ha).choose

theorem simpleWallCocharacter_zero_iff
    (hpair : ∀ x y : I → ℤ, P.toLinearMap x y = coPairing x y)
    {a : J} (ha : a ∈ b.support) (β : J) :
    coPairing (P.root β) (simpleWallCocharacter P b hpair ha) = 0 ↔
      β = a ∨ β = P.reflectionPerm a a :=
  (exists_simpleWallCocharacter P b hpair ha).choose_spec.1 β

theorem simpleWallCocharacter_pos
    (hpair : ∀ x y : I → ℤ, P.toLinearMap x y = coPairing x y)
    {a : J} (ha : a ∈ b.support) {β : J} (hβ : b.IsPos β) (hne : β ≠ a) :
    0 < coPairing (P.root β) (simpleWallCocharacter P b hpair ha) :=
  (exists_simpleWallCocharacter P b hpair ha).choose_spec.2.1 β hβ hne

theorem simpleWallCocharacter_neg
    (hpair : ∀ x y : I → ℤ, P.toLinearMap x y = coPairing x y)
    {a : J} (ha : a ∈ b.support) {β : J} (hβ : ¬ b.IsPos β)
    (hne : β ≠ P.reflectionPerm a a) :
    coPairing (P.root β) (simpleWallCocharacter P b hpair ha) < 0 :=
  (exists_simpleWallCocharacter P b hpair ha).choose_spec.2.2 β hβ hne

end Langlands.GroupScheme.LocalSplitCell

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {m : I → ℤ} {v : Ga R ⟶ G}

/-- A positive coordinate pairing contracts the actual root map, over
every coefficient ring and on every relative scheme test. -/
theorem IsRootParametrization.rootPoint_mem_dynamicUnipotent
    (hv : IsRootParametrization i m v) (ν : I → ℤ) (hν : 0 < coPairing m ν)
    (Z : Over (Spec (CommRingCat.of R))) (c : Γ(Z.left, ⊤)) :
    rootPoint v Z c ∈
      (Dynamic.unipotent (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) ≫ i)).carrier Z := by
  apply RelativeRoot.subgroup_le_dynamicUnipotent_of_power i
    (splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I m)
    (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν)
    (show 0 < (coPairing m ν).toNat by omega)
  · rw [splitTorus.exponentCocharacter_comp_exponentCharacter,
      Int.toNat_of_nonneg hν.le]
    rfl
  · rw [← hv.represents.2]
    exact SubgroupFunctor.mem_range.mpr
      ⟨VectorGroup.scalarPoint (CommRingCat.of R) Z c, rfl⟩

end Langlands.GroupScheme.LocalSplitCell
