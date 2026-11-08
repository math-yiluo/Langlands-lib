import Langlands.Geometry.Building.SelectedRootDepthCollection
import Langlands.GroupScheme.Rational.SelectedRootCoordinateRestriction
import Langlands.GroupScheme.Rational.SemigroupIntersection
import Langlands.GroupScheme.Rational.SemigroupTriviality

/-! # Exact intersections for selected filtered root products -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- On a root ray, a semigroup that omits the first character keeps at most
the actual doubled root functor. -/
theorem subgroup_inf_semigroup_le_double_of_not_mem
    (hT : IsSplitTorus T.toGrp) (hE : HasOppositeFactorPairs i)
    {a : characterLattice T} (ha : a ≠ 0)
    (B : AddSubsemigroup (characterLattice T)) (hnot : a ∉ B) :
    subgroup i a ⊓ semigroupSubgroup (AutomorphicAction.conjugation i) B ≤
      subgroup i (2 • a) := by
  have h2a : 2 • a ≠ 0 := hT.nsmul_ne_zero ha (by omega)
  rw [← weightFiltration_one_eq_subgroup hT i a ha,
    ← weightFiltration_one_eq_subgroup hT i (2 • a) h2a]
  change semigroupSubgroup _ (cyclicTail a 1) ⊓ semigroupSubgroup _ B ≤
    semigroupSubgroup _ (cyclicTail (2 • a) 1)
  have hzero : 0 ∉ cyclicTail a 1 := by
    rintro ⟨n, _, hn, heq⟩
    exact hT.nsmul_ne_zero ha (Nat.ne_of_gt hn) heq
  rw [semigroupSubgroup_inf_eq hT _ (cyclicTail a 1) B hzero]
  have hcongr :
      semigroupSubgroup (AutomorphicAction.conjugation i) (cyclicTail a 1 ⊓ B) =
        semigroupSubgroup (AutomorphicAction.conjugation i)
          (cyclicTail (2 • a) 1 ⊓ B) := by
    apply semigroupSubgroup_eq_of_weightSupport
    intro χ hχ
    constructor
    · rintro ⟨⟨n, hn, hn0, rfl⟩, hB⟩
      have hroot := (mem_actionWeightSupport_conjugation_iff i
        (hT.nsmul_ne_zero ha (Nat.ne_of_gt hn0))).mp hχ
      rcases hE.eq_one_or_two_of_nsmul_mem i hT hroot with h | h
      · subst n
        change 1 • a ∈ B at hB
        rw [one_nsmul] at hB
        exact (hnot hB).elim
      · subst n
        exact ⟨⟨1, le_rfl, by omega, one_nsmul _⟩, hB⟩
    · rintro ⟨⟨n, hn, hn0, rfl⟩, hB⟩
      exact ⟨⟨n * 2, by omega, by omega, by rw [mul_comm, mul_nsmul]⟩, hB⟩
  rw [hcongr]
  exact semigroupSubgroup_mono _ inf_le_left

/-- If a semigroup omits both possible characters on a root ray, its
intersection with that actual root functor is trivial on every test. -/
theorem subgroup_inf_semigroup_eq_bot_of_not_mem
    (hT : IsSplitTorus T.toGrp) (hE : HasOppositeFactorPairs i)
    {a : characterLattice T} (ha : a ≠ 0)
    (B : AddSubsemigroup (characterLattice T))
    (hnot : a ∉ B) (hnot2 : 2 • a ∉ B) :
    subgroup i a ⊓ semigroupSubgroup (AutomorphicAction.conjugation i) B = ⊥ := by
  rw [← weightFiltration_one_eq_subgroup hT i a ha]
  change semigroupSubgroup _ (cyclicTail a 1) ⊓ semigroupSubgroup _ B = _
  have hzero : 0 ∉ cyclicTail a 1 := by
    rintro ⟨n, _, hn, heq⟩
    exact hT.nsmul_ne_zero ha (Nat.ne_of_gt hn) heq
  rw [semigroupSubgroup_inf_eq hT _ (cyclicTail a 1) B hzero]
  apply semigroupSubgroup_eq_bot_of_noAmbientWeights_without_realization _ hT
  rintro χ ⟨⟨n, hn, hn0, rfl⟩, hB⟩ hχ
  have hroot := (mem_actionWeightSupport_conjugation_iff i
    (hT.nsmul_ne_zero ha (Nat.ne_of_gt hn0))).mp hχ
  rcases hE.eq_one_or_two_of_nsmul_mem i hT hroot with h | h
  · subst n
    change 1 • a ∈ B at hB
    rw [one_nsmul] at hB
    exact hnot hB
  · subst n
    exact hnot2 hB

end Langlands.GroupScheme.RelativeRoot

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
    {φ : RootFunctionFamily T G}

omit [Smooth G.X.hom] in
/-- V4 transfers the original finite bound to the doubled root at twice
that bound, including negative bounds. -/
private theorem mem_double_filtration_of_mem
    (hφ : IsRootDatumValuation i φ)
    {a : characterLattice T} (ha : a ∈ relativeRoots i)
    (h2a : 2 • a ∈ relativeRoots i) (r : ℝ)
    {x : rationalPoints G} (hx : x ∈ rootFiltration i φ a r)
    (hx2 : x ∈ rootGroupPoints i (2 • a)) :
    x ∈ rootFiltration i φ (2 • a) (2 * r) := by
  refine ⟨hx2, ?_⟩
  rw [hφ.double a ha h2a x hx2, two_nsmul]
  simpa only [two_mul, WithTop.coe_add] using add_le_add hx.2 hx.2

/-- Intersecting a positive selected-depth subgroup with a smaller actual
semigroup subgroup retains exactly the selected depths of that semigroup. -/
theorem selectedRootDepthSubgroup_inf_semigroup_eq
    (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (A B : AddSubsemigroup (characterLattice T)) (hA : 0 ∉ A) (hBA : B ≤ A)
    (ν : cocharacterLattice T)
    (hpos : ∀ a ∈ relativeRoots i, a ∈ A → 0 < latticePairing T a ν)
    (d : characterLattice T →+ ℝ) :
    selectedRootDepthSubgroup hφ A d ⊓
        (RelativeRoot.semigroupSubgroup (AutomorphicAction.conjugation i) B).carrier
          (Over.mk (𝟙 _)) =
      selectedRootDepthSubgroup hφ B d := by
  classical
  apply le_antisymm
  · intro g hg
    obtain ⟨n, a, hinj, hrange⟩ :=
      RelativeRoot.exists_semigroupIndivisibleRoots_enumeration i hT A
    obtain ⟨x, hx, _⟩ :=
      (mem_selectedRootDepthSubgroup_iff_existsUnique hT hE hφ A hA ν hpos
        d a hinj hrange g).mp hg.1
    let X : ∀ j, (RelativeRoot.subgroup i (a j)).carrier (Over.mk (𝟙 _)) :=
      fun j => ⟨(x j).val, (x j).property.1⟩
    have hX : RelativeRoot.rootPointsProduct i a (Over.mk (𝟙 _)) X = g := hx
    have hXB : ∀ j, (X j).val ∈
        (RelativeRoot.semigroupSubgroup (AutomorphicAction.conjugation i) B).carrier
          (Over.mk (𝟙 _)) := by
      apply (RelativeRoot.rootPointsProduct_mem_semigroup_iff i hT hE A B hA hBA
        a hinj hrange (Over.mk (𝟙 _)) X).mp
      rw [hX]
      exact hg.2
    rw [← hx]
    apply Subgroup.list_prod_mem
    intro z hz
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
    have hj : a j ∈ RelativeRoot.semigroupIndivisibleRoots i A :=
      hrange ▸ Set.mem_range_self j
    by_cases hB : a j ∈ B
    · exact (le_iSup (fun b : {b : characterLattice T |
          b ∈ relativeRoots i ∧ b ∈ B} => hφ.filtrationSubgroup b.val (d b.val))
        ⟨a j, hj.1, hB⟩) (x j).property
    · by_cases h2B : 2 • a j ∈ B
      · have hdouble : (x j).val ∈ rootGroupPoints i (2 • a j) :=
          RelativeRoot.subgroup_inf_semigroup_le_double_of_not_mem i hT hE hj.1.1 B hB
            (Over.mk (𝟙 _)) ⟨(x j).property.1, hXB j⟩
        by_cases h2root : 2 • a j ∈ relativeRoots i
        · have hfil := mem_double_filtration_of_mem hφ hj.1 h2root (d (a j))
            (x j).property hdouble
          have hdepth : d (2 • a j) = 2 * d (a j) := by
            rw [map_nsmul, nsmul_eq_mul, Nat.cast_ofNat]
          rw [← hdepth] at hfil
          exact (le_iSup (fun b : {b : characterLattice T |
              b ∈ relativeRoots i ∧ b ∈ B} => hφ.filtrationSubgroup b.val (d b.val))
            ⟨2 • a j, h2root, h2B⟩) hfil
        · have hbot : RelativeRoot.subgroup i (2 • a j) = ⊥ := by
            rw [← RelativeRoot.weightFiltration_one_eq_subgroup hT i (2 • a j)
              (hT.nsmul_ne_zero hj.1.1 (by omega))]
            apply RelativeRoot.weightFiltration_eq_bot_of_noRelativeRoots
              RelativeRoot.semigroupRealization inferInstance hT i
              (hT.nsmul_ne_zero hj.1.1 (by omega))
            intro m hm hm0 hroot
            have hroot' : (m * 2) • a j ∈ relativeRoots i := by
              rw [mul_comm, mul_nsmul]
              exact hroot
            rcases hE.eq_one_or_two_of_nsmul_mem i hT hroot' with h | h
            · omega
            · have hm1 : m = 1 := by omega
              exact h2root (by simpa only [hm1, one_nsmul] using hroot)
          change (x j).val ∈ (RelativeRoot.subgroup i (2 • a j)).carrier
            (Over.mk (𝟙 _)) at hdouble
          rw [hbot] at hdouble
          rw [Subgroup.mem_bot.mp hdouble]
          exact (selectedRootDepthSubgroup hφ B d).one_mem
      · have hbot := RelativeRoot.subgroup_inf_semigroup_eq_bot_of_not_mem
          i hT hE hj.1.1 B hB h2B
        have htriv : (x j).val ∈
            ((RelativeRoot.subgroup i (a j)) ⊓
              RelativeRoot.semigroupSubgroup (AutomorphicAction.conjugation i) B).carrier
              (Over.mk (𝟙 _)) := ⟨(x j).property.1, hXB j⟩
        rw [hbot] at htriv
        rw [Subgroup.mem_bot.mp htriv]
        exact (selectedRootDepthSubgroup hφ B d).one_mem
  · apply le_inf
    · refine iSup_le fun b => ?_
      exact le_iSup (fun a : {a : characterLattice T |
          a ∈ relativeRoots i ∧ a ∈ A} => hφ.filtrationSubgroup a.val (d a.val))
        ⟨b.val, b.property.1, hBA b.property.2⟩
    · exact selectedRootDepthSubgroup_le_semigroupSubgroup hT hφ B d

/-- The intersection identification on the original rational point group. -/
def selectedRootDepthIntersectionPointsEquiv
    (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (A B : AddSubsemigroup (characterLattice T)) (hA : 0 ∉ A) (hBA : B ≤ A)
    (ν : cocharacterLattice T)
    (hpos : ∀ a ∈ relativeRoots i, a ∈ A → 0 < latticePairing T a ν)
    (d : characterLattice T →+ ℝ) :
    ↥(selectedRootDepthSubgroup hφ A d ⊓
      (RelativeRoot.semigroupSubgroup (AutomorphicAction.conjugation i) B).carrier
        (Over.mk (𝟙 _)) : Subgroup (rationalPoints G)) ≃*
      ↥(selectedRootDepthSubgroup hφ B d) :=
  MulEquiv.subgroupCongr
    (selectedRootDepthSubgroup_inf_semigroup_eq hT hE hφ A B hA hBA ν hpos d)

@[simp] theorem selectedRootDepthIntersectionPointsEquiv_val
    (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (A B : AddSubsemigroup (characterLattice T)) (hA : 0 ∉ A) (hBA : B ≤ A)
    (ν : cocharacterLattice T)
    (hpos : ∀ a ∈ relativeRoots i, a ∈ A → 0 < latticePairing T a ν)
    (d : characterLattice T →+ ℝ)
    (x : ↥(selectedRootDepthSubgroup hφ A d ⊓
      (RelativeRoot.semigroupSubgroup (AutomorphicAction.conjugation i) B).carrier
        (Over.mk (𝟙 _)) : Subgroup (rationalPoints G))) :
    (selectedRootDepthIntersectionPointsEquiv hT hE hφ A B hA hBA ν hpos d x).val =
      x.val := rfl

end Langlands.Geometry.Building
