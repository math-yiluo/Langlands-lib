import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Rational.GeneralLinearIndexing
import Langlands.GroupScheme.Reductive.GeneralLinearRootDatumProof

/-! # Simple relative roots for the diagonal torus of GL -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.GeneralLinear

variable {N : ℕ} (k : Type u) [Field k]

local notation "𝔻" =>
  splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin N))
local notation "iD" => diagonalTorus (Fin N) (CommRingCat.of k)

theorem latticePairing_rootDatum_root (p : {p : Fin N × Fin N // p.1 ≠ p.2})
    (zeta : cocharacterLattice 𝔻) :
    latticePairing 𝔻 ((rootDatum (Fin N) k).root p) zeta =
      cocharacterCoordEquiv (Fin N) k zeta p.val.1 -
        cocharacterCoordEquiv (Fin N) k zeta p.val.2 := by
  rw [latticePairing_coord, characterCoordEquiv_rootDatum_root, sum_rootCoord_mul]

/-- Strict decrease makes a root positive exactly when its indices increase. -/
theorem mem_positiveRelativeRoots_diagonalTorus_iff
    (nu : cocharacterLattice 𝔻)
    (hnu : StrictAnti (cocharacterCoordEquiv (Fin N) k nu))
    (alpha : characterLattice 𝔻) :
    alpha ∈ positiveRelativeRoots iD nu ↔
      ∃ a b : Fin N, ∃ hab : a < b,
        alpha = (rootDatum (Fin N) k).root ⟨(a, b), ne_of_lt hab⟩ := by
  have hrange := (isRootDatumOf_rootDatum (n := Fin N) k).2.1
  constructor
  · rintro ⟨halpha, hpos⟩
    change alpha ∈ roots iD at halpha
    rw [← hrange] at halpha
    obtain ⟨p, rfl⟩ := halpha
    rw [latticePairing_rootDatum_root] at hpos
    have hab : p.val.1 < p.val.2 := by
      by_contra hn
      have hw := hnu.antitone (le_of_not_gt hn)
      omega
    exact ⟨p.val.1, p.val.2, hab, rfl⟩
  · rintro ⟨a, b, hab, rfl⟩
    constructor
    · change (rootDatum (Fin N) k).root _ ∈ roots iD
      rw [← hrange]
      exact Set.mem_range_self _
    · rw [latticePairing_rootDatum_root]
      exact sub_pos.mpr (hnu hab)

private theorem positive_root_height
    (nu : cocharacterLattice 𝔻)
    (hnu : StrictAnti (cocharacterCoordEquiv (Fin N) k nu))
    {alpha : characterLattice 𝔻}
    (halpha : alpha ∈ positiveRelativeRoots iD nu) :
    1 ≤ latticePairing 𝔻 alpha (cocharacterOfWeights k (fun a => -(a.val : ℤ))) := by
  obtain ⟨a, b, hab, rfl⟩ :=
    (mem_positiveRelativeRoots_diagonalTorus_iff k nu hnu alpha).mp halpha
  rw [latticePairing_rootDatum_root, cocharacterCoordEquiv_cocharacterOfWeights]
  have hab' : a.val < b.val := hab
  dsimp
  omega

theorem simpleRootCharacter_mem_simpleRelativeRoots
    (nu : cocharacterLattice 𝔻)
    (hnu : StrictAnti (cocharacterCoordEquiv (Fin N) k nu))
    (a : Fin (N - 1)) :
    simpleRootCharacter k a ∈ simpleRelativeRoots iD nu := by
  have hpos : simpleRootCharacter k a ∈ positiveRelativeRoots iD nu := by
    apply (mem_positiveRelativeRoots_diagonalTorus_iff k nu hnu _).mpr
    refine ⟨(adjacentRootPair a).val.1, (adjacentRootPair a).val.2, ?_, rfl⟩
    change a.val < a.val + 1
    omega
  refine ⟨hpos, ?_⟩
  rintro ⟨beta, hbeta, gamma, hgamma, heq⟩
  have hb := positive_root_height k nu hnu hbeta
  have hc := positive_root_height k nu hnu hgamma
  have hheight : latticePairing 𝔻 (simpleRootCharacter k a)
      (cocharacterOfWeights k (fun x => -(x.val : ℤ))) = 1 := by
    rw [latticePairing_simpleRootCharacter, cocharacterCoordEquiv_cocharacterOfWeights]
    simp only [adjacentRootPair]
    omega
  rw [heq, map_add, LinearMap.add_apply] at hheight
  omega

/-- For decreasing cocharacter coordinates the simple relative roots are precisely
the actual adjacent characters. This includes ranks zero and one. -/
theorem simpleRelativeRoots_diagonalTorus
    (nu : cocharacterLattice 𝔻)
    (hnu : StrictAnti (cocharacterCoordEquiv (Fin N) k nu)) :
    simpleRelativeRoots iD nu = Set.range (simpleRootCharacter k) := by
  apply Set.Subset.antisymm
  · intro alpha halpha
    obtain ⟨a, b, hab, rfl⟩ :=
      (mem_positiveRelativeRoots_diagonalTorus_iff k nu hnu alpha).mp halpha.1
    have hadj : a.val + 1 = b.val := by
      by_contra hgap
      let c : Fin N := ⟨a.val + 1, by omega⟩
      have hac : a < c := by change a.val < a.val + 1; omega
      have hcb : c < b := by change a.val + 1 < b.val; omega
      have hfirst : (rootDatum (Fin N) k).root ⟨(a, c), ne_of_lt hac⟩ ∈
          positiveRelativeRoots iD nu :=
        (mem_positiveRelativeRoots_diagonalTorus_iff k nu hnu _).mpr ⟨a, c, hac, rfl⟩
      have hsecond : (rootDatum (Fin N) k).root ⟨(c, b), ne_of_lt hcb⟩ ∈
          positiveRelativeRoots iD nu :=
        (mem_positiveRelativeRoots_diagonalTorus_iff k nu hnu _).mpr ⟨c, b, hcb, rfl⟩
      apply halpha.2
      refine ⟨_, hfirst, _, hsecond, ?_⟩
      apply (characterCoordEquiv (Fin N) k).injective
      rw [map_add, characterCoordEquiv_rootDatum_root,
        characterCoordEquiv_rootDatum_root, characterCoordEquiv_rootDatum_root]
      simp only [rootCoord]
      abel
    refine ⟨⟨a.val, by omega⟩, ?_⟩
    apply (characterCoordEquiv (Fin N) k).injective
    rw [characterCoordEquiv_simpleRootCharacter, characterCoordEquiv_rootDatum_root]
    congr 1
    apply Prod.ext <;> apply Fin.ext
    · rfl
    · exact hadj
  · rintro _ ⟨a, rfl⟩
    exact simpleRootCharacter_mem_simpleRelativeRoots k nu hnu a

end Langlands.GroupScheme.GeneralLinear
