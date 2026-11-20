import Langlands.Global.RankinSelberg.TriangularDiagonal
import Langlands.Group.GL.CartanProof
import Langlands.Group.GL.PrincipalLevelDominance
import Langlands.Group.GL.TriangularParabolic
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTerm

/-! # Cartan representatives contracting the upper triangular subgroup -/

noncomputable section

namespace Langlands.GeneralLinear

open Matrix Conductor Iwasawa HarishChandraSchwartz

universe u

/-- A compact double-coset cover with representatives whose inverse conjugations
carry a common upper triangular neighbourhood into each prescribed open subgroup. -/
def HasUpperTriangularCartanContraction (n : ℕ) (R : Type u)
    [CommRing R] [TopologicalSpace R] : Prop :=
  ∃ (K : CompactOpenSubgroup (GeneralLinear n R)) (M : Set (GeneralLinear n R)),
    (∀ g : GeneralLinear n R, ∃ k : K.toSubgroup, ∃ m ∈ M, ∃ j : K.toSubgroup,
      g = (k : GeneralLinear n R) * m * (j : GeneralLinear n R)) ∧
    ∀ J : OpenSubgroup (GeneralLinear n R),
      ∃ L : CompactOpenSubgroup (upperTriangularSubgroup n R),
        ∀ m ∈ M, ∀ p : L.toSubgroup,
          m⁻¹ * ((p : upperTriangularSubgroup n R) : GeneralLinear n R) * m ∈ J

/-- The upper triangular conditions are closed conditions on matrix entries. -/
theorem isClosed_upperTriangularSubgroup (n : ℕ) (R : Type u)
    [CommRing R] [TopologicalSpace R] [T2Space R] :
    IsClosed (upperTriangularSubgroup n R : Set (GeneralLinear n R)) :=
  Langlands.Global.RankinSelbergGlobal.GaugeDescent.isClosed_upperTriangular (n := n) (A := R)

section Valued

variable {F : Type u} [Field F] [ValuativeRel F]

private theorem integralRange_eq_rankPrincipalLevel_zero (n : ℕ) :
    integralRange (ValuativeRel.valuation F) n = rankPrincipalLevel F n 0 := by
  cases n with
  | zero =>
    ext g
    rw [eq_one_of_rank_zero F g]
    simp
  | succ n =>
    rw [rankPrincipalLevel_succ, principalLevelSubgroup_zero, integralRange_succ]

private theorem torus_conj_entry_difference {n : ℕ} {ϖ : Fˣ}
    (hϖ : ValuativeRel.valuation F (ϖ : F) ≤ 1) {lam : Fin (n + 1) → ℤ}
    (hlam : Antitone lam) {g : GeneralLinear (n + 1) F}
    (hg : g ∈ upperTriangularSubgroup (n + 1) F)
    {I : Ideal (ValuativeRel.valuation F).integer}
    (hentry : ∀ i j, ∃ x : (ValuativeRel.valuation F).integer, x ∈ I ∧
      (x : F) = g i j - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i j)
    (i j : Fin (n + 1)) :
    ∃ x : (ValuativeRel.valuation F).integer, x ∈ I ∧
      (x : F) = (torus ϖ lam * g * (torus ϖ lam)⁻¹) i j -
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i j := by
  rw [torus_inv, torus, diagonalUnits_mul_mul_apply]
  rcases lt_trichotomy i j with hij | rfl | hji
  · obtain ⟨x, hx, hxg⟩ := hentry i j
    let a : (ValuativeRel.valuation F).integer :=
      ⟨_, ratio_mem_integer hϖ hlam i j hij⟩
    refine ⟨a * x, I.mul_mem_left a hx, ?_⟩
    have hxg' : (x : F) = g i j := by
      simpa only [Matrix.one_apply_ne hij.ne, sub_zero] using hxg
    change (↑(ϖ ^ lam i * (ϖ ^ lam j)⁻¹ : Fˣ) : F) * (x : F) = _
    rw [Units.val_mul, hxg', Matrix.one_apply_ne hij.ne, sub_zero]
    ac_rfl
  · obtain ⟨x, hx, hxg⟩ := hentry i i
    refine ⟨x, hx, ?_⟩
    rw [mul_right_comm, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    exact hxg
  · refine ⟨0, I.zero_mem, ?_⟩
    rw [(mem_upperTriangularSubgroup_iff g).mp hg i j hji, mul_zero, zero_mul,
      Matrix.one_apply_ne hji.ne', sub_zero]
    rfl

/-- Conjugation by a dominant diagonal preserves the upper triangular part of
every principal congruence level. -/
theorem torus_conj_mem_rankPrincipalLevel_of_upperTriangular {n a : ℕ} {ϖ : Fˣ}
    (hϖ : ValuativeRel.valuation F (ϖ : F) ≤ 1) {lam : Fin n → ℤ}
    (hlam : Antitone lam) {g : GeneralLinear n F}
    (hg : g ∈ upperTriangularSubgroup n F) (hlevel : g ∈ rankPrincipalLevel F n a) :
    torus ϖ lam * g * (torus ϖ lam)⁻¹ ∈ rankPrincipalLevel F n a := by
  cases n with
  | zero =>
    rw [eq_one_of_rank_zero F (torus ϖ lam * g * (torus ϖ lam)⁻¹)]
    exact one_mem _
  | succ n =>
    rw [rankPrincipalLevel_succ, principalLevelSubgroup,
      mem_principalCongruenceSubgroup_iff] at hlevel ⊢
    exact ⟨torus_conj_entry_difference hϖ hlam hg hlevel.1, by
      simpa only [_root_.mul_inv_rev, inv_inv, mul_assoc] using
        torus_conj_entry_difference hϖ hlam (inv_mem hg) hlevel.2⟩

end Valued

/-- The inverse Cartan chamber gives a uniform upper triangular contraction
over any nonarchimedean local field. -/
theorem hasUpperTriangularCartanContraction_localField (n : ℕ) (F : Type u)
    [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    HasUpperTriangularCartanContraction n F := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUniformizingElement F
  let K : CompactOpenSubgroup (GeneralLinear n F) :=
    ⟨⟨rankPrincipalLevel F n 0, isOpen_rankPrincipalLevel F n 0⟩,
      isCompact_rankPrincipalLevel F n 0⟩
  let M : Set (GeneralLinear n F) :=
    {m | ∃ lam : Fin n → ℤ, Antitone lam ∧ m = (torus ϖ lam)⁻¹}
  refine ⟨K, M, ?_, ?_⟩
  · intro g
    obtain ⟨lam, hlam, a, ha, b, hb, hg⟩ := Cartan.exists_cartan hϖ n g⁻¹
    rw [integralRange_eq_rankPrincipalLevel_zero] at ha hb
    refine ⟨⟨b⁻¹, inv_mem hb⟩, (torus ϖ lam)⁻¹, ⟨lam, hlam, rfl⟩,
      ⟨a⁻¹, inv_mem ha⟩, ?_⟩
    simpa only [_root_.mul_inv_rev, inv_inv, mul_assoc] using congrArg Inv.inv hg
  · intro J
    obtain ⟨a, -, ha⟩ := exists_pos_rankPrincipalLevel_subset F n (J.isOpen.mem_nhds J.one_mem)
    let C : CompactOpenSubgroup (GeneralLinear n F) :=
      ⟨⟨rankPrincipalLevel F n a, isOpen_rankPrincipalLevel F n a⟩,
        isCompact_rankPrincipalLevel F n a⟩
    let := IsTopologicalAddGroup.rightUniformSpace F
    have := isUniformAddGroup_of_addCommGroup (G := F)
    refine ⟨C.subgroupOf (isClosed_upperTriangularSubgroup n F), ?_⟩
    rintro _ ⟨lam, hlam, rfl⟩ p
    rw [inv_inv]
    exact ha (torus_conj_mem_rankPrincipalLevel_of_upperTriangular hϖ.1.le hlam
      (p : upperTriangularSubgroup n F).property p.property)

end Langlands.GeneralLinear
