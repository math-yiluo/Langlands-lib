import Langlands.AbelianScheme.Tate.ConnectedIntegralLatticeReflectionProof

/-! # Primitive homomorphisms of abelian schemes -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.AbelianScheme.Tate

open Langlands.AlgebraicGeometry.FiniteEtale

variable {S : Scheme.{u}}

/-- An actual homomorphism is primitive when it is a positive integer multiple of an
actual homomorphism only with multiplier one. -/
def IsPrimitiveHom {A B : AbelianScheme S} (f : A ⟶ B) : Prop :=
  ∀ (j : ℕ) (g : A ⟶ B), j • g = f → j = 1

/-- Multiplication by `k` acts on actual torsion points as multiplication by `k`. -/
theorem levelMap_multiplication (A : AbelianScheme S) (T : Over S) (k n : ℕ)
    (x : GroupScheme.Tate.Level A.toGrp T n) :
    GroupScheme.Tate.levelMap T (GroupScheme.multiplication A.toGrp (k : ℤ)) n x = k • x := by
  apply GroupScheme.Tate.toSection_injective A.toGrp T n
  rw [map_nsmul]
  change (Additive.toMul x).val ≫ (GroupScheme.multiplication A.toGrp (k : ℤ)).hom.hom =
    Additive.toMul (k • GroupScheme.Tate.toSection A.toGrp T n x)
  rw [GroupScheme.points_multiplication, zpow_natCast, toMul_nsmul]
  rfl

/-- The action on torsion points of a composite is the composite of the actions. -/
theorem levelMap_comp {A B C : AbelianScheme S} (T : Over S) (f : A ⟶ B) (g : B ⟶ C)
    (n : ℕ) (x : GroupScheme.Tate.Level A.toGrp T n) :
    GroupScheme.Tate.levelMap T (groupHom (f ≫ g)) n x =
      GroupScheme.Tate.levelMap T (groupHom g) n
        (GroupScheme.Tate.levelMap T (groupHom f) n x) := by
  apply GroupScheme.Tate.toSection_injective C.toGrp T n
  change (Additive.toMul x).val ≫ (groupHom (f ≫ g)).hom.hom =
    ((Additive.toMul x).val ≫ (groupHom f).hom.hom) ≫ (groupHom g).hom.hom
  rw [Category.assoc]
  rfl

/-- Multiplying an actual homomorphism by `k` multiplies its action on torsion points by `k`. -/
theorem levelMap_nsmul {A B : AbelianScheme S} (T : Over S) (f : A ⟶ B) (k n : ℕ)
    (x : GroupScheme.Tate.Level A.toGrp T n) :
    GroupScheme.Tate.levelMap T (groupHom (k • f)) n x =
      k • GroupScheme.Tate.levelMap T (groupHom f) n x := by
  have hk : k • f = (k • 𝟙 A) ≫ f := by
    rw [Preadditive.nsmul_comp, Category.id_comp]
  rw [hk, levelMap_comp, groupHom_nsmul_id, levelMap_multiplication, map_nsmul]

/-- A positive multiple kills the torsion of the same order. -/
theorem levelMap_nsmul_self {A B : AbelianScheme S} (T : Over S) (f : A ⟶ B) (n : ℕ)
    (x : GroupScheme.Tate.Level A.toGrp T n) :
    GroupScheme.Tate.levelMap T (groupHom (n • f)) n x = 0 := by
  rw [levelMap_nsmul]
  exact GroupScheme.Tate.level_nsmul_eq_zero B.toGrp T n _

/-- A homomorphism whose positive divisors are bounded is a positive multiple of a primitive
homomorphism. -/
theorem exists_isPrimitiveHom_nsmul_eq {A B : AbelianScheme S} (f : A ⟶ B) (N : ℕ)
    (hbound : ∀ (k : ℕ) (g : A ⟶ B), 0 < k → k • g = f → k ≤ N) :
    ∃ (k : ℕ) (g : A ⟶ B), 0 < k ∧ k • g = f ∧ IsPrimitiveHom g := by
  classical
  let P : ℕ → Prop := fun k => 0 < k ∧ ∃ g : A ⟶ B, k • g = f
  have h1 : P 1 := ⟨Nat.one_pos, f, one_smul ℕ f⟩
  have hN : 1 ≤ N := hbound 1 f Nat.one_pos (one_smul ℕ f)
  obtain ⟨hk0, g, hg⟩ : P (Nat.findGreatest P N) := Nat.findGreatest_spec hN h1
  refine ⟨Nat.findGreatest P N, g, hk0, hg, ?_⟩
  intro j g' hj
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exfalso
      have hg0 : g = 0 := by rw [← hj, zero_smul]
      have hf0 : f = 0 := by rw [← hg, hg0, smul_zero]
      have := hbound (N + 1) 0 (Nat.succ_pos N) (by rw [smul_zero, hf0])
      omega
    · exact hj0
  have hkj : (Nat.findGreatest P N * j) • g' = f := by rw [mul_smul, hj, hg]
  have hP : P (Nat.findGreatest P N * j) := ⟨Nat.mul_pos hk0 hj0, g', hkj⟩
  have hle := Nat.le_findGreatest (hbound _ g' hP.1 hkj) hP
  have : j ≤ 1 := by
    by_contra hcon
    have : Nat.findGreatest P N * 1 < Nat.findGreatest P N * j :=
      Nat.mul_lt_mul_of_pos_left (by omega) hk0
    omega
  omega

variable (htor : TorsionFiniteEtaleStatement.{u}) [IsLocallyNoetherian S] [ConnectedSpace S]
  (hu : ∀ k : GroupScheme.Tate.Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)

include htor hu in
/-- On a connected base, an actual homomorphism is divisible by `n` exactly when it kills
the `n`-torsion points at one algebraically closed point. -/
theorem exists_nsmul_eq_iff_levelMap_eq_zero {A B : AbelianScheme S} (f : A ⟶ B) {n : ℕ}
    (hn : 0 < n) :
    (∃ g : A ⟶ B, n • g = f) ↔
      ∀ x : GroupScheme.Tate.Level A.toGrp (Over.mk s) n,
        GroupScheme.Tate.levelMap (Over.mk s) (groupHom f) n x = 0 := by
  constructor
  · rintro ⟨g, rfl⟩ x
    exact levelMap_nsmul_self (Over.mk s) g n x
  · intro hz
    have hker := kernel_comp_eq_one_of_levelMap_eq_zero htor s f n hn
      (hu ⟨n, hn, trivial⟩) hz
    let hniso := multiplication_isIsogeny_of_isUnit A n (hu ⟨n, hn, trivial⟩)
    let g : A ⟶ B := Additive.ofMul
      (GroupScheme.IsogenyFactorization.lift hniso (groupHom f) hker)
    have hfac : (n • 𝟙 A) ≫ g = f := by
      apply Additive.toMul.injective
      change groupHom (n • 𝟙 A) ≫ groupHom g = groupHom f
      rw [groupHom_nsmul_id]
      exact GroupScheme.IsogenyFactorization.fac hniso (groupHom f) hker
    exact ⟨g, by simpa only [Preadditive.nsmul_comp, Category.id_comp] using hfac⟩

include htor hu s in
/-- Two primitive homomorphisms on the same positive rational ray coincide, with equal
multipliers. -/
theorem eq_of_nsmul_eq_nsmul_of_isPrimitiveHom {A B : AbelianScheme S} {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) {f g : A ⟶ B} (hf : IsPrimitiveHom f) (hg : IsPrimitiveHom g)
    (h : a • f = b • g) : a = b ∧ f = g := by
  obtain ⟨d, a', b', hd0, hcop, rfl, rfl⟩ :=
    Nat.exists_coprime' (m := a) (n := b) (Nat.gcd_pos_of_pos_left b ha)
  have ha' : 0 < a' := Nat.pos_of_mul_pos_right ha
  have hb'0 : 0 < b' := Nat.pos_of_mul_pos_right hb
  have h' : a' • f = b' • g := by
    apply hom_nsmul_injective hu hd0
    simp only [smul_smul]
    rw [mul_comm d a', mul_comm d b']
    exact h
  -- `f` kills the `b'`-torsion, and `g` kills the `a'`-torsion
  have kill : ∀ {c c' : ℕ} {u v : A ⟶ B}, Nat.Coprime c c' → 0 < c' →
      c • u = c' • v → ∃ w : A ⟶ B, c' • w = u := by
    intro c c' u v hcc hc' huv
    refine (exists_nsmul_eq_iff_levelMap_eq_zero htor hu s u hc').mpr ?_
    intro x
    have h1 : c • GroupScheme.Tate.levelMap (Over.mk s) (groupHom u) c' x = 0 := by
      rw [← levelMap_nsmul, huv]
      exact levelMap_nsmul_self (Over.mk s) v c' x
    have h2 : c' • GroupScheme.Tate.levelMap (Over.mk s) (groupHom u) c' x = 0 :=
      GroupScheme.Tate.level_nsmul_eq_zero B.toGrp (Over.mk s) c' _
    have hgcd : Nat.gcd c c' = 1 := hcc
    have hdvd : addOrderOf (GroupScheme.Tate.levelMap (Over.mk s) (groupHom u) c' x) ∣ 1 := by
      rw [← hgcd]
      exact Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero h1) (addOrderOf_dvd_of_nsmul_eq_zero h2)
    exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
  obtain ⟨w, hw⟩ := kill hcop hb'0 h'
  obtain ⟨w', hw'⟩ := kill hcop.symm ha' h'.symm
  have hb1 : b' = 1 := hf b' w hw
  have ha1 : a' = 1 := hg a' w' hw'
  subst hb1 ha1
  exact ⟨rfl, by simpa only [one_smul] using h'⟩

end Langlands.AbelianScheme.Tate
