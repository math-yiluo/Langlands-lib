import Langlands.GroupScheme.Rational.SimpleRootValueCharacter
import Langlands.GroupScheme.Rational.QuasiSplitCompatiblePinning
import Langlands.GroupScheme.Rational.RootRayDecomposition
import Langlands.GroupScheme.Reductive.RootReducednessReduction

/-! # Galois-compatible pinnings in which a relative root fiber consists of simple roots -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

namespace RelativeRoot

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]

omit [LocallyOfFiniteType G.X.hom] in
/-- A relative root that is linearly dependent on an indivisible root `b`, and positive on a
cocharacter on which `b` is positive, is a positive integral multiple of `b`. -/
theorem eq_nsmul_of_not_linearIndependent (hroot : HasRelativeRootSystem i)
    (hS : IsSplitTorus S.toGrp) {b β : characterLattice S} (hb : b ∈ indivisibleRoots i)
    (hβ : β ∈ relativeRoots i) (hdep : ¬ LinearIndependent ℤ ![b, β])
    {μ : cocharacterLattice S} (hbμ : 0 < latticePairing S b μ)
    (hβμ : 0 < latticePairing S β μ) :
    ∃ p : ℕ, 0 < p ∧ β = p • b := by
  obtain ⟨n, m, hn, hm, hnm⟩ : ∃ n m : ℕ, 0 < n ∧ 0 < m ∧ n • b = m • β := by
    rw [LinearIndependent.pair_iff] at hdep
    push Not at hdep
    obtain ⟨x, y, hxy, hne⟩ := hdep
    have hpair : x * latticePairing S b μ + y * latticePairing S β μ = 0 := by
      have h := congrArg (fun χ => latticePairing S χ μ) hxy
      simpa only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        map_zero, LinearMap.zero_apply] using h
    rcases lt_trichotomy x 0 with hx | hx | hx
    · have hy : 0 < y := by nlinarith
      refine ⟨x.natAbs, y.natAbs, by omega, by omega, ?_⟩
      have h1 : y • β = (-x) • b := by
        rw [neg_smul]
        exact eq_neg_of_add_eq_zero_right hxy
      rw [← natCast_zsmul, ← natCast_zsmul, Int.natCast_natAbs, Int.natCast_natAbs,
        abs_of_neg hx, abs_of_pos hy]
      exact h1.symm
    · subst hx
      have hy : y * latticePairing S β μ = 0 := by simpa using hpair
      rcases mul_eq_zero.mp hy with h | h
      · exact absurd h (hne rfl)
      · omega
    · have hy : y < 0 := by nlinarith
      refine ⟨x.natAbs, y.natAbs, by omega, by omega, ?_⟩
      have h1 : x • b = (-y) • β := by
        rw [neg_smul]
        exact eq_neg_of_add_eq_zero_left hxy
      rw [← natCast_zsmul, ← natCast_zsmul, Int.natCast_natAbs, Int.natCast_natAbs,
        abs_of_pos hx, abs_of_neg hy]
      exact h1
  obtain ⟨a, ha, p, -, hp, hpa⟩ := exists_indivisiblePositiveRoot_ray i μ hβ hβμ
  by_cases hab : b = a
  · subst hab
    exact ⟨p, hp, hpa.symm⟩
  · exfalso
    have hdisj := disjoint_cyclicTail_indivisibleRoots i hroot hS hb ha.1 hab
    have h1 : n • b ∈ (cyclicTail b 1 : Set (characterLattice S)) := ⟨n, by omega, hn, rfl⟩
    have h2 : n • b ∈ (cyclicTail a 1 : Set (characterLattice S)) := by
      refine ⟨m * p, Nat.mul_pos hm hp, Nat.mul_pos hm hp, ?_⟩
      rw [hnm, ← hpa, smul_smul]
    exact Set.disjoint_left.mp hdisj h1 h2

/-- Every indivisible relative root is simple for some generic cocharacter. The cocharacter is
`N • ζ + μ`, where `ζ` kills `b` and only the roots dependent on `b`, `μ` is generic and
positive on `b`, and `N` exceeds every `|⟨γ, μ⟩|`. -/
theorem exists_isGenericCocharacter_mem_simpleRelativeRoots (hroot : HasRelativeRootSystem i)
    (hS : IsSplitTorus S.toGrp) {b : characterLattice S} (hb : b ∈ indivisibleRoots i) :
    ∃ lam : cocharacterLattice S, IsGenericCocharacter i lam ∧
      b ∈ simpleRelativeRoots i lam := by
  classical
  have hfin : (relativeRoots i).Finite := hS.finite_relativeRoots i
  have hb0 : b ≠ 0 := hb.1.1
  obtain ⟨ζ, hζb, hζ⟩ := RootReducedness.exists_cocharacter_pairing_eq_zero hS hb0 hfin
  obtain ⟨μ₀, hμ₀⟩ := hS.exists_genericCocharacter i
  obtain ⟨μ, hμ, hbμ⟩ : ∃ μ : cocharacterLattice S,
      IsGenericCocharacter i μ ∧ 0 < latticePairing S b μ := by
    rcases lt_or_gt_of_ne (hμ₀ b hb.1) with h | h
    · refine ⟨-μ₀, fun γ hγ => ?_, ?_⟩
      · simpa only [map_neg, neg_ne_zero] using hμ₀ γ hγ
      · simpa only [map_neg, Left.neg_pos_iff] using h
    · exact ⟨μ₀, hμ₀, h⟩
  let N : ℤ := ∑ γ ∈ hfin.toFinset, |latticePairing S γ μ| + 1
  have hN : ∀ γ ∈ relativeRoots i, |latticePairing S γ μ| < N := by
    intro γ hγ
    have h := Finset.single_le_sum (f := fun γ => |latticePairing S γ μ|)
      (fun _ _ => abs_nonneg _) (hfin.mem_toFinset.mpr hγ)
    omega
  have hN0 : 0 < N := lt_of_le_of_lt (abs_nonneg _) (hN b hb.1)
  let lam : cocharacterLattice S := N • ζ + μ
  have hlam (γ : characterLattice S) :
      latticePairing S γ lam = N * latticePairing S γ ζ + latticePairing S γ μ := by
    simp only [lam, map_add, map_zsmul, smul_eq_mul]
  have hpos_of (γ : characterLattice S) (hγ : γ ∈ relativeRoots i)
      (hz : 0 < latticePairing S γ ζ) : 0 < latticePairing S γ lam := by
    have h1 := hN γ hγ
    have h2 := neg_abs_le (latticePairing S γ μ)
    rw [hlam]
    nlinarith
  have hneg_of (γ : characterLattice S) (hγ : γ ∈ relativeRoots i)
      (hz : latticePairing S γ ζ < 0) : latticePairing S γ lam < 0 := by
    have h1 := hN γ hγ
    have h2 := le_abs_self (latticePairing S γ μ)
    rw [hlam]
    nlinarith
  have hsign (γ : characterLattice S) (hγ : γ ∈ relativeRoots i)
      (hpos : 0 < latticePairing S γ lam) : 0 ≤ latticePairing S γ ζ := by
    by_contra hz
    push Not at hz
    exact absurd (hneg_of γ hγ hz) (not_lt.mpr hpos.le)
  have hgen : IsGenericCocharacter i lam := by
    intro γ hγ
    rcases lt_trichotomy (latticePairing S γ ζ) 0 with hz | hz | hz
    · exact (hneg_of γ hγ hz).ne
    · rw [hlam, hz, mul_zero, zero_add]
      exact hμ γ hγ
    · exact (hpos_of γ hγ hz).ne'
  have hbpos : 0 < latticePairing S b lam := by
    rw [hlam, hζb, mul_zero, zero_add]
    exact hbμ
  refine ⟨lam, hgen, ⟨hb.1, hbpos⟩, ?_⟩
  rintro ⟨β, ⟨hβ, hβpos⟩, γ, ⟨hγ, hγpos⟩, hsum⟩
  have hβζ := hsign β hβ hβpos
  have hγζ := hsign γ hγ hγpos
  have hsumζ : latticePairing S β ζ + latticePairing S γ ζ = 0 := by
    have h := congrArg (fun χ => latticePairing S χ ζ) hsum
    simp only [map_add, LinearMap.add_apply] at h
    rw [← h]
    exact hζb
  have hβ0 : latticePairing S β ζ = 0 := by omega
  have hγ0 : latticePairing S γ ζ = 0 := by omega
  have hβμ : 0 < latticePairing S β μ := by
    rw [hlam, hβ0, mul_zero, zero_add] at hβpos
    exact hβpos
  have hγμ : 0 < latticePairing S γ μ := by
    rw [hlam, hγ0, mul_zero, zero_add] at hγpos
    exact hγpos
  obtain ⟨p, hp, rfl⟩ :=
    eq_nsmul_of_not_linearIndependent i hroot hS hb hβ (hζ β hβ hβ0) hbμ hβμ
  obtain ⟨q, hq, rfl⟩ :=
    eq_nsmul_of_not_linearIndependent i hroot hS hb hγ (hζ γ hγ hγ0) hbμ hγμ
  have h := congrArg (fun χ => latticePairing S χ μ) hsum
  simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply,
    nsmul_eq_mul] at h
  have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast hp
  have hq1 : (1 : ℤ) ≤ q := by exact_mod_cast hq
  nlinarith

end RelativeRoot

namespace SimpleRootFiber

section Restriction

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))} (f : S ⟶ T)

local notation "bK" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange bK) T
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange bK) S
local notation "f_K" => CategoryTheory.Functor.map (CommGroupScheme.baseChange bK) f

/-- A character of `T_K` restricts to `a` exactly when its pullback along `f_K` is the base
change of `a`. -/
theorem restrictCharacter_eq_iff (hS : IsSplitTorus S.toGrp)
    (χ : characterLattice T_K) (a : characterLattice S) :
    restrictCharacter k K f hS χ = a ↔ f_K ≫ χ = characterLattice.baseChange bK S a := by
  rw [← restrictCharacter_baseChange k K f hS χ]
  exact ⟨fun h => h ▸ rfl, fun h => (characterLattice.baseChangeEquiv bK S hS).injective h⟩

end Restriction

section Roots

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
  (f : S ⟶ T) (j : T.toGrp ⟶ G)

local notation "bK" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange bK) T
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange bK) G
local notation "j_K" => CategoryTheory.Functor.map (GroupScheme.baseChange bK) j

local instance simpleRootFiberIsAffineHom : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom bK)
  infer_instance

variable {J : Type u} [Finite J]
  {P : RootDatum J
    (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))}
  (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map j) P)
  (hf : IsMaximalSplitTorus (CommGroupScheme.groupHom f ≫ j))
  (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
  (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp)

variable [P.IsReduced]
  (ν : cocharacterLattice S)
  (hν : IsGenericCocharacter (CommGroupScheme.groupHom f ≫ j) ν)

omit [P.IsReduced] in
include hP hcent hT in
/-- Two distinct simple roots of any base with the same restriction `a` are orthogonal when
`2 • a` is not a relative root. -/
theorem isOrthogonal_of_restrictCharacter_eq (B : P.Base) {t t' : J} (htt' : t ≠ t')
    (ht : t ∈ B.support) (ht' : t' ∈ B.support) {a : characterLattice S}
    (hta : restrictCharacter k K f hf.1.1 (P.root t) = a)
    (hta' : restrictCharacter k K f hf.1.1 (P.root t') = a)
    (h2a : 2 • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (haν : latticePairing S a ν ≠ 0) :
    P.IsOrthogonal t t' := by
  have hle : P.pairingIn ℤ t t' ≤ 0 := B.pairingIn_le_zero_of_ne htt' ht ht'
  have hnneg : ¬ P.pairingIn ℤ t t' < 0 := by
    intro hneg
    have hroot_ne : P.root t ≠ -P.root t' := by
      intro heq
      apply haν
      have h := congrArg (fun χ => latticePairing S (restrictCharacter k K f hf.1.1 χ) ν) heq
      simp only [map_neg, LinearMap.neg_apply, hta, hta'] at h
      omega
    obtain ⟨r, hr⟩ := P.root_add_root_mem_of_pairingIn_neg hneg hroot_ne
    apply h2a
    have hmem := restrictCharacter_root_mem k K f j hP hf hcent hT r
    rwa [hr, map_add, hta, hta', ← two_nsmul] at hmem
  have hzero : P.pairingIn ℤ t t' = 0 := le_antisymm hle (not_lt.mp hnneg)
  have hpair : P.pairing t t' = 0 := by
    have h := P.algebraMap_pairingIn ℤ t t'
    rw [hzero, map_zero] at h
    exact h.symm
  exact ⟨hpair, (P.pairing_eq_zero_iff' (i := t) (j := t')).mp hpair⟩


omit [P.IsReduced] [Finite J] in
include hP hcent hT in
/-- When `a` is a relative root and `2 • a` is not, an absolute root restricting to a positive
integral multiple of `a` restricts to `a` itself. -/
theorem eq_one_of_restrictCharacter_eq_nsmul [Mono (CommGroupScheme.groupHom f ≫ j).hom.hom.left]
    (hR : HasRelativeRootSystem (CommGroupScheme.groupHom f ≫ j)) {a : characterLattice S}
    (ha : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (h2a : 2 • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (t : J) {m : ℕ} (ht : restrictCharacter k K f hf.1.1 (P.root t) = m • a) : m = 1 := by
  have hm : m • a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j) := by
    rw [← ht]
    exact restrictCharacter_root_mem k K f j hP hf hcent hT t
  rcases hR.eq_one_or_two_of_nsmul_mem ha hm with h | h
  · exact h
  · subst h
    exact absurd hm h2a

section Pinning

variable [FiniteDimensional k K]
  (hGK : IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
  (hi : IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map j))

/-- The Galois-compatible pinning whose base is prescribed by the generic cocharacter `ν`
of the maximal split torus. -/
def fiberPinning : GaloisCompatiblePinningData k K G :=
  GaloisCompatiblePinningData.ofRegularCocharacter j hP (ν ≫ f)
    (regular_root_pairing k K f j hP hf hcent hT ν hν) hGK hT hi

local notation "D" => fiberPinning k K f j hP hf hcent hT ν hν hGK hi

/-- The roots of the pinning are those of `P`. -/
theorem fiberPinning_root (t : (D).pinning.rootIndex) :
    (D).pinning.rootDatum.root t = P.root t := rfl

/-- The base of the pinning is the one prescribed by `ν ≫ f`. -/
theorem fiberPinning_support :
    (D).pinning.base.support = (IsRootDatumOf.regularCocharacterBase k K (P := P)
      (cocharacterLattice.baseChange bK T (ν ≫ f))
      (regular_root_pairing k K f j hP hf hcent hT ν hν)).support := rfl

/-- The simple roots of the pinning whose restriction to the split torus is `a`. -/
def fiberSet (a : characterLattice S) : Set (D).pinning.base.support :=
  {t | restrictCharacter k K f hf.1.1 ((D).pinning.rootDatum.root t) = a}

/-- Membership in the fiber is the restriction condition used by the root-group coordinates. -/
theorem mem_fiberSet_iff (a : characterLattice S) (t : (D).pinning.base.support) :
    t ∈ fiberSet k K f j hP hf hcent hT ν hν hGK hi a ↔
      CategoryTheory.Functor.map (CommGroupScheme.baseChange bK) f ≫
          (D).pinning.rootDatum.root t = characterLattice.baseChange bK S a :=
  restrictCharacter_eq_iff k K f hf.1.1 _ a

/-- The fiber is stable under the Galois action on the simple roots. -/
theorem fiberSet_galois (a : characterLattice S) (σ : K ≃ₐ[k] K)
    (t : (D).pinning.base.support) :
    t ∈ fiberSet k K f j hP hf hcent hT ν hν hGK hi a ↔
      (D).action σ t ∈ fiberSet k K f j hP hf hcent hT ν hν hGK hi a := by
  change restrictCharacter k K f hf.1.1 (P.root (show J from t.1)) = a ↔
    restrictCharacter k K f hf.1.1
      (P.root (IsRootDatumOf.descendedRegularCocharacterSimpleAction k K j hP (ν ≫ f)
        (regular_root_pairing k K f j hP hf hcent hT ν hν) σ t : J)) = a
  rw [IsRootDatumOf.descendedRegularCocharacterSimpleAction_root,
    restrictCharacter_galois]

/-- Distinct members of the fiber of a simple relative root `a` with `2 • a` not a relative
root are orthogonal. -/
theorem fiberSet_isOrthogonal {a : characterLattice S}
    (ha : a ∈ simpleRelativeRoots (CommGroupScheme.groupHom f ≫ j) ν)
    (h2a : 2 • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j)) :
    ∀ t ∈ fiberSet k K f j hP hf hcent hT ν hν hGK hi a,
      ∀ t' ∈ fiberSet k K f j hP hf hcent hT ν hν hGK hi a, t ≠ t' →
        (D).pinning.rootDatum.IsOrthogonal t t' := by
  intro t ht t' ht' htt'
  exact isOrthogonal_of_restrictCharacter_eq k K f j hP hf hcent hT ν (D).pinning.base
    (fun h => htt' (Subtype.ext h)) t.2 t'.2 ht ht' h2a (ha.1.2).ne'

/-- Every absolute root restricting to a simple relative root `a` is a member of the
fiber. -/
theorem exists_mem_fiberSet {a : characterLattice S}
    (ha : a ∈ simpleRelativeRoots (CommGroupScheme.groupHom f ≫ j) ν)
    (t : J) (ht : restrictCharacter k K f hf.1.1 (P.root t) = a) :
    ∃ s ∈ fiberSet k K f j hP hf hcent hT ν hν hGK hi a, s.1 = t :=
  ⟨⟨t, simpleRootFiber_mem_base k K f j hP hf hcent hT ν hν ha t ht⟩, ht, rfl⟩

/-- The fiber of a simple relative root is nonempty. -/
theorem fiberSet_nonempty {a : characterLattice S}
    (ha : a ∈ simpleRelativeRoots (CommGroupScheme.groupHom f ≫ j) ν) :
    (fiberSet k K f j hP hf hcent hT ν hν hGK hi a).Nonempty := by
  obtain ⟨β, hβ⟩ := rootRestrictionFiber_nonempty k K j f hf.1.1 hT ⟨a, ha.1.1⟩
  obtain ⟨t, ht⟩ : β.val ∈ Set.range P.root := by
    rw [hP.2.1]
    exact β.property
  have hta : restrictCharacter k K f hf.1.1 (P.root t) = a := by
    rw [restrictCharacter_eq_iff, ht]
    exact hβ
  obtain ⟨s, hs, -⟩ := exists_mem_fiberSet k K f j hP hf hcent hT ν hν hGK hi ha t hta
  exact ⟨s, hs⟩


section Field

variable [IsGalois k K] (hjc : IsClosedSubgroup j)
  {a : characterLattice S} (ha : a ∈ simpleRelativeRoots (CommGroupScheme.groupHom f ≫ j) ν)

attribute [local instance] rootsGaloisAction

omit [LocallyOfFiniteType G.X.hom] [IsAffineHom T.toGrp.X.hom]
  [LocallyOfFiniteType T.toGrp.X.hom] [Finite J] [P.IsReduced] [FiniteDimensional k K]
  [IsGalois k K] in
include hP in
/-- The roots of `P` are actual roots of `j_K`. -/
theorem root_mem_roots (t : J) : P.root t ∈ roots (T := T_K) (G := G_K) j_K := by
  rw [← hP.2.1]
  exact Set.mem_range_self t

/-- An absolute root index as an element of the actual root set. -/
def rootOf (t : J) : roots (T := T_K) (G := G_K) j_K :=
  ⟨P.root t, root_mem_roots k K j hP t⟩

omit [IsGalois k K] in
/-- Members of the fiber give actual roots in the Library restriction fiber of `a`. -/
theorem rootOf_mem_restrictionFiber (t : (D).pinning.base.support)
    (ht : t ∈ fiberSet k K f j hP hf hcent hT ν hν hGK hi a) :
    rootOf k K j hP t.1 ∈ rootRestrictionFiber k K j f a :=
  (mem_fiberSet_iff k K f j hP hf hcent hT ν hν hGK hi a t).mp ht

/-- A chosen base point of the fiber of the simple relative root `a`. -/
def basePoint : (D).pinning.base.support :=
  (fiberSet_nonempty k K f j hP hf hcent hT ν hν hGK hi ha).some

omit [IsGalois k K] in
/-- The base point lies in the fiber. -/
theorem basePoint_mem :
    basePoint k K f j hP hf hcent hT ν hν hGK hi ha ∈
      fiberSet k K f j hP hf hcent hT ν hν hGK hi a :=
  (fiberSet_nonempty k K f j hP hf hcent hT ν hν hGK hi ha).some_mem

local notation "t₀" => basePoint k K f j hP hf hcent hT ν hν hGK hi ha

/-- The absolute root of the base point. -/
def baseRoot : roots (T := T_K) (G := G_K) j_K :=
  rootOf k K j hP (basePoint k K f j hP hf hcent hT ν hν hGK hi ha).val

local notation "β₀" => baseRoot k K f j hP hf hcent hT ν hν hGK hi ha

/-- The field of the fiber: the fixed field of the stabilizer of the base root. -/
abbrev fiberField : IntermediateField k K := rootOrbitField k K j β₀

include hjc in
/-- The fiber is one Galois orbit. -/
theorem baseRoot_orbit :
    MulAction.orbit (K ≃ₐ[k] K) β₀ = rootRestrictionFiber k K j f a :=
  rootOrbit_eq_restrictionFiber_of_torusCentralizer k K f j hf hjc hcent hT hP a
    (rootOf_mem_restrictionFiber k K f j hP hf hcent hT ν hν hGK hi t₀
      (basePoint_mem k K f j hP hf hcent hT ν hν hGK hi ha))

/-- The embedding of the fiber field attached to each member of the fiber; members outside
the fiber get the inclusion. -/
def fiberEmbedding (t : (D).pinning.base.support) :
    fiberField k K f j hP hf hcent hT ν hν hGK hi ha →ₐ[k] K :=
  open Classical in
  if h : t ∈ fiberSet k K f j hP hf hcent hT ν hν hGK hi a then
    rootRestrictionFiberEmbeddingEquiv k K f j a β₀
      (baseRoot_orbit k K f j hP hf hcent hT ν hν hGK hi hjc ha)
      ⟨rootOf k K j hP t.1, rootOf_mem_restrictionFiber k K f j hP hf hcent hT ν hν hGK hi t h⟩
  else (fiberField k K f j hP hf hcent hT ν hν hGK hi ha).val

/-- On the fiber, the embedding corresponds to the member's actual root. -/
theorem fiberEmbedding_symm (t : (D).pinning.base.support)
    (h : t ∈ fiberSet k K f j hP hf hcent hT ν hν hGK hi a) :
    (((rootRestrictionFiberEmbeddingEquiv k K f j a β₀
      (baseRoot_orbit k K f j hP hf hcent hT ν hν hGK hi hjc ha)).symm
        (fiberEmbedding k K f j hP hf hcent hT ν hν hGK hi hjc ha t) :
          roots (T := T_K) (G := G_K) j_K)) = rootOf k K j hP t.1 := by
  unfold fiberEmbedding
  rw [dite_eq_left_of_eq_true (eq_true h), Equiv.symm_apply_apply]

/-- The embeddings are Galois equivariant on the fiber. -/
theorem fiberEmbedding_galois (σ : K ≃ₐ[k] K) (t : (D).pinning.base.support)
    (ht : t ∈ fiberSet k K f j hP hf hcent hT ν hν hGK hi a) :
    fiberEmbedding k K f j hP hf hcent hT ν hν hGK hi hjc ha ((D).action σ t) =
      σ.toAlgHom.comp (fiberEmbedding k K f j hP hf hcent hT ν hν hGK hi hjc ha t) := by
  have hσt := (fiberSet_galois k K f j hP hf hcent hT ν hν hGK hi a σ t).mp ht
  apply (rootRestrictionFiberEmbeddingEquiv k K f j a β₀
    (baseRoot_orbit k K f j hP hf hcent hT ν hν hGK hi hjc ha)).symm.injective
  apply Subtype.ext
  rw [rootRestrictionFiberEmbeddingEquiv_symm_comp,
    fiberEmbedding_symm k K f j hP hf hcent hT ν hν hGK hi hjc ha _ hσt,
    fiberEmbedding_symm k K f j hP hf hcent hT ν hν hGK hi hjc ha _ ht]
  apply Subtype.ext
  change P.root (IsRootDatumOf.descendedRegularCocharacterSimpleAction k K j hP (ν ≫ f)
      (regular_root_pairing k K f j hP hf hcent hT ν hν) σ t : J) =
    characterLattice.galoisRepresentation k K T σ (P.root t.1)
  exact IsRootDatumOf.descendedRegularCocharacterSimpleAction_root k K j hP _ _ σ t

/-- The base point corresponds to the inclusion of the fiber field. -/
theorem fiberEmbedding_basePoint (x : fiberField k K f j hP hf hcent hT ν hν hGK hi ha) :
    fiberEmbedding k K f j hP hf hcent hT ν hν hGK hi hjc ha t₀ x = x := by
  have h1 : fiberEmbedding k K f j hP hf hcent hT ν hν hGK hi hjc ha t₀ =
      Langlands.Algebra.FiniteGaloisOrbits.restriction k K
        (MulAction.stabilizer (K ≃ₐ[k] K) β₀) 1 := by
    apply (rootRestrictionFiberEmbeddingEquiv k K f j a β₀
      (baseRoot_orbit k K f j hP hf hcent hT ν hν hGK hi hjc ha)).symm.injective
    apply Subtype.ext
    rw [fiberEmbedding_symm k K f j hP hf hcent hT ν hν hGK hi hjc ha _
        (basePoint_mem k K f j hP hf hcent hT ν hν hGK hi ha),
      rootRestrictionFiberEmbeddingEquiv_symm_val]
    change _ = ((Langlands.Algebra.FiniteGaloisOrbits.orbitEmbeddingEquiv k K β₀).symm
      (Langlands.Algebra.FiniteGaloisOrbits.restriction k K
        (MulAction.stabilizer (K ≃ₐ[k] K) β₀) 1) : roots (T := T_K) (G := G_K) j_K)
    rw [Langlands.Algebra.FiniteGaloisOrbits.orbitEmbeddingEquiv_symm_restriction, one_smul]
    rfl
  rw [h1]
  rfl

/-- Every Galois-equivariant family of scalars on the fiber comes from one element of the
fiber field through the embeddings. -/
theorem exists_eq_fiberEmbedding (c : (D).pinning.base.support → K)
    (hc : ∀ (σ : K ≃ₐ[k] K) (t : (D).pinning.base.support),
      t ∈ fiberSet k K f j hP hf hcent hT ν hν hGK hi a → c ((D).action σ t) = σ (c t)) :
    ∃ x : fiberField k K f j hP hf hcent hT ν hν hGK hi ha,
      ∀ t ∈ fiberSet k K f j hP hf hcent hT ν hν hGK hi a,
        c t = fiberEmbedding k K f j hP hf hcent hT ν hν hGK hi hjc ha t x := by
  have h0 := basePoint_mem k K f j hP hf hcent hT ν hν hGK hi ha
  have hact (σ : K ≃ₐ[k] K) (t : (D).pinning.base.support) :
      P.root (show J from ((D).action σ t).1) =
        characterLattice.galoisRepresentation k K T σ (P.root t.1) :=
    IsRootDatumOf.descendedRegularCocharacterSimpleAction_root k K j hP _ _ σ t
  have hmem : c t₀ ∈ fiberField k K f j hP hf hcent hT ν hν hGK hi ha := by
    rw [mem_rootOrbitField_iff]
    intro σ hσ
    have hfix : (D).action σ t₀ = t₀ := by
      apply Subtype.ext
      apply P.root.injective
      rw [hact]
      exact hσ
    rw [← hc σ t₀ h0, hfix]
  refine ⟨⟨c t₀, hmem⟩, fun t ht => ?_⟩
  have hin : rootOf k K j hP t.1 ∈ MulAction.orbit (K ≃ₐ[k] K) β₀ := by
    rw [baseRoot_orbit k K f j hP hf hcent hT ν hν hGK hi hjc ha]
    exact rootOf_mem_restrictionFiber k K f j hP hf hcent hT ν hν hGK hi t ht
  obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp hin
  have hσt : (D).action σ t₀ = t := by
    apply Subtype.ext
    apply P.root.injective
    rw [hact]
    exact congrArg Subtype.val hσ
  rw [← hσt, hc σ t₀ h0, fiberEmbedding_galois k K f j hP hf hcent hT ν hν hGK hi hjc ha σ t₀ h0]
  change σ (c t₀) = σ (fiberEmbedding k K f j hP hf hcent hT ν hν hGK hi hjc ha t₀ ⟨c t₀, hmem⟩)
  rw [fiberEmbedding_basePoint]

end Field

end Pinning

end Roots

end SimpleRootFiber

end Langlands.GroupScheme
