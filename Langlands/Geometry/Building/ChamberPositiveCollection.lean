import Langlands.Geometry.Building.ChamberFiltration
import Langlands.Geometry.Building.RankZeroAffineRootSystem
import Langlands.GroupScheme.Rational.RootRayDecomposition
import Langlands.GroupTheory.HeightCollection

/-! # Collection for positive chamber root groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

private theorem prod_ofFn_pairs {M : Type*} [Monoid M] {n : ℕ}
    (f : Fin (n * 2) → M) :
    (List.ofFn f).prod = (List.ofFn fun j : Fin n =>
      f (finProdFinEquiv (j, 0)) * f (finProdFinEquiv (j, 1))).prod := by
  rw [List.ofFn_mul, List.prod_flatten, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext j
  simp only [Function.comp_def, List.ofFn_succ, List.ofFn_zero,
    List.prod_cons, List.prod_nil, mul_one]
  congr 2 <;> apply Fin.ext <;>
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

private theorem range_orderedProduct_pairs {M : Type*} [Group M] {n : ℕ}
    (H : Fin (n * 2) → Subgroup M) (K : Fin n → Subgroup M)
    (h0 : ∀ j, H (finProdFinEquiv (j, 0)) = K j)
    (h1 : ∀ j, H (finProdFinEquiv (j, 1)) ≤ K j) :
    Set.range (RelativeRoot.CentralExtension.orderedProduct (fun l => (H l).subtype)) =
      Set.range (RelativeRoot.CentralExtension.orderedProduct (fun j => (K j).subtype)) := by
  classical
  ext g
  constructor
  · rintro ⟨t, rfl⟩
    let s : ∀ j, K j := fun j =>
      ⟨(t (finProdFinEquiv (j, 0)) : M) * (t (finProdFinEquiv (j, 1)) : M),
        (K j).mul_mem (h0 j ▸ (t (finProdFinEquiv (j, 0))).property)
          (h1 j (t (finProdFinEquiv (j, 1))).property)⟩
    refine ⟨s, ?_⟩
    exact (prod_ofFn_pairs (fun l => (t l : M))).symm
  · rintro ⟨s, rfl⟩
    let t : ∀ l, H l := fun l =>
      if h : (finProdFinEquiv.symm l).2 = 0 then
        ⟨(s (finProdFinEquiv.symm l).1 : M), by
          have he : finProdFinEquiv ((finProdFinEquiv.symm l).1, 0) = l := by
            rw [← h]
            exact finProdFinEquiv.apply_symm_apply l
          have hh := h0 (finProdFinEquiv.symm l).1
          rw [he] at hh
          exact hh.symm ▸ (s _).property⟩
      else 1
    refine ⟨t, ?_⟩
    unfold RelativeRoot.CentralExtension.orderedProduct
    rw [prod_ofFn_pairs]
    apply congrArg List.prod
    apply congrArg List.ofFn
    funext j
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [t, Equiv.symm_apply_apply, h10, dite_true, dite_false,
      Subgroup.subtype_apply, Subgroup.coe_one, mul_one]
    exact congrArg (fun p : Fin n × Fin 2 => (s p.1 : M))
      (finProdFinEquiv.symm_apply_apply (j, (0 : Fin 2)))

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [IsAffineHom G.X.hom]

/-- The apartment form respects positive integral multiplication of actual roots. -/
theorem rootForm_nsmul {a : characterLattice S} (ha : a ∈ relativeRoots i)
    (m : ℕ) (hma : m • a ∈ relativeRoots i) :
    rootForm i ⟨m • a, hma⟩ = (m : ℝ) • rootForm i ⟨a, ha⟩ := by
  apply LinearMap.ext
  intro v
  refine Submodule.Quotient.induction_on _ v fun w => ?_
  simp only [rootForm_mk, eval_eq_pair, TensorProduct.tmul_smul,
    map_nsmul, LinearMap.smul_apply, Nat.cast_smul_eq_nsmul]

namespace KPApartmentData

variable [Mono i.hom.hom.left] {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- AS2 and coroot integrality exclude actual positive root multiples above two. -/
theorem root_multiple_eq_one_or_two
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.extendedAffineRoots)
    (hderiv : AffineRootSystem.derivativeRoots D.extendedAffineRoots = Set.range (rootForm i))
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    {m : ℕ} (hm : 0 < m) (hma : m • a ∈ relativeRoots i) :
    m = 1 ∨ m = 2 := by
  have hroot (b : relativeRoots i) :
      ∃ ψ ∈ D.extendedAffineRoots, ψ.linear = rootForm i b := by
    apply AffineRootSystem.mem_derivativeRoots.mp
    rw [hderiv]
    exact Set.mem_range_self b
  obtain ⟨ψ, hψ, hψlin⟩ := hroot ⟨a, ha⟩
  obtain ⟨eta, heta, hetalin⟩ := hroot ⟨m • a, hma⟩
  obtain ⟨v, hv⟩ := hsys.exists_isCoroot eta heta
  obtain ⟨z, hz⟩ := hsys.coroot_integral ψ hψ eta heta v hv
  have heq : (m : ℝ) * (z : ℝ) = 2 := by
    rw [← hz, hψlin]
    change ((m : ℝ) • rootForm i ⟨a, ha⟩) v = 2
    rw [← rootForm_nsmul ha m hma, ← hetalin]
    exact hv.1
  have hInt : (m : ℤ) * z = 2 := by exact_mod_cast heq
  have hmInt : 0 < (m : ℤ) := by exact_mod_cast hm
  have hzpos : 0 < z := by nlinarith
  have hmle : (m : ℤ) ≤ 2 := by nlinarith
  omega

/-- Every positive actual root is an indivisible positive root or its double. -/
theorem exists_indivisiblePositiveRoot_eq_or_double
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.extendedAffineRoots)
    (hderiv : AffineRootSystem.derivativeRoots D.extendedAffineRoots = Set.range (rootForm i))
    (ν : cocharacterLattice S) {b : characterLattice S}
    (hb : b ∈ positiveRelativeRoots i ν) :
    ∃ a ∈ RelativeRoot.indivisiblePositiveRoots i ν, b = a ∨ b = 2 • a := by
  obtain ⟨a, ha, m, _, hm, hma⟩ :=
    RelativeRoot.exists_indivisiblePositiveRoot_ray i ν hb.1 hb.2
  refine ⟨a, ha, ?_⟩
  rcases D.root_multiple_eq_one_or_two hsys hderiv ha.1.1 hm (hma.symm ▸ hb.1) with h | h
  · left
    simpa only [h, one_smul] using hma.symm
  · right
    simpa only [h] using hma.symm

omit [Mono i.hom.hom.left] in
/-- Positive roots cannot be negative real multiples of one another. -/
theorem positiveRoots_nonopposite (ν : cocharacterLattice S)
    {a b : characterLattice S} (ha : a ∈ positiveRelativeRoots i ν)
    (hb : b ∈ positiveRelativeRoots i ν) :
    ∀ t : ℝ, 0 < t → ((1 : ℝ) ⊗ₜ[ℤ] b : Vstar S) ≠
      -(t • (1 : ℝ) ⊗ₜ[ℤ] a) := by
  intro t ht heq
  have h := congrArg (fun χ => pair S χ ((1 : ℝ) ⊗ₜ[ℤ] ν)) heq
  simp only [map_neg, map_smul, LinearMap.neg_apply, LinearMap.smul_apply,
    pair_tmul_tmul, smul_eq_mul, one_mul, mul_one] at h
  have haR : (0 : ℝ) < (latticePairing S a ν : ℝ) := by exact_mod_cast ha.2
  have hbR : (0 : ℝ) < (latticePairing S b ν : ℝ) := by exact_mod_cast hb.2
  nlinarith

omit [Mono i.hom.hom.left] in
/-- Positive integral combinations strictly increase both positive pairing heights. -/
theorem positiveRootCombination_height (ν : cocharacterLattice S)
    {a b : characterLattice S} (ha : a ∈ positiveRelativeRoots i ν)
    (hb : b ∈ positiveRelativeRoots i ν) {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hc : p • a + q • b ∈ relativeRoots i) :
    p • a + q • b ∈ positiveRelativeRoots i ν ∧
      max (latticePairing S a ν).toNat (latticePairing S b ν).toNat <
        (latticePairing S (p • a + q • b) ν).toNat := by
  have heval : latticePairing S (p • a + q • b) ν =
      (p : ℤ) * latticePairing S a ν + (q : ℤ) * latticePairing S b ν := by
    simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
  have haPos : 0 < latticePairing S a ν := ha.2
  have hbPos : 0 < latticePairing S b ν := hb.2
  have hp' : 1 ≤ (p : ℤ) := by omega
  have hq' : 1 ≤ (q : ℤ) := by omega
  have hca : latticePairing S a ν < latticePairing S (p • a + q • b) ν := by
    rw [heval]
    nlinarith [ha.2, hb.2]
  have hcb : latticePairing S b ν < latticePairing S (p • a + q • b) ν := by
    rw [heval]
    nlinarith [ha.2, hb.2]
  exact ⟨⟨hc, lt_trans ha.2 hca⟩, by omega⟩

/-- V3 for the actual subgroup filtrations, with the closure notation removed. -/
theorem filtration_commutator_le (x : D.Apartment)
    {a b : characterLattice S} (ha : a ∈ relativeRoots i) (hb : b ∈ relativeRoots i)
    (hnon : ∀ t : ℝ, 0 < t → ((1 : ℝ) ⊗ₜ[ℤ] b : Vstar S) ≠
      -(t • (1 : ℝ) ⊗ₜ[ℤ] a)) (r s : ℝ) :
    ⁅D.filtration x a r, D.filtration x b s⁆ ≤
      ⨆ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q)
        (_ : p • a + q • b ∈ relativeRoots i),
        D.filtration x (p • a + q • b) (p * r + q * s) := by
  have h := x.isValuation.commutator a ha b hb hnon r s
  change ⁅Subgroup.closure (D.filtration x a r : Set (rationalPoints G)),
    Subgroup.closure (D.filtration x b s : Set (rationalPoints G))⁆ ≤
      Subgroup.closure (⋃ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q)
        (_ : p • a + q • b ∈ relativeRoots i),
        (D.filtration x (p • a + q • b) (p * r + q * s) : Set (rationalPoints G))) at h
  simpa only [Subgroup.closure_iUnion, Subgroup.closure_eq] using h

private theorem exists_filtration_of_mem_plus {x : D.Apartment}
    {a : characterLattice S} {r : ℝ} {g : rationalPoints G}
    (hg : g ∈ D.filtrationPlus x a r) :
    ∃ s : ℝ, r < s ∧ g ∈ D.filtration x a s := by
  have : Nonempty (Set.Ioi r) := ⟨⟨r + 1, lt_add_one r⟩⟩
  have hdir : Directed (· ≤ ·) (fun s : Set.Ioi r => D.filtration x a s) := by
    intro s t
    exact ⟨⟨min s t, Set.mem_Ioi.2 (lt_min s.2 t.2)⟩,
      filtration_antitone x a (min_le_left _ _),
      filtration_antitone x a (min_le_right _ _)⟩
  obtain ⟨s, hs⟩ := (Subgroup.mem_iSup_of_directed hdir).mp hg
  exact ⟨s, s.2, hs⟩

/-- Both zero-depth root groups satisfy the strictly increasing positive-height bound. -/
theorem chamberRootGroup_commutator_height (x : D.Apartment) (strict : Bool)
    (ν : cocharacterLattice S) {a b : characterLattice S}
    (ha : a ∈ positiveRelativeRoots i ν) (hb : b ∈ positiveRelativeRoots i ν) :
    ⁅D.chamberRootGroup x strict a, D.chamberRootGroup x strict b⁆ ≤
      ⨆ c : positiveRelativeRoots i ν,
        ⨆ (_ : max (latticePairing S a ν).toNat (latticePairing S b ν).toNat <
          (latticePairing S c ν).toNat), D.chamberRootGroup x strict c := by
  have hnon := positiveRoots_nonopposite ν ha hb
  cases strict with
  | false =>
    change ⁅D.filtration x a 0, D.filtration x b 0⁆ ≤ _
    refine (D.filtration_commutator_le x ha.1 hb.1 hnon 0 0).trans ?_
    refine iSup_le fun p => iSup_le fun q => iSup_le fun hp =>
      iSup_le fun hq => iSup_le fun hc => ?_
    obtain ⟨hcpos, hheight⟩ := positiveRootCombination_height ν ha hb hp hq hc
    simp only [mul_zero, add_zero]
    exact le_iSup_of_le (⟨p • a + q • b, hcpos⟩ : positiveRelativeRoots i ν)
      (le_iSup_of_le hheight le_rfl)
  | true =>
    apply Subgroup.commutator_le.mpr
    intro g hg h hh
    obtain ⟨r, hr, hgr⟩ := D.exists_filtration_of_mem_plus hg
    obtain ⟨s, hs, hhs⟩ := D.exists_filtration_of_mem_plus hh
    have hbound := D.filtration_commutator_le x ha.1 hb.1 hnon r s
    have hle : (⨆ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q)
        (_ : p • a + q • b ∈ relativeRoots i),
        D.filtration x (p • a + q • b) (p * r + q * s)) ≤
        ⨆ c : positiveRelativeRoots i ν,
          ⨆ (_ : max (latticePairing S a ν).toNat (latticePairing S b ν).toNat <
            (latticePairing S c ν).toNat), D.chamberRootGroup x true c := by
      refine iSup_le fun p => iSup_le fun q => iSup_le fun hp =>
        iSup_le fun hq => iSup_le fun hc => ?_
      obtain ⟨hcpos, hheight⟩ := positiveRootCombination_height ν ha hb hp hq hc
      have hdepth : (0 : ℝ) < (p : ℝ) * r + (q : ℝ) * s := by
        exact add_pos (mul_pos (by exact_mod_cast hp) hr) (mul_pos (by exact_mod_cast hq) hs)
      exact le_iSup_of_le ⟨p • a + q • b, hcpos⟩
        (le_iSup_of_le hheight (D.filtration_le_filtrationPlus x _ hdepth))
    exact (hbound.trans hle) (Subgroup.commutator_mem_commutator hgr hhs)

/-- Any complete finite enumeration of positive roots admits collection in its given order. -/
theorem range_orderedPositiveRootGroupProduct_eq_iSup (x : D.Apartment) (strict : Bool)
    (ν : cocharacterLattice S) {n : ℕ} (a : Fin n → characterLattice S)
    (hrange : Set.range a = positiveRelativeRoots i ν) :
    Set.range (RelativeRoot.CentralExtension.orderedProduct
      (fun j => (D.chamberRootGroup x strict (a j)).subtype)) =
      ((⨆ j, D.chamberRootGroup x strict (a j) : Subgroup (rationalPoints G)) :
        Set (rationalPoints G)) := by
  apply Langlands.GroupTheory.HeightCollection.range_orderedProduct_eq_iSup
    (w := fun j => (latticePairing S (a j) ν).toNat)
  intro j k
  have hj : a j ∈ positiveRelativeRoots i ν := hrange ▸ Set.mem_range_self j
  have hk : a k ∈ positiveRelativeRoots i ν := hrange ▸ Set.mem_range_self k
  refine (D.chamberRootGroup_commutator_height x strict ν hj hk).trans ?_
  refine iSup_le fun c => iSup_le fun hc => ?_
  obtain ⟨l, hl⟩ := (show (c : characterLattice S) ∈ Set.range a by
    rw [hrange]
    exact c.2)
  exact le_iSup_of_le l (le_iSup_of_le (hl.symm ▸ hc) (by rw [hl]))

/-- The prescribed primitive-root product is the subgroup generated by all
positive root groups, at either zero depth and at every apartment point. -/
theorem range_orderedIndivisiblePositiveRootGroupProduct_eq_iSup
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.extendedAffineRoots)
    (hderiv : AffineRootSystem.derivativeRoots D.extendedAffineRoots = Set.range (rootForm i))
    (x : D.Apartment) (strict : Bool) (ν : cocharacterLattice S)
    {n : ℕ} (a : Fin n → characterLattice S)
    (hrange : Set.range a = RelativeRoot.indivisiblePositiveRoots i ν) :
    Set.range (RelativeRoot.CentralExtension.orderedProduct
      (fun j => (D.chamberRootGroup x strict (a j)).subtype)) =
      ((⨆ b : positiveRelativeRoots i ν, D.chamberRootGroup x strict b :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) := by
  classical
  let c : Fin (n * 2) → characterLattice S := fun l =>
    if (finProdFinEquiv.symm l).2 = 0 then a (finProdFinEquiv.symm l).1
      else 2 • a (finProdFinEquiv.symm l).1
  let H : Fin (n * 2) → Subgroup (rationalPoints G) := fun l =>
    if c l ∈ relativeRoots i then D.chamberRootGroup x strict (c l) else ⊥
  have ha (j : Fin n) : a j ∈ RelativeRoot.indivisiblePositiveRoots i ν :=
    hrange ▸ Set.mem_range_self j
  have hc0 (j : Fin n) : c (finProdFinEquiv (j, 0)) = a j := by
    simp only [c, Equiv.symm_apply_apply, ↓reduceIte]
  have hc1 (j : Fin n) : c (finProdFinEquiv (j, 1)) = 2 • a j := by
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [c, Equiv.symm_apply_apply, ite_eq_right h10]
  have hpos (l : Fin (n * 2)) (hl : c l ∈ relativeRoots i) :
      c l ∈ positiveRelativeRoots i ν := by
    refine ⟨hl, ?_⟩
    dsimp only [c]
    split_ifs
    · exact (ha _).2
    · have hp := (ha (finProdFinEquiv.symm l).1).2
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      omega
  have hcover (b : positiveRelativeRoots i ν) : ∃ l, c l = b := by
    obtain ⟨d, hd, hb⟩ := D.exists_indivisiblePositiveRoot_eq_or_double hsys hderiv ν b.2
    obtain ⟨j, hj⟩ := (show d ∈ Set.range a by rw [hrange]; exact hd)
    rcases hb with hb | hb
    · exact ⟨finProdFinEquiv (j, 0), (hc0 j).trans (hj.trans hb.symm)⟩
    · exact ⟨finProdFinEquiv (j, 1),
        (hc1 j).trans ((congrArg (2 • ·) hj).trans hb.symm)⟩
  have hcollect :
      Set.range (RelativeRoot.CentralExtension.orderedProduct (fun l => (H l).subtype)) =
        ((⨆ l, H l : Subgroup (rationalPoints G)) : Set (rationalPoints G)) := by
    apply Langlands.GroupTheory.HeightCollection.range_orderedProduct_eq_iSup
      (w := fun l => (latticePairing S (c l) ν).toNat)
    intro j k
    by_cases hj : c j ∈ relativeRoots i
    · by_cases hk : c k ∈ relativeRoots i
      · have hjH : H j = D.chamberRootGroup x strict (c j) := ite_eq_left hj
        have hkH : H k = D.chamberRootGroup x strict (c k) := ite_eq_left hk
        rw [hjH, hkH]
        refine (D.chamberRootGroup_commutator_height x strict ν (hpos j hj)
          (hpos k hk)).trans ?_
        refine iSup_le fun b => iSup_le fun hb => ?_
        obtain ⟨l, hl⟩ := hcover b
        have hroot : c l ∈ relativeRoots i := hl.symm ▸ b.2.1
        exact le_iSup_of_le l (le_iSup_of_le (hl.symm ▸ hb)
          (by dsimp only [H]; rw [ite_eq_left hroot, hl]))
      · simp only [H, ite_eq_right hk, Subgroup.commutator_bot_right, bot_le]
    · simp only [H, ite_eq_right hj, Subgroup.commutator_bot_left, bot_le]
  have h0 (j : Fin n) :
      H (finProdFinEquiv (j, 0)) = D.chamberRootGroup x strict (a j) := by
    simp only [H, hc0, ite_eq_left (ha j).1.1]
  have h1 (j : Fin n) :
      H (finProdFinEquiv (j, 1)) ≤ D.chamberRootGroup x strict (a j) := by
    simp only [H, hc1]
    split_ifs with h2a
    · cases strict with
      | false => exact D.filtration_double_le x (ha j).1.1 h2a
      | true => exact D.filtrationPlus_double_le x (ha j).1.1 h2a
    · exact bot_le
  rw [← range_orderedProduct_pairs H _ h0 h1, hcollect]
  apply congrArg (fun K : Subgroup (rationalPoints G) => (K : Set (rationalPoints G)))
  apply le_antisymm
  · refine iSup_le fun l => ?_
    dsimp only [H]
    split_ifs with hl
    · exact le_iSup (fun b : positiveRelativeRoots i ν =>
        D.chamberRootGroup x strict b) ⟨c l, hpos l hl⟩
    · exact bot_le
  · refine iSup_le fun b => ?_
    obtain ⟨l, hl⟩ := hcover b
    have hroot : c l ∈ relativeRoots i := hl.symm ▸ b.2.1
    exact le_iSup_of_le l (by dsimp only [H]; rw [ite_eq_left hroot, hl])

/-- Collection for the original doubled-root blocks, with their prescribed order. -/
theorem range_orderedPositiveChamberBlockProduct_eq_iSup
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.extendedAffineRoots)
    (hderiv : AffineRootSystem.derivativeRoots D.extendedAffineRoots = Set.range (rootForm i))
    (x : D.Apartment) (strict : Bool) (ν : cocharacterLattice S)
    {n : ℕ} (a : Fin n → characterLattice S)
    (hrange : Set.range a = RelativeRoot.indivisiblePositiveRoots i ν) :
    Set.range (D.orderedChamberBlockProduct x strict a) =
      ((⨆ b : positiveRelativeRoots i ν, D.chamberRootGroup x strict b :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) := by
  rw [← D.range_orderedIndivisiblePositiveRootGroupProduct_eq_iSup
    hsys hderiv x strict ν a hrange]
  have ha (j : Fin n) : a j ∈ relativeRoots i :=
    (show a j ∈ RelativeRoot.indivisiblePositiveRoots i ν from
      hrange ▸ Set.mem_range_self j).1.1
  ext g
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨fun j => D.chamberRootBlockEquiv x strict (ha j) (t j), ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨fun j => (D.chamberRootBlockEquiv x strict (ha j)).symm (t j), ht⟩

/-- The generated-positive-root-group form of collection. -/
theorem range_orderedPositiveChamberBlockProduct_eq_closure
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.extendedAffineRoots)
    (hderiv : AffineRootSystem.derivativeRoots D.extendedAffineRoots = Set.range (rootForm i))
    (x : D.Apartment) (strict : Bool) (ν : cocharacterLattice S)
    {n : ℕ} (a : Fin n → characterLattice S)
    (hrange : Set.range a = RelativeRoot.indivisiblePositiveRoots i ν) :
    Set.range (D.orderedChamberBlockProduct x strict a) =
      (Subgroup.closure (⋃ b : positiveRelativeRoots i ν,
        (D.chamberRootGroup x strict b : Set (rationalPoints G))) :
        Set (rationalPoints G)) := by
  simpa only [Subgroup.closure_iUnion, Subgroup.closure_eq] using
    D.range_orderedPositiveChamberBlockProduct_eq_iSup hsys hderiv x strict ν a hrange

/-- Depth zero collection as the closure of the actual positive filtrations. -/
theorem range_orderedPositiveChamberBlockProduct_zero_eq_closure
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.extendedAffineRoots)
    (hderiv : AffineRootSystem.derivativeRoots D.extendedAffineRoots = Set.range (rootForm i))
    (x : D.Apartment) (ν : cocharacterLattice S)
    {n : ℕ} (a : Fin n → characterLattice S)
    (hrange : Set.range a = RelativeRoot.indivisiblePositiveRoots i ν) :
    Set.range (D.orderedChamberBlockProduct x false a) =
      (Subgroup.closure (⋃ b : positiveRelativeRoots i ν,
        (D.filtration x b 0 : Set (rationalPoints G))) : Set (rationalPoints G)) :=
  D.range_orderedPositiveChamberBlockProduct_eq_closure hsys hderiv x false ν a hrange

/-- The original ordered positive block range, packaged as a subgroup. -/
def positiveChamberProductSubgroup
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.extendedAffineRoots)
    (hderiv : AffineRootSystem.derivativeRoots D.extendedAffineRoots = Set.range (rootForm i))
    (x : D.Apartment) (strict : Bool) (ν : cocharacterLattice S)
    {n : ℕ} (a : Fin n → characterLattice S)
    (hrange : Set.range a = RelativeRoot.indivisiblePositiveRoots i ν) :
    Subgroup (rationalPoints G) :=
  (⨆ b : positiveRelativeRoots i ν, D.chamberRootGroup x strict b).copy _
    (D.range_orderedPositiveChamberBlockProduct_eq_iSup hsys hderiv x strict ν a hrange)

@[simp]
theorem mem_positiveChamberProductSubgroup
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.extendedAffineRoots)
    (hderiv : AffineRootSystem.derivativeRoots D.extendedAffineRoots = Set.range (rootForm i))
    (x : D.Apartment) (strict : Bool) (ν : cocharacterLattice S)
    {n : ℕ} (a : Fin n → characterLattice S)
    (hrange : Set.range a = RelativeRoot.indivisiblePositiveRoots i ν)
    (g : rationalPoints G) :
    g ∈ D.positiveChamberProductSubgroup hsys hderiv x strict ν a hrange ↔
      ∃ t, D.orderedChamberBlockProduct x strict a t = g :=
  Iff.rfl

theorem positiveChamberProductSubgroup_eq_iSup
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.extendedAffineRoots)
    (hderiv : AffineRootSystem.derivativeRoots D.extendedAffineRoots = Set.range (rootForm i))
    (x : D.Apartment) (strict : Bool) (ν : cocharacterLattice S)
    {n : ℕ} (a : Fin n → characterLattice S)
    (hrange : Set.range a = RelativeRoot.indivisiblePositiveRoots i ν) :
    D.positiveChamberProductSubgroup hsys hderiv x strict ν a hrange =
      ⨆ b : positiveRelativeRoots i ν, D.chamberRootGroup x strict b :=
  Subgroup.copy_eq _ _ _

/-- The range is independent of the supplied enumeration, including repetitions. -/
theorem range_orderedPositiveChamberBlockProduct_order_independent
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.extendedAffineRoots)
    (hderiv : AffineRootSystem.derivativeRoots D.extendedAffineRoots = Set.range (rootForm i))
    (x : D.Apartment) (strict : Bool) (ν : cocharacterLattice S)
    {n m : ℕ} (a : Fin n → characterLattice S) (b : Fin m → characterLattice S)
    (ha : Set.range a = RelativeRoot.indivisiblePositiveRoots i ν)
    (hb : Set.range b = RelativeRoot.indivisiblePositiveRoots i ν) :
    Set.range (D.orderedChamberBlockProduct x strict a) =
      Set.range (D.orderedChamberBlockProduct x strict b) := by
  rw [D.range_orderedPositiveChamberBlockProduct_eq_iSup hsys hderiv x strict ν a ha,
    D.range_orderedPositiveChamberBlockProduct_eq_iSup hsys hderiv x strict ν b hb]

end KPApartmentData
end Langlands.Geometry.Building
