import Langlands.Geometry.Building.MoyPrasadOrderedEmbedding
import Langlands.Geometry.Building.ChamberPositiveCollection

/-! # Collection of original constant-depth blocks within one sign -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- Collect adjacent pairs as elements of their actual set products,
without assuming that either member of the pair contains the other. -/
theorem range_orderedSubgroupPairsProduct {M : Type*} [Group M] {n : ℕ}
    (H : Fin (n * 2) → Subgroup M) (A B : Fin n → Subgroup M)
    (h0 : ∀ j, H (finProdFinEquiv (j, 0)) = A j)
    (h1 : ∀ j, H (finProdFinEquiv (j, 1)) = B j) :
    Set.range (RelativeRoot.CentralExtension.orderedProduct (fun l => (H l).subtype)) =
      Set.range (fun u : ∀ j, (A j : Set M) * (B j : Set M) =>
        (List.ofFn fun j => (u j : M)).prod) := by
  classical
  ext g
  constructor
  · rintro ⟨t, rfl⟩
    let s : ∀ j, (A j : Set M) * (B j : Set M) := fun j =>
      ⟨(t (finProdFinEquiv (j, 0)) : M) * (t (finProdFinEquiv (j, 1)) : M),
        Set.mul_mem_mul (h0 j ▸ (t (finProdFinEquiv (j, 0))).property)
          (h1 j ▸ (t (finProdFinEquiv (j, 1))).property)⟩
    exact ⟨s, (prod_ofFn_pairs (fun l => (t l : M))).symm⟩
  · rintro ⟨s, rfl⟩
    have hex (j : Fin n) : ∃ uv : A j × B j, (uv.1 : M) * (uv.2 : M) = s j := by
      obtain ⟨v, hv, w, hw, heq⟩ := (s j).property
      exact ⟨(⟨v, hv⟩, ⟨w, hw⟩), heq⟩
    choose uv huv using hex
    let t : ∀ l, H l := fun l =>
      if h : (finProdFinEquiv.symm l).2 = 0 then
        ⟨(uv (finProdFinEquiv.symm l).1).1, by
          have he : finProdFinEquiv ((finProdFinEquiv.symm l).1, 0) = l := by
            rw [← h]
            exact finProdFinEquiv.apply_symm_apply l
          have hh := h0 (finProdFinEquiv.symm l).1
          rw [he] at hh
          exact hh.symm ▸ (uv _).1.property⟩
      else
        ⟨(uv (finProdFinEquiv.symm l).1).2, by
          have h' : (finProdFinEquiv.symm l).2 = 1 := by omega
          have he : finProdFinEquiv ((finProdFinEquiv.symm l).1, 1) = l := by
            rw [← h']
            exact finProdFinEquiv.apply_symm_apply l
          have hh := h1 (finProdFinEquiv.symm l).1
          rw [he] at hh
          exact hh.symm ▸ (uv _).2.property⟩
    refine ⟨t, ?_⟩
    unfold RelativeRoot.CentralExtension.orderedProduct
    rw [prod_ofFn_pairs]
    apply congrArg List.prod
    apply congrArg List.ofFn
    funext j
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [t, Equiv.symm_apply_apply, dite_true, dite_false, h10,
      Subgroup.subtype_apply]
    exact (congrArg₂
      (fun p q : Fin n × Fin 2 => ((uv p.1).1 : M) * ((uv q.1).2 : M))
      (finProdFinEquiv.symm_apply_apply (j, (0 : Fin 2)))
      (finProdFinEquiv.symm_apply_apply (j, (1 : Fin 2)))).trans (huv j)

namespace KPApartmentData

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- At a constant nonnegative depth, V3 still strictly increases positive
root heights, while the commutator depth remains at least the same depth. -/
theorem filtration_commutator_positive_height (x : D.Apartment) (r : ℝ) (hr : 0 ≤ r)
    (ν : cocharacterLattice S) {a b : characterLattice S}
    (ha : a ∈ positiveRelativeRoots i ν) (hb : b ∈ positiveRelativeRoots i ν) :
    ⁅D.filtration x a r, D.filtration x b r⁆ ≤
      ⨆ c : positiveRelativeRoots i ν,
        ⨆ (_ : max (latticePairing S a ν).toNat (latticePairing S b ν).toNat <
          (latticePairing S c ν).toNat), D.filtration x c r := by
  refine (D.filtration_commutator_le x ha.1 hb.1
    (positiveRoots_nonopposite ν ha hb) r r).trans ?_
  refine iSup_le fun p => iSup_le fun q => iSup_le fun hp =>
    iSup_le fun hq => iSup_le fun hc => ?_
  obtain ⟨hcpos, hheight⟩ := positiveRootCombination_height ν ha hb hp hq hc
  have hdepth : r ≤ (p : ℝ) * r + (q : ℝ) * r := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hpbound := mul_le_mul_of_nonneg_right hp1 hr
    have hqbound := mul_nonneg (Nat.cast_nonneg (α := ℝ) q) hr
    linarith
  exact le_iSup_of_le (⟨p • a + q • b, hcpos⟩ : positiveRelativeRoots i ν)
    (le_iSup_of_le hheight (D.filtration_antitone x _ hdepth))

/-- Every complete ordering of the indivisible positive roots collects
the unchanged two-factor constant-depth blocks onto the generated positive
root subgroup. The doubled factor is retained at its original depth. -/
theorem range_orderedPositiveFiltrationBlockProduct_eq_iSup
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.extendedAffineRoots)
    (hderiv : AffineRootSystem.derivativeRoots D.extendedAffineRoots = Set.range (rootForm i))
    (x : D.Apartment) (r : ℝ) (hr : 0 ≤ r) (ν : cocharacterLattice S)
    {n : ℕ} (a : Fin n → characterLattice S)
    (hrange : Set.range a = RelativeRoot.indivisiblePositiveRoots i ν) :
    Set.range (D.orderedFiltrationBlockProduct x (fun _ => r) a) =
      ((⨆ b : positiveRelativeRoots i ν, D.filtration x b r :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) := by
  classical
  let c : Fin (n * 2) → characterLattice S := fun l =>
    if (finProdFinEquiv.symm l).2 = 0 then a (finProdFinEquiv.symm l).1
      else 2 • a (finProdFinEquiv.symm l).1
  let H : Fin (n * 2) → Subgroup (rationalPoints G) := fun l =>
    if c l ∈ relativeRoots i then D.filtration x (c l) r else ⊥
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
    intro j l
    by_cases hj : c j ∈ relativeRoots i
    · by_cases hl : c l ∈ relativeRoots i
      · have hjH : H j = D.filtration x (c j) r := ite_eq_left hj
        have hlH : H l = D.filtration x (c l) r := ite_eq_left hl
        rw [hjH, hlH]
        refine (D.filtration_commutator_positive_height x r hr ν (hpos j hj)
          (hpos l hl)).trans ?_
        refine iSup_le fun b => iSup_le fun hb => ?_
        obtain ⟨m, hm⟩ := hcover b
        have hroot : c m ∈ relativeRoots i := hm.symm ▸ b.2.1
        exact le_iSup_of_le m (le_iSup_of_le (hm.symm ▸ hb)
          (by dsimp only [H]; rw [ite_eq_left hroot, hm]))
      · simp only [H, ite_eq_right hl, Subgroup.commutator_bot_right, bot_le]
    · simp only [H, ite_eq_right hj, Subgroup.commutator_bot_left, bot_le]
  have h0 (j : Fin n) : H (finProdFinEquiv (j, 0)) = D.filtration x (a j) r := by
    simp only [H, hc0, ite_eq_left (ha j).1.1]
  have h1 (j : Fin n) : H (finProdFinEquiv (j, 1)) = D.doubleFiltration x (a j) r := by
    simp only [H, hc1, doubleFiltration]
  have hpairs := range_orderedSubgroupPairsProduct H
    (fun j => D.filtration x (a j) r) (fun j => D.doubleFiltration x (a j) r) h0 h1
  change Set.range (RelativeRoot.CentralExtension.orderedProduct (fun l => (H l).subtype)) =
    Set.range (D.orderedFiltrationBlockProduct x (fun _ => r) a) at hpairs
  rw [← hpairs, hcollect]
  apply congrArg (fun K : Subgroup (rationalPoints G) => (K : Set (rationalPoints G)))
  apply le_antisymm
  · refine iSup_le fun l => ?_
    dsimp only [H]
    split_ifs with hl
    · exact le_iSup (fun b : positiveRelativeRoots i ν =>
        D.filtration x b r) ⟨c l, hpos l hl⟩
    · exact bot_le
  · refine iSup_le fun b => ?_
    obtain ⟨l, hl⟩ := hcover b
    have hroot : c l ∈ relativeRoots i := hl.symm ▸ b.2.1
    exact le_iSup_of_le l (by dsimp only [H]; rw [ite_eq_left hroot, hl])

/-- The original ordered positive blocks give actual bijective coordinates
on the subgroup generated by the positive root filtrations at this depth. -/
def positiveFiltrationBlockProductEquiv
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.extendedAffineRoots)
    (hderiv : AffineRootSystem.derivativeRoots D.extendedAffineRoots = Set.range (rootForm i))
    (x : D.Apartment) (r : ℝ) (hr : 0 ≤ r) (ν : cocharacterLattice S)
    {n : ℕ} (a : Fin n → characterLattice S)
    (ha : Function.Injective a)
    (hrange : Set.range a = RelativeRoot.indivisiblePositiveRoots i ν) :
    (∀ j, D.filtrationBlock x (fun _ => r) (a j)) ≃
      (⨆ b : positiveRelativeRoots i ν, D.filtration x b r :
        Subgroup (rationalPoints G)) := by
  let f (v : ∀ j, D.filtrationBlock x (fun _ => r) (a j)) :
      (⨆ b : positiveRelativeRoots i ν, D.filtration x b r :
        Subgroup (rationalPoints G)) :=
    ⟨D.orderedFiltrationBlockProduct x (fun _ => r) a v, by
      change D.orderedFiltrationBlockProduct x (fun _ => r) a v ∈
        ((⨆ b : positiveRelativeRoots i ν, D.filtration x b r :
          Subgroup (rationalPoints G)) : Set (rationalPoints G))
      rw [← D.range_orderedPositiveFiltrationBlockProduct_eq_iSup
        hsys hderiv x r hr ν a hrange]
      exact ⟨v, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro v w hvw
    apply D.orderedFiltrationBlockProduct_injective hG hi x _ ν a ha hrange
    exact congrArg Subtype.val hvw
  · intro w
    have hw : (w : rationalPoints G) ∈
        ((⨆ b : positiveRelativeRoots i ν, D.filtration x b r :
          Subgroup (rationalPoints G)) : Set (rationalPoints G)) := w.property
    rw [← D.range_orderedPositiveFiltrationBlockProduct_eq_iSup
      hsys hderiv x r hr ν a hrange] at hw
    obtain ⟨v, hv⟩ := hw
    exact ⟨v, Subtype.ext hv⟩

end KPApartmentData

end Langlands.Geometry.Building
