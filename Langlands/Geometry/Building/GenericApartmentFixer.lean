import Langlands.Geometry.Building.GenericPositiveRootFixerCoordinates
import Langlands.Geometry.Building.ApartmentFacetClosureFixing
import Langlands.Geometry.Building.PositiveRootFixerCoordinates
import Langlands.Geometry.Building.LocalRootProductInjectivity
import Langlands.Geometry.Building.GenericApartmentInjection

/-! # The pointwise fixer of a whole apartment over an arbitrary field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- Opposite pairs reduce every positive root to an indivisible root or its double. -/
theorem exists_indivisiblePositiveRoot_eq_or_double_of_rankOne
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice S) {b : characterLattice S}
    (hb : b ∈ positiveRelativeRoots i ν) :
    ∃ a ∈ RelativeRoot.indivisiblePositiveRoots i ν, b = a ∨ b = 2 • a := by
  have : Smooth G.X.hom := hG.smooth
  have hE : RelativeRoot.HasOppositeFactorPairs i :=
    fun a ha g hg hg1 => (rootRankOneFactorization k G hG S i hi a ha g hg hg1).1.exists
  obtain ⟨a, ha, m, _, hm, hma⟩ :=
    RelativeRoot.exists_indivisiblePositiveRoot_ray i ν hb.1 hb.2
  refine ⟨a, ha, ?_⟩
  rcases hE.root_eq_or_twice_of_common_positive_multiple i hi.isSplitSubtorus.1
      hb.1 ha.1.1 (show 0 < 1 by omega) hm (by simpa only [one_smul] using hma.symm) with
      h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (ha.1.2 b hb.1 2 (by omega) h.symm).elim

/-- Ordered collection from actual rank-one factorization, without affine-root-system axioms. -/
theorem range_orderedIndivisiblePositiveRootGroupProduct_eq_iSup_of_rankOne
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
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
    obtain ⟨d, hd, hb⟩ := exists_indivisiblePositiveRoot_eq_or_double_of_rankOne hG hi ν b.2
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

/-- The nonnegative ray from `x` in the direction of a cocharacter. -/
def cocharacterRay (x : D.Apartment) (ν : cocharacterLattice S) : Set D.Apartment :=
  {y | ∃ t : ℝ, 0 ≤ t ∧ y = (Submodule.Quotient.mk (t ⊗ₜ[ℤ] ν) :
    TranslationSpace i) +ᵥ x}

/-- The initial point belongs to its cocharacter ray. -/
theorem mem_cocharacterRay_self (x : D.Apartment) (ν : cocharacterLattice S) :
    x ∈ D.cocharacterRay x ν := by
  refine ⟨0, le_rfl, ?_⟩
  simp

/-- A root group has trivial fixer on a ray on which its root tends to minus infinity. -/
theorem rootFixer_cocharacterRay_eq_bot
    (x : D.Apartment) (ν : cocharacterLattice S) {a : characterLattice S}
    (ha : a ∈ relativeRoots i) (hpair : latticePairing S a ν < 0) :
    D.rootFixer a (D.cocharacterRay x ν) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro g hg
  rw [Subgroup.mem_bot]
  obtain ⟨hgU, hfix⟩ := D.mem_rootFixer.1 hg
  apply (x.isValuation.eq_top_iff a ha g hgU).1
  by_contra htop
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 htop
  have hp : 0 < -(latticePairing S a ν : ℝ) := by exact_mod_cast neg_pos.2 hpair
  let t : ℝ := (max r 0 + 1) / -(latticePairing S a ν : ℝ)
  have ht : 0 ≤ t := div_nonneg (by positivity) (le_of_lt hp)
  have hmul : t * -(latticePairing S a ν : ℝ) = max r 0 + 1 :=
    div_mul_cancel₀ _ (ne_of_gt hp)
  have h := hfix ((Submodule.Quotient.mk (t ⊗ₜ[ℤ] ν) :
    TranslationSpace i) +ᵥ x) ⟨t, ht, rfl⟩
  rw [filtration_mk_vadd] at h
  have hle := h.2
  rw [← hr, WithTop.coe_le_coe] at hle
  simp only [eval_tmul, zero_sub] at hle
  have := le_max_left r 0
  nlinarith

/-- The positive unipotent groups separate along the opposite cocharacter ray. -/
theorem iInf_positiveRootGroups_oppositeRay_eq_bot
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (x : D.Apartment) (ν : cocharacterLattice S) :
    (⨅ y ∈ D.cocharacterRay x (-ν),
      ⨆ b : positiveRelativeRoots i ν, D.chamberRootGroup y false b) = ⊥ := by
  rw [D.iInf_iSup_chamberRootGroup_eq_iSup_rootFixer_of_rankOne hG hi ν
    ⟨x, D.mem_cocharacterRay_self x (-ν)⟩]
  apply iSup_eq_bot.2
  intro b
  exact D.rootFixer_cocharacterRay_eq_bot x (-ν) b.2.1 (by
    rw [map_neg]
    exact neg_neg_of_pos b.2.2)

/-- A unipotent point fixing an entire opposite ray is the identity. -/
theorem eq_one_of_unipotent_fixes_oppositeRay
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (x : D.Apartment) (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
    {g : rationalPoints G}
    (hgU : g ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)))
    (hfix : ∀ y ∈ D.cocharacterRay x (-ν),
      g • D.apartmentMap y = D.apartmentMap y) :
    g = 1 := by
  have hg : g ∈ (⨅ y ∈ D.cocharacterRay x (-ν),
      ⨆ b : positiveRelativeRoots i ν, D.chamberRootGroup y false b) :=
    Subgroup.mem_iInf.2 fun y => Subgroup.mem_iInf.2 fun hy =>
      D.mem_positiveRootGroups_of_mem_unipotent_of_smul_apartmentMap_eq
        hG hi y ν hν hgU (hfix y hy)
  rwa [D.iInf_positiveRootGroups_oppositeRay_eq_bot hG hi x ν, Subgroup.mem_bot] at hg

/-- An affine normalizer action fixing a translated positive cone fixes the whole apartment. -/
theorem normalizerAffineEquiv_eq_one_of_fixes_positiveCone
    (hG : IsConnectedReductive G) (hS : IsSplitTorus S.toGrp)
    (x : D.Apartment) (ν : cocharacterLattice S)
    (n : normalizerPoints i)
    (hfix : ∀ w : V S,
      (∀ b ∈ relativeRoots i, 0 < latticePairing S b ν → 0 ≤ eval S b w) →
      n • ((Submodule.Quotient.mk w : TranslationSpace i) +ᵥ x) =
        (Submodule.Quotient.mk w : TranslationSpace i) +ᵥ x) :
    D.normalizerAffineEquiv n = 1 := by
  classical
  have : Smooth G.X.hom := hG.smooth
  have hnx : n • x = x := by
    have h := hfix 0 (fun _ _ _ => by simp)
    simpa only [Submodule.Quotient.mk_zero, zero_vadd] using h
  have hlin (w : V S)
      (hw : ∀ b ∈ relativeRoots i, 0 < latticePairing S b ν → 0 ≤ eval S b w) :
      translationAction i n (Submodule.Quotient.mk w) = Submodule.Quotient.mk w := by
    apply vadd_right_cancel x
    simpa only [smul_vadd, hnx] using hfix w hw
  apply AffineEquiv.ext
  intro y
  obtain ⟨w, rfl⟩ := exists_mk_vadd_eq x y
  let s := (hS.finite_relativeRoots i).toFinset
  let t : ℝ := ∑ b ∈ s, |eval S b w|
  have ht : 0 ≤ t := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hbound (b : characterLattice S) (hb : b ∈ relativeRoots i) :
      |eval S b w| ≤ t :=
    Finset.single_le_sum (f := fun b => |eval S b w|)
      (fun _ _ => abs_nonneg _) ((hS.finite_relativeRoots i).mem_toFinset.2 hb)
  have hcone : ∀ b ∈ relativeRoots i, 0 < latticePairing S b ν →
      0 ≤ eval S b (t ⊗ₜ[ℤ] ν) := by
    intro b hb hpos
    rw [eval_tmul]
    exact mul_nonneg ht (by exact_mod_cast le_of_lt hpos)
  have hcone' : ∀ b ∈ relativeRoots i, 0 < latticePairing S b ν →
      0 ≤ eval S b (w + t ⊗ₜ[ℤ] ν) := by
    intro b hb hpos
    rw [map_add, eval_tmul]
    have hp : (1 : ℝ) ≤ latticePairing S b ν := by
      exact_mod_cast (show 1 ≤ latticePairing S b ν by omega)
    have hm : t ≤ t * (latticePairing S b ν : ℝ) := by nlinarith
    have hbw := (abs_le.1 (hbound b hb)).1
    linarith
  have hw := hlin (w + t ⊗ₜ[ℤ] ν) hcone'
  rw [Submodule.Quotient.mk_add, map_add, hlin _ hcone] at hw
  have hw' := add_right_cancel hw
  change n • ((Submodule.Quotient.mk w : TranslationSpace i) +ᵥ x) = _
  rw [smul_vadd, hnx, hw']
  rfl

/-- The reduced linear normalizer action has the centralizer as its kernel over any field. -/
theorem translationAction_eq_one_iff_mem_centralizerPoints_of_isMaximalSplitTorus
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (n : normalizerPoints i) :
    translationAction i n = 1 ↔ (n : rationalPoints G) ∈ centralizerPoints i := by
  let hT := hi.isSplitSubtorus.1
  constructor
  · intro hn
    have hfixed : ∀ a ∈ relativeRoots i, weylAction i n⁻¹ a = a := by
      intro a ha
      apply eval_injective hT
      apply LinearMap.ext
      intro v
      have h := congrArg
        (fun e : TranslationSpace i ≃ₗ[ℝ] TranslationSpace i =>
          rootForm i ⟨a, ha⟩ (e (Submodule.Quotient.mk v))) hn
      change eval S a (n • v) = eval S a v at h
      rwa [eval_normalizer_smul] at h
    have hw := hT.weylAction_eq_one_of_fixed_roots i
      (relativeRootsRestrictedCharactersSpan k G hG S i hi) n⁻¹ hfixed
    have hc := (hT.weylAction_eq_one_iff i n⁻¹).mp hw
    simpa only [Subgroup.coe_inv, inv_inv] using (centralizerPoints i).inv_mem hc
  · intro hn
    apply LinearEquiv.ext
    intro v
    refine Submodule.Quotient.induction_on _ v fun w => ?_
    change Submodule.Quotient.mk (normalizerAction i n w) = Submodule.Quotient.mk w
    rw [normalizerAction_eq_one_of_mem_centralizerPoints i hn]
    rfl

/-- A normalizer point acting trivially on the apartment centralizes the maximal split torus. -/
theorem mem_centralizerPoints_of_normalizerAffineEquiv_eq_one_of_isMaximalSplitTorus
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (n : normalizerPoints i) (hn : D.normalizerAffineEquiv n = 1) :
    (n : rationalPoints G) ∈ centralizerPoints i := by
  apply (translationAction_eq_one_iff_mem_centralizerPoints_of_isMaximalSplitTorus
    hG hi n).mp
  exact congrArg (fun e : D.Apartment ≃ᵃ[ℝ] D.Apartment => e.linear) hn

/-- The pointwise fixer of the original apartment image centralizes the maximal split torus,
over any field and without affine-root-system assumptions. -/
theorem mem_centralizerPoints_of_fixes_apartment
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {g : rationalPoints G}
    (hfix : ∀ y : D.Apartment, g • D.apartmentMap y = D.apartmentMap y) :
    g ∈ centralizerPoints i := by
  classical
  have : Smooth G.X.hom := hG.smooth
  have hS := hi.isSplitSubtorus.1
  obtain ⟨ν, hν⟩ := hS.exists_genericCocharacter i
  have hνneg : IsGenericCocharacter i (-ν) := by
    intro a ha
    simpa only [map_neg] using neg_ne_zero.mpr (hν a ha)
  let x : D.Apartment := Classical.arbitrary _
  obtain ⟨m, hmx, s, hs, rfl⟩ :=
    (ApartmentQuotient.mem_stabilizer_apartment_iff D.sharpFixerFamily x g).1
      (MulAction.mem_stabilizer_iff.2 (hfix x))
  have hsharp := D.sharpFixer_subset_mul_sharpNormalizerStabilizer hG hi x (-ν) hνneg
  rw [neg_neg] at hsharp
  obtain ⟨_, ⟨u, hu, v, hv, rfl⟩, q, hq, hsq⟩ := hsharp hs
  change u * v * q = s at hsq
  obtain ⟨-, hqN, hqx⟩ := KPApartmentData.mem_sharpNormalizerStabilizer.mp hq
  let n : normalizerPoints i := ⟨q, hqN⟩ * m
  have hh : s * (m : rationalPoints G) = u * (v * (n : rationalPoints G)) := by
    rw [← hsq]
    change u * v * q * (m : rationalPoints G) =
      u * (v * (q * (m : rationalPoints G)))
    group
  have huU := (D.positiveChamberRootGroups_le_sharpUnipotentPoints x ν hu).1
  have hvU := (D.positiveChamberRootGroups_le_sharpUnipotentPoints x (-ν) hv).1
  have hu_fix (w : V S)
      (hw : ∀ b ∈ relativeRoots i, 0 < latticePairing S b ν → 0 ≤ eval S b w) :
      u • D.apartmentMap ((Submodule.Quotient.mk w : TranslationSpace i) +ᵥ x) =
        D.apartmentMap ((Submodule.Quotient.mk w : TranslationSpace i) +ᵥ x) :=
    D.mem_reducedFixer.1 (D.sharpFixer_le_reducedFixer _
      (D.positiveChamberRootGroups_le_sharpFixer_vadd x ν hw hu))
  have hvn_fix (w : V S)
      (hw : ∀ b ∈ relativeRoots i, 0 < latticePairing S b ν → 0 ≤ eval S b w) :
      (v * (n : rationalPoints G)) •
        D.apartmentMap ((Submodule.Quotient.mk w : TranslationSpace i) +ᵥ x) =
        D.apartmentMap ((Submodule.Quotient.mk w : TranslationSpace i) +ᵥ x) := by
    have h := hfix ((Submodule.Quotient.mk w : TranslationSpace i) +ᵥ x)
    rw [hh, mul_smul] at h
    exact (smul_left_cancel_iff u).1 (h.trans (hu_fix w hw).symm)
  have hn : D.normalizerAffineEquiv n = 1 :=
    D.normalizerAffineEquiv_eq_one_of_fixes_positiveCone hG hS x ν n
      (fun w hw =>
        D.smul_eq_self_of_unipotent_mul_smul_apartmentMap_eq_of_isMaximalSplitTorus
          hG hi _ (-ν) hνneg hvU n (hvn_fix w hw))
  have hn_fix (y : D.Apartment) : n • y = y := by
    change D.normalizerAffineEquiv n y = y
    rw [hn]
    rfl
  have hnG_fix (y : D.Apartment) :
      (n : rationalPoints G) • D.apartmentMap y = D.apartmentMap y := by
    rw [← D.apartmentMap_smul, hn_fix]
  have hv_fix : ∀ y ∈ D.cocharacterRay x ν,
      v • D.apartmentMap y = D.apartmentMap y := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := hy
    have hcone : ∀ b ∈ relativeRoots i, 0 < latticePairing S b ν →
        0 ≤ eval S b (t ⊗ₜ[ℤ] ν) := by
      intro b hb hpos
      rw [eval_tmul]
      exact mul_nonneg ht (by exact_mod_cast le_of_lt hpos)
    have h := hvn_fix (t ⊗ₜ[ℤ] ν) hcone
    rwa [mul_smul, hnG_fix] at h
  have hv1 : v = 1 :=
    D.eq_one_of_unipotent_fixes_oppositeRay hG hi x (-ν) hνneg hvU
      (by simpa only [neg_neg] using hv_fix)
  have hu_fix_all (y : D.Apartment) :
      u • D.apartmentMap y = D.apartmentMap y := by
    have h := hfix y
    rwa [hh, hv1, one_mul, mul_smul, hnG_fix] at h
  have hu1 : u = 1 :=
    D.eq_one_of_unipotent_fixes_oppositeRay hG hi x ν hν huU
      (fun y _ => hu_fix_all y)
  rw [hh, hu1, hv1, one_mul, one_mul]
  exact D.mem_centralizerPoints_of_normalizerAffineEquiv_eq_one_of_isMaximalSplitTorus
    hG hi n hn

/-- Subgroup form of the whole-apartment fixer containment. -/
theorem pointwiseFixer_apartment_le_centralizerPoints
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) :
    D.pointwiseFixer (Set.range D.apartmentMap) ≤ centralizerPoints i := by
  intro g hg
  apply D.mem_centralizerPoints_of_fixes_apartment hG hi
  intro y
  exact D.mem_pointwiseFixer.1 hg _ ⟨y, rfl⟩

/-- The actual whole-apartment fixer, regarded as centralizer points without changing any
ambient rational point. -/
def wholeApartmentFixerToCentralizer
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) :
    D.pointwiseFixer (Set.range D.apartmentMap) →* centralizerPoints i :=
  Subgroup.inclusion (D.pointwiseFixer_apartment_le_centralizerPoints hG hi)

@[simp]
theorem wholeApartmentFixerToCentralizer_coe
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (g : D.pointwiseFixer (Set.range D.apartmentMap)) :
    (D.wholeApartmentFixerToCentralizer hG hi g : rationalPoints G) = g :=
  rfl

end Langlands.Geometry.Building.KPApartmentData
