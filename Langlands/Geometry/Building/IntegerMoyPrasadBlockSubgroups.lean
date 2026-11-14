import Langlands.Geometry.Building.IntegerExtendedAffineRootSystems
import Langlands.Geometry.Building.MoyPrasadDoubleRefinement

/-! # Integer-valued constant-depth root blocks -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj Pointwise TensorProduct commutatorElement
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building.IntegerValuationBuildingData

variable {k : Type u} [Field k]
    {v : Valuation k (WithZero (Multiplicative ℤ))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G)

/-- The opposite ordinary-root/centralizer/root product is injective on
the actual rational-point subgroups of any actual relative root. -/
theorem oppositeRootTripleProduct_injective
    {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i) :
    Function.Injective (fun p :
      rootGroupPoints B.i (-a) × centralizerPoints B.i × rootGroupPoints B.i a =>
        (p.1 : rationalPoints G) * (p.2.1 : rationalPoints G) *
          (p.2.2 : rationalPoints G)) := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  obtain ⟨ν, hν⟩ :=
    B.isMaximalSplitTorus.isSplitSubtorus.1.exists_genericCocharacter B.i
  have hex : ∃ mu : cocharacterLattice B.S, 0 < latticePairing B.S a mu := by
    rcases lt_or_gt_of_ne (hν a ha) with hn | hp
    · exact ⟨-ν, by simpa using neg_pos.mpr hn⟩
    · exact ⟨ν, hp⟩
  obtain ⟨mu, hmu⟩ := hex
  apply unipotentTripleProduct_injective B.i mu
    (rootGroupPoints B.i (-a)) (rootGroupPoints B.i a)
    (fun z : centralizerPoints B.i => (z : rationalPoints G)) Subtype.val_injective
  · exact RelativeRoot.subgroup_le_dynamicUnipotent B.i (-mu)
      (by simpa using hmu) (Over.mk (𝟙 _))
  · exact RelativeRoot.subgroup_le_dynamicUnipotent B.i mu hmu (Over.mk (𝟙 _))
  · exact fun z => z.property

/-- The doubled-root subgroup centralizes the ordinary root subgroup,
using the actual root-system bound on positive multiples. -/
theorem doubleRootGroupPoints_commute
    (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i)
    {g h : rationalPoints G} (hg : g ∈ rootGroupPoints B.i (2 • a))
    (hh : h ∈ rootGroupPoints B.i a) : Commute g h := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  have hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots B.i := by
    intro n hn hroot
    have hm := B.apartment.root_multiple_eq_one_or_two
      (B.isAffineRootSystemWithRankZero_extendedAffineRoots hunit)
      B.derivativeRoots_extendedAffineRoots
      ha (by omega) hroot
    omega
  exact RelativeRoot.double_subgroup_commute_of_noHigherRoots
    RelativeRoot.semigroupRealization RelativeRoot.semigroupCommutator
    RelativeRoot.cyclicRootFunctorComparison inferInstance
    B.isMaximalSplitTorus.isSplitSubtorus.1 B.i ha.1 hhigh
    (Over.mk (𝟙 _)) g h hg hh

/-- If the first input lies in the actual doubled-root group, the positive
factor of ordinary rank-one exchange differs from it at the higher depth
`2t+t'`. The factorization itself is left unchanged. -/
theorem rankOne_double_positive_difference
    (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1) (x : B.Apartment)
    {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i)
    (h2a : 2 • a ∈ relativeRoots B.i)
    {u v v' z u' : rationalPoints G}
    (hu : u ∈ rootGroupPoints B.i (2 • a)) (hu1 : u ≠ 1)
    (hv : v ∈ rootGroupPoints B.i (-a)) (hv1 : v ≠ 1)
    (hv' : v' ∈ rootGroupPoints B.i (-a))
    (hz : z ∈ centralizerPoints B.i) (hu' : u' ∈ rootGroupPoints B.i a)
    (heq : u * v = v' * z * u') {t t' : ℝ}
    (ht : x.val a u = t) (ht' : x.val (-a) v = t') (hpos : 0 < t + t') :
    ((2 * t + t' : ℝ) : WithTop ℝ) ≤ x.val a (u' * u⁻¹) := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  have hT := B.isMaximalSplitTorus.isSplitSubtorus.1
  have hrank := rootRankOneFactorization k G B.isConnectedReductive
    B.S B.i B.isMaximalSplitTorus
  have hneg : -a ∈ relativeRoots B.i :=
    KPApartmentData.neg_mem_relativeRoots_of_rankOne hT hrank x ha
  have huA : u ∈ rootGroupPoints B.i a :=
    RelativeRoot.double_subgroup_le B.i a (Over.mk (𝟙 _)) hu
  obtain ⟨p, hp⟩ := ((hrank (2 • a) h2a u hu hu1).1).exists
  have hp1long : p.1 ∈ rootGroupPoints B.i (2 • -a) := by
    change p.1 ∈ (RelativeRoot.subgroup B.i (2 • -a)).carrier (Over.mk (𝟙 _))
    simpa only [smul_neg] using hp.1
  have hp2long : p.2 ∈ rootGroupPoints B.i (2 • -a) := by
    change p.2 ∈ (RelativeRoot.subgroup B.i (2 • -a)).carrier (Over.mk (𝟙 _))
    simpa only [smul_neg] using hp.2.1
  have hp1 : p.1 ∈ rootGroupPoints B.i (-a) :=
    RelativeRoot.double_subgroup_le B.i (-a) (Over.mk (𝟙 _)) hp1long
  have hp2 : p.2 ∈ rootGroupPoints B.i (-a) :=
    RelativeRoot.double_subgroup_le B.i (-a) (Over.mk (𝟙 _)) hp2long
  have hpa : RelativeRoot.IsOppositeFactorPair B.i a u p := ⟨hp1, hp2, hp.2.2⟩
  let n : normalizerPoints B.i := ⟨p.1 * u * p.2, hp.2.2⟩
  have hnflip : weylAction B.i n a = -a :=
    hpa.weylAction_eq_neg B.i hT ha.1 huA hu1
  have hnflipNeg : weylAction B.i n (-a) = a := by
    rw [map_neg, hnflip, neg_neg]
  have hninv : weylAction B.i n⁻¹ a = -a := by
    have h := weylAction_inv_apply_apply n (-a)
    rw [hnflipNeg] at h
    exact h
  obtain ⟨W, hW⟩ := KPApartmentData.exists_smul_val_eq_vadd n x
  have hWa : eval B.S a W = -2 * t :=
    KPApartmentData.eval_translation_eq_of_factor x ha hneg huA hu1 hp1 hp2
      hp.2.2 hnflip ht hW
  have hp1val : x.val (-a) p.1 = ((-t : ℝ) : WithTop ℝ) := by
    have h := x.isValuation.opposite a ha u huA hu1 p.1 hp1 p.2 hp2 hp.2.2
    rw [ht] at h
    exact withTop_eq_neg_of_add_eq_zero h
  have hp1ne : p.1 ≠ 1 := by
    intro h
    rw [h, (x.isValuation.eq_top_iff (-a) hneg 1 (Subgroup.one_mem _)).mpr rfl] at hp1val
    exact WithTop.top_ne_coe hp1val
  let w : rationalPoints G := (n : rationalPoints G) * v * (n : rationalPoints G)⁻¹
  have hw : w ∈ rootGroupPoints B.i a := by
    have h := conj_mem_rootGroupPoints n hv
    rwa [hnflipNeg] at h
  have hwne : w ≠ 1 := by
    intro h
    apply hv1
    calc
      v = (n : rationalPoints G)⁻¹ * w * (n : rationalPoints G) := by
        dsimp only [w]
        group
      _ = 1 := by rw [h]; group
  have hwval : x.val a w = ((2 * t + t' : ℝ) : WithTop ℝ) := by
    have hev := congrArg (fun φ : RootFunctionFamily B.S G => φ a w) hW
    simp only [RootFunctionFamily.smul_apply, hninv,
      RootFunctionFamily.vadd_apply, hWa] at hev
    have hcancel : (n : rationalPoints G)⁻¹ * w * (n : rationalPoints G) = v := by
      dsimp only [w]
      group
    rw [hcancel, ht'] at hev
    induction he : x.val a w using WithTop.recTopCoe with
    | top =>
      rw [he, top_add] at hev
      exact False.elim (WithTop.coe_ne_top hev)
    | coe q =>
      rw [he, ← WithTop.coe_add, WithTop.coe_inj] at hev
      apply congrArg (fun z : ℝ => (z : WithTop ℝ))
      linarith
  have hspan := relativeRootsRestrictedCharactersSpan k G B.isConnectedReductive
    B.S B.i B.isMaximalSplitTorus
  obtain ⟨b, hb, c, hc, d, hd, hwd, -, hdt, -⟩ :=
    B.apartment.exists_rankOne_factorization hT (hT.finite_relativeRoots B.i)
      hspan hrank x ha hneg hw hwne hp1 hp1ne hwval hp1val (by linarith)
  have hconj : p.2⁻¹ * v * p.2 = v := by
    have hcomm := B.doubleRootGroupPoints_commute hunit hneg hp2long hv
    calc p.2⁻¹ * v * p.2 = p.2⁻¹ * (v * p.2) := by group
      _ = p.2⁻¹ * (p.2 * v) := by rw [hcomm.eq]
      _ = v := inv_mul_cancel_left _ _
  have hcompare :
      v' * z * (u' * u⁻¹) = (p.1⁻¹ * b) * c * d := by
    calc v' * z * (u' * u⁻¹) = (u * v) * u⁻¹ := by rw [heq]; group
      _ = p.1⁻¹ * (n : rationalPoints G) * (p.2⁻¹ * v * p.2) *
          (n : rationalPoints G)⁻¹ * p.1 := by dsimp only [n]; group
      _ = p.1⁻¹ * w * p.1 := by rw [hconj]; dsimp only [w]; group
      _ = p.1⁻¹ * (w * p.1) := by group
      _ = p.1⁻¹ * (b * c * d) := by rw [hwd]
      _ = (p.1⁻¹ * b) * c * d := by group
  have hunique := B.oppositeRootTripleProduct_injective ha
    (a₁ := (⟨v', hv'⟩, ⟨z, hz⟩, ⟨u' * u⁻¹,
      (rootGroupPoints B.i a).mul_mem hu' ((rootGroupPoints B.i a).inv_mem huA)⟩))
    (a₂ := (⟨p.1⁻¹ * b, (rootGroupPoints B.i (-a)).mul_mem
      ((rootGroupPoints B.i (-a)).inv_mem hp1) hb⟩, ⟨c, hc⟩, ⟨d, hd⟩)) hcompare
  have hlast : u' * u⁻¹ = d :=
    congrArg (fun p : rootGroupPoints B.i (-a) × centralizerPoints B.i ×
      rootGroupPoints B.i a => (p.2.2 : rationalPoints G)) hunique
  rwa [hlast]

/-- An element of the retained double-depth factor commutes with an
element of the ordinary root-depth factor, at arbitrary real depths. -/
theorem doubleFiltration_commute_filtration (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    (x : B.Apartment) {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i)
    (r s : ℝ) {g h : rationalPoints G}
    (hg : g ∈ B.apartment.doubleFiltration x a r)
    (hh : h ∈ B.filtration x a s) : Commute g h := by
  by_cases h2a : 2 • a ∈ relativeRoots B.i
  · rw [B.apartment.doubleFiltration_of_mem x a r h2a] at hg
    exact B.doubleRootGroupPoints_commute hunit ha hg.1 hh.1
  · rw [B.apartment.doubleFiltration_of_not_mem x a r h2a] at hg
    rw [Subgroup.mem_bot.mp hg]
    exact Commute.one_left _

/-- The original constant-depth two-factor block is itself a subgroup.
Its carrier remains definitionally the original set product. -/
def filtrationBlockSubgroup (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    (x : B.Apartment) (r : ℝ) {a : characterLattice B.S}
    (ha : a ∈ relativeRoots B.i) : Subgroup (rationalPoints G) where
  carrier := B.apartment.filtrationBlock x (fun _ => r) a
  one_mem' := ⟨1, (B.filtration x a r).one_mem,
    1, (B.apartment.doubleFiltration x a r).one_mem, one_mul _⟩
  mul_mem' := by
    rintro g h ⟨v, hv, w, hw, rfl⟩ ⟨v', hv', w', hw', rfl⟩
    refine ⟨v * v', (B.filtration x a r).mul_mem hv hv',
      w * w', (B.apartment.doubleFiltration x a r).mul_mem hw hw', ?_⟩
    have hcomm := B.doubleFiltration_commute_filtration hunit x ha r r hw hv'
    calc
      (v * v') * (w * w') = v * (v' * w) * w' := by group
      _ = v * (w * v') * w' := by rw [hcomm.eq]
      _ = (v * w) * (v' * w') := by group
  inv_mem' := by
    rintro g ⟨v, hv, w, hw, rfl⟩
    refine ⟨v⁻¹, (B.filtration x a r).inv_mem hv,
      w⁻¹, (B.apartment.doubleFiltration x a r).inv_mem hw, ?_⟩
    have hcomm := B.doubleFiltration_commute_filtration hunit x ha r r hw hv
    calc
      v⁻¹ * w⁻¹ = (w * v)⁻¹ := by group
      _ = (v * w)⁻¹ := congrArg Inv.inv hcomm.eq

@[simp]
theorem coe_filtrationBlockSubgroup (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    (x : B.Apartment) (r : ℝ) {a : characterLattice B.S}
    (ha : a ∈ relativeRoots B.i) :
    (B.filtrationBlockSubgroup hunit x r ha : Set (rationalPoints G)) =
      B.apartment.filtrationBlock x (fun _ => r) a := rfl

theorem filtration_le_filtrationBlockSubgroup (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    (x : B.Apartment) (r : ℝ) {a : characterLattice B.S}
    (ha : a ∈ relativeRoots B.i) :
    B.filtration x a r ≤ B.filtrationBlockSubgroup hunit x r ha :=
  B.apartment.filtration_subset_filtrationBlock x (fun _ => r) a

theorem doubleFiltration_le_filtrationBlockSubgroup (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    (x : B.Apartment) (r : ℝ) {a : characterLattice B.S}
    (ha : a ∈ relativeRoots B.i) :
    B.apartment.doubleFiltration x a r ≤ B.filtrationBlockSubgroup hunit x r ha := by
  intro g hg
  exact ⟨1, (B.filtration x a r).one_mem, g, hg, one_mul _⟩

end Langlands.Geometry.Building.IntegerValuationBuildingData
