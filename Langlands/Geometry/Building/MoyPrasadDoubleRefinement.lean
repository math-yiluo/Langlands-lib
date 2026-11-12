import Langlands.Geometry.Building.MoyPrasadRankOne
import Langlands.Geometry.Building.MoyPrasadRootSeparation
import Langlands.Geometry.Building.ValuationBuildingAxioms
import Langlands.Geometry.Building.ChamberProductInjective
import Langlands.Geometry.Building.ChamberPositiveCollection
import Langlands.GroupScheme.Rational.RootDoubleCommutatorPairing
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Rational.RootSubgroupPositive

/-! # The retained doubled-root factor in local depth exchange -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)

/-- The opposite ordinary-root/centralizer/root product is injective on
the actual rational-point subgroups of any actual relative root. -/
theorem oppositeRootTripleProduct_injective
    {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i) :
    Function.Injective (fun p :
      rootGroupPoints P.i (-a) × centralizerPoints P.i × rootGroupPoints P.i a =>
        (p.1 : rationalPoints G) * (p.2.1 : rationalPoints G) *
          (p.2.2 : rationalPoints G)) := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  obtain ⟨ν, hν⟩ :=
    P.isMaximalSplitTorus.isSplitSubtorus.1.exists_genericCocharacter P.i
  have hex : ∃ mu : cocharacterLattice P.S, 0 < latticePairing P.S a mu := by
    rcases lt_or_gt_of_ne (hν a ha) with hn | hp
    · exact ⟨-ν, by simpa using neg_pos.mpr hn⟩
    · exact ⟨ν, hp⟩
  obtain ⟨mu, hmu⟩ := hex
  apply unipotentTripleProduct_injective P.i mu
    (rootGroupPoints P.i (-a)) (rootGroupPoints P.i a)
    (fun z : centralizerPoints P.i => (z : rationalPoints G)) Subtype.val_injective
  · exact RelativeRoot.subgroup_le_dynamicUnipotent P.i (-mu)
      (by simpa using hmu) (Over.mk (𝟙 _))
  · exact RelativeRoot.subgroup_le_dynamicUnipotent P.i mu hmu (Over.mk (𝟙 _))
  · exact fun z => z.property

/-- The doubled-root subgroup centralizes the ordinary root subgroup,
using the actual root-system bound on positive multiples. -/
theorem doubleRootGroupPoints_commute
    (hP : P.SatisfiesApartmentAxioms)
    {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i)
    {g h : rationalPoints G} (hg : g ∈ rootGroupPoints P.i (2 • a))
    (hh : h ∈ rootGroupPoints P.i a) : Commute g h := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  have hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots P.i := by
    intro n hn hroot
    have hm := P.apartment.root_multiple_eq_one_or_two
      hP.isAffineRootSystem_extendedAffineRoots hP.derivativeRoots_extendedAffineRoots
      ha (by omega) hroot
    omega
  exact RelativeRoot.double_subgroup_commute_of_noHigherRoots
    RelativeRoot.semigroupRealization RelativeRoot.semigroupCommutator
    RelativeRoot.cyclicRootFunctorComparison inferInstance
    P.isMaximalSplitTorus.isSplitSubtorus.1 P.i ha.1 hhigh
    (Over.mk (𝟙 _)) g h hg hh

/-- If the first input lies in the actual doubled-root group, the positive
factor of ordinary rank-one exchange differs from it at the higher depth
`2t+t'`. The factorization itself is left unchanged. -/
theorem rankOne_double_positive_difference
    (hP : P.SatisfiesApartmentAxioms) (x : P.Apartment)
    {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i)
    (h2a : 2 • a ∈ relativeRoots P.i)
    {u v v' z u' : rationalPoints G}
    (hu : u ∈ rootGroupPoints P.i (2 • a)) (hu1 : u ≠ 1)
    (hv : v ∈ rootGroupPoints P.i (-a)) (hv1 : v ≠ 1)
    (hv' : v' ∈ rootGroupPoints P.i (-a))
    (hz : z ∈ centralizerPoints P.i) (hu' : u' ∈ rootGroupPoints P.i a)
    (heq : u * v = v' * z * u') {t t' : ℝ}
    (ht : x.val a u = t) (ht' : x.val (-a) v = t') (hpos : 0 < t + t') :
    ((2 * t + t' : ℝ) : WithTop ℝ) ≤ x.val a (u' * u⁻¹) := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  have hT := P.isMaximalSplitTorus.isSplitSubtorus.1
  have hrank := rootRankOneFactorization F G P.isConnectedReductive
    P.S P.i P.isMaximalSplitTorus
  have hneg : -a ∈ relativeRoots P.i :=
    KPApartmentData.neg_mem_relativeRoots_of_rankOne hT hrank x ha
  have huA : u ∈ rootGroupPoints P.i a :=
    RelativeRoot.double_subgroup_le P.i a (Over.mk (𝟙 _)) hu
  obtain ⟨p, hp⟩ := ((hrank (2 • a) h2a u hu hu1).1).exists
  have hp1long : p.1 ∈ rootGroupPoints P.i (2 • -a) := by
    change p.1 ∈ (RelativeRoot.subgroup P.i (2 • -a)).carrier (Over.mk (𝟙 _))
    simpa only [smul_neg] using hp.1
  have hp2long : p.2 ∈ rootGroupPoints P.i (2 • -a) := by
    change p.2 ∈ (RelativeRoot.subgroup P.i (2 • -a)).carrier (Over.mk (𝟙 _))
    simpa only [smul_neg] using hp.2.1
  have hp1 : p.1 ∈ rootGroupPoints P.i (-a) :=
    RelativeRoot.double_subgroup_le P.i (-a) (Over.mk (𝟙 _)) hp1long
  have hp2 : p.2 ∈ rootGroupPoints P.i (-a) :=
    RelativeRoot.double_subgroup_le P.i (-a) (Over.mk (𝟙 _)) hp2long
  have hpa : RelativeRoot.IsOppositeFactorPair P.i a u p := ⟨hp1, hp2, hp.2.2⟩
  let n : normalizerPoints P.i := ⟨p.1 * u * p.2, hp.2.2⟩
  have hnflip : weylAction P.i n a = -a :=
    hpa.weylAction_eq_neg P.i hT ha.1 huA hu1
  have hnflipNeg : weylAction P.i n (-a) = a := by
    rw [map_neg, hnflip, neg_neg]
  have hninv : weylAction P.i n⁻¹ a = -a := by
    have h := weylAction_inv_apply_apply n (-a)
    rw [hnflipNeg] at h
    exact h
  obtain ⟨W, hW⟩ := KPApartmentData.exists_smul_val_eq_vadd n x
  have hWa : eval P.S a W = -2 * t :=
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
  have hw : w ∈ rootGroupPoints P.i a := by
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
    have hev := congrArg (fun φ : RootFunctionFamily P.S G => φ a w) hW
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
  have hspan := relativeRootsRestrictedCharactersSpan F G P.isConnectedReductive
    P.S P.i P.isMaximalSplitTorus
  obtain ⟨b, hb, c, hc, d, hd, hwd, -, hdt, -⟩ :=
    P.apartment.exists_rankOne_factorization hT (hT.finite_relativeRoots P.i)
      hspan hrank x ha hneg hw hwne hp1 hp1ne hwval hp1val (by linarith)
  have hconj : p.2⁻¹ * v * p.2 = v := by
    have hcomm := P.doubleRootGroupPoints_commute hP hneg hp2long hv
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
  have hunique := P.oppositeRootTripleProduct_injective ha
    (a₁ := (⟨v', hv'⟩, ⟨z, hz⟩, ⟨u' * u⁻¹,
      (rootGroupPoints P.i a).mul_mem hu' ((rootGroupPoints P.i a).inv_mem huA)⟩))
    (a₂ := (⟨p.1⁻¹ * b, (rootGroupPoints P.i (-a)).mul_mem
      ((rootGroupPoints P.i (-a)).inv_mem hp1) hb⟩, ⟨c, hc⟩, ⟨d, hd⟩)) hcompare
  have hlast : u' * u⁻¹ = d :=
    congrArg (fun p : rootGroupPoints P.i (-a) × centralizerPoints P.i ×
      rootGroupPoints P.i a => (p.2.2 : rationalPoints G)) hunique
  rwa [hlast]

namespace CentralizerFiltration

/-- Exchange an original doubled-root element with an opposite ordinary
root element. The new positive coordinate stays in the original two-factor
block at the original doubled-root depth. -/
def doublePositiveMoyPrasadCoordinates
    (hP : P.SatisfiesApartmentAxioms)
    (Zf : P.CentralizerFiltration) (hZ : Zf.IsCommutatorFriendly)
    (x : P.Apartment) {a : characterLattice P.S}
    (ha : a ∈ relativeRoots P.i) (h2a : 2 • a ∈ relativeRoots P.i)
    (r s : NNReal) (hpos : 0 < r / 2 + s)
    (u : P.filtration x (2 • a) r) (v : P.filtration x (-a) s) :
    {p : P.filtration x (-a) s × Zf.filtration (r / 2 + s) ×
        P.apartment.filtrationBlock x (fun _ => (r : ℝ)) a //
      (p.1 : rationalPoints G) *
        rationalPoints.map P.centralizer.j (p.2.1 : rationalPoints P.centralizer.Z) *
        (p.2.2 : rationalPoints G) = (u : rationalPoints G) * (v : rationalPoints G)} := by
  apply Classical.choice
  have huBlock : (u : rationalPoints G) ∈
      P.apartment.filtrationBlock x (fun _ => (r : ℝ)) a := by
    refine ⟨1, (P.filtration x a r).one_mem, u, ?_, one_mul _⟩
    rw [P.apartment.doubleFiltration_of_mem x a r h2a]
    exact u.property
  have hOneBlock : (1 : rationalPoints G) ∈
      P.apartment.filtrationBlock x (fun _ => (r : ℝ)) a := by
    exact ⟨1, (P.filtration x a r).one_mem,
      1, (P.apartment.doubleFiltration x a r).one_mem, one_mul _⟩
  by_cases hu1 : (u : rationalPoints G) = 1
  · exact ⟨⟨(v, 1, ⟨1, hOneBlock⟩), by simp [hu1]⟩⟩
  by_cases hv1 : (v : rationalPoints G) = 1
  · exact ⟨⟨(1, 1, ⟨u, huBlock⟩), by simp [hv1]⟩⟩
  have huHalf : (u : rationalPoints G) ∈ P.filtration x a (r / 2 : NNReal) := by
    have h := P.apartment.filtration_double_le_half x ha h2a (r : ℝ) u.property
    simpa only [NNReal.coe_div, NNReal.coe_ofNat] using h
  obtain ⟨v', hv', z, hz, u', hu', heq⟩ :=
    Zf.exists_rankOne_depth_factorization hZ x ha (r / 2) s hpos huHalf v.property
  obtain ⟨t, ht⟩ := KPApartmentData.exists_val_eq_coe x ha huHalf.1 hu1
  have hneg : -a ∈ relativeRoots P.i := by
    let : Smooth G.X.hom := P.isConnectedReductive.smooth
    exact KPApartmentData.neg_mem_relativeRoots_of_rankOne
      P.isMaximalSplitTorus.isSplitSubtorus.1
      (rootRankOneFactorization F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus)
      x ha
  obtain ⟨t', ht'⟩ := KPApartmentData.exists_val_eq_coe x hneg v.property.1 hv1
  have hrt : (r : ℝ) / 2 ≤ t := by
    have h := huHalf.2
    rw [ht, WithTop.coe_le_coe] at h
    exact h
  have hst : (s : ℝ) ≤ t' := by
    have h := v.property.2
    rw [ht', WithTop.coe_le_coe] at h
    exact h
  have hsum : 0 < t + t' := by
    have hpos' : 0 < (r : ℝ) / 2 + (s : ℝ) := by exact_mod_cast hpos
    linarith
  have hdelta := P.rankOne_double_positive_difference hP x ha h2a u.property.1 hu1
    v.property.1 hv1 hv'.1
    (map_mem_centralizerPoints P.centralizer.isRepresentedBy z) hu'.1 heq.symm ht ht' hsum
  have hdeltaFil : u' * (u : rationalPoints G)⁻¹ ∈ P.filtration x a r := by
    refine ⟨(rootGroupPoints P.i a).mul_mem hu'.1
      ((rootGroupPoints P.i a).inv_mem huHalf.1), ?_⟩
    apply le_trans (WithTop.coe_le_coe.mpr ?_) hdelta
    linarith [s.coe_nonneg]
  have hu'Block : u' ∈ P.apartment.filtrationBlock x (fun _ => (r : ℝ)) a := by
    refine ⟨u' * (u : rationalPoints G)⁻¹, hdeltaFil, u, ?_, inv_mul_cancel_right _ _⟩
    rw [P.apartment.doubleFiltration_of_mem x a r h2a]
    exact u.property
  exact ⟨⟨(⟨v', hv'⟩, ⟨z, hz⟩, ⟨u', hu'Block⟩), heq⟩⟩

end CentralizerFiltration

end ParahoricBuildingData

end Langlands.Geometry.Building
