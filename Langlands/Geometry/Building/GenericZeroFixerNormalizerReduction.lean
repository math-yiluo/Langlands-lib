import Langlands.Geometry.Building.GenericFiniteSharpExchange
import Langlands.Geometry.Building.GenericPositiveRootFixerCoordinates
import Langlands.Geometry.Building.ApartmentFacetClosureFixing
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! # Finite zero-fixer comparison reduced to the normalizer over any field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- Fixing the apartment image is pointwise fixation of its parameter set. -/
theorem mem_pointwiseFixer_image_iff {Ω : Set D.Apartment} {g : rationalPoints G} :
    g ∈ D.pointwiseFixer (D.apartmentMap '' Ω) ↔
      ∀ x ∈ Ω, g • D.apartmentMap x = D.apartmentMap x := by
  rw [D.mem_pointwiseFixer, Set.forall_mem_image]

/-- Apartment-image fixers are antitone in the parameter set. -/
theorem pointwiseFixer_image_anti {Ω Ω' : Set D.Apartment} (h : Ω ⊆ Ω') :
    D.pointwiseFixer (D.apartmentMap '' Ω') ≤
      D.pointwiseFixer (D.apartmentMap '' Ω) := by
  intro g hg
  exact D.mem_pointwiseFixer_image_iff.2
    (fun x hx => (D.mem_pointwiseFixer_image_iff.1 hg) x (h hx))

/-- Every sharp fixer fixes the image of its apartment subset. -/
theorem sharpFixer_le_pointwiseFixer_image (Ω : Set D.Apartment) :
    D.sharpFixer Ω ≤ D.pointwiseFixer (D.apartmentMap '' Ω) := by
  intro g hg
  refine D.mem_pointwiseFixer_image_iff.2 fun x hx => ?_
  exact D.mem_reducedFixer.1 (D.sharpFixer_le_reducedFixer x
    (D.sharpFixer_anti (Set.singleton_subset_iff.2 hx) hg))

/-- A subgroup of normalizer points acting trivially on the entire apartment normalizes
its sharp fixers. -/
theorem map_trivialNormalizer_le_normalizer_sharpFixer
    (Q : Subgroup (normalizerPoints i))
    (hQ : ∀ n ∈ Q, ∀ x : D.Apartment, n • x = x) (Ω : Set D.Apartment) :
    Q.map (normalizerPoints i).subtype ≤
      Subgroup.normalizer (D.sharpFixer Ω : Set (rationalPoints G)) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro n hn g hg
  obtain ⟨n, hn, rfl⟩ := hn
  have hΩ : n • Ω = Ω := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change n • y ∈ Ω
      rwa [hQ n hn y]
    · intro hx
      exact ⟨x, hx, hQ n hn x⟩
  have h := D.sharpFixer_le_comap n Ω hg
  rw [hΩ] at h
  exact h

/-- The join with a trivial normalizer subgroup is the sharp-fixer/normalizer set product. -/
theorem coe_trivialNormalizer_sup_sharpFixer_eq_mul_reverse
    (Q : Subgroup (normalizerPoints i))
    (hQ : ∀ n ∈ Q, ∀ x : D.Apartment, n • x = x) (Ω : Set D.Apartment) :
    ((Q.map (normalizerPoints i).subtype ⊔ D.sharpFixer Ω :
      Subgroup (rationalPoints G)) : Set (rationalPoints G)) =
        (D.sharpFixer Ω : Set (rationalPoints G)) *
          (Q.map (normalizerPoints i).subtype : Set (rationalPoints G)) := by
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (D.map_trivialNormalizer_le_normalizer_sharpFixer Q hQ Ω)]
  exact Subgroup.set_mul_normalizer_comm _ _
    (D.map_trivialNormalizer_le_normalizer_sharpFixer Q hQ Ω)

/-- Trivial normalizer points fix every apartment image. -/
theorem map_trivialNormalizer_le_pointwiseFixer_image
    (Q : Subgroup (normalizerPoints i))
    (hQ : ∀ n ∈ Q, ∀ x : D.Apartment, n • x = x) (Ω : Set D.Apartment) :
    Q.map (normalizerPoints i).subtype ≤
      D.pointwiseFixer (D.apartmentMap '' Ω) := by
  rintro g ⟨n, hn, rfl⟩
  refine D.mem_pointwiseFixer_image_iff.2 fun x _ => ?_
  change (n : rationalPoints G) • D.apartmentMap x = D.apartmentMap x
  rw [← D.apartmentMap_smul, hQ n hn x]

/-- The exact finite normalizer premise needed for the generic comparison. -/
def HasNormalizerSharpFixers (H : Subgroup (rationalPoints G))
    (Q : Subgroup (normalizerPoints i)) : Prop :=
  ∀ Ω : Set D.Apartment, Ω.Finite → Ω.Nonempty → ∀ n : normalizerPoints i,
    (n : rationalPoints G) ∈ H → (∀ x ∈ Ω, n • x = x) →
      (n : rationalPoints G) ∈ Q.map (normalizerPoints i).subtype ⊔ D.sharpFixer Ω

/-- A point fixer in `H` belongs to the proposed join once the normalizer premise holds. -/
theorem subgroup_pointwiseFixer_singleton_le_trivialNormalizer_sup_sharpFixer
    (H : Subgroup (rationalPoints G)) (Q : Subgroup (normalizerPoints i))
    (hS : ∀ Ω : Set D.Apartment, D.sharpFixer Ω ≤ H)
    (hN : D.HasNormalizerSharpFixers H Q) (x : D.Apartment) :
    H ⊓ D.pointwiseFixer (D.apartmentMap '' {x}) ≤
      Q.map (normalizerPoints i).subtype ⊔ D.sharpFixer {x} := by
  intro g hg
  obtain ⟨hgH, hgfix⟩ := hg
  obtain ⟨n, hnx, s, hs, hgsn⟩ :=
    (ApartmentQuotient.mem_stabilizer_apartment_iff D.sharpFixerFamily x g).1
      (MulAction.mem_stabilizer_iff.2
        ((D.mem_pointwiseFixer_image_iff.1 hgfix) x (Set.mem_singleton x)))
  have hnH : (n : rationalPoints G) ∈ H := by
    have h := H.mul_mem (H.inv_mem (hS {x} hs)) hgH
    rwa [hgsn, inv_mul_cancel_left] at h
  have hnP := hN {x} (Set.finite_singleton x) (Set.singleton_nonempty x) n hnH
    (fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hnx)
  rw [hgsn]
  exact (Q.map (normalizerPoints i).subtype ⊔ D.sharpFixer {x}).mul_mem
    ((show D.sharpFixer {x} ≤
      Q.map (normalizerPoints i).subtype ⊔ D.sharpFixer {x} from le_sup_right) hs) hnP

/-- Decompose a finite-set join into positive and negative root fixers and a normalizer
point in `H` fixing the finite set. -/
theorem exists_mul_mul_normalizer_of_mem_trivialNormalizer_sup_sharpFixer
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (H : Subgroup (rationalPoints G)) (Q : Subgroup (normalizerPoints i))
    (hQ : ∀ n ∈ Q, ∀ x : D.Apartment, n • x = x)
    (hQH : Q.map (normalizerPoints i).subtype ≤ H)
    (hS : ∀ Ω : Set D.Apartment, D.sharpFixer Ω ≤ H)
    {Ω : Set D.Apartment} (hΩ : Ω.Finite) (hne : Ω.Nonempty)
    (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
    {g : rationalPoints G}
    (hg : g ∈ Q.map (normalizerPoints i).subtype ⊔ D.sharpFixer Ω) :
    ∃ u ∈ (⨆ b : positiveRelativeRoots i ν, D.rootFixer b Ω),
      ∃ v ∈ (⨆ b : positiveRelativeRoots i (-ν), D.rootFixer b Ω),
        ∃ n : normalizerPoints i, (n : rationalPoints G) ∈ H ∧
          (∀ x ∈ Ω, n • x = x) ∧ g = u * v * n := by
  have hνneg : IsGenericCocharacter i (-ν) := by
    intro a ha
    simpa only [map_neg] using neg_ne_zero.mpr (hν a ha)
  have hg' : g ∈ ((Q.map (normalizerPoints i).subtype ⊔ D.sharpFixer Ω :
      Subgroup (rationalPoints G)) : Set (rationalPoints G)) := hg
  rw [D.coe_trivialNormalizer_sup_sharpFixer_eq_mul_reverse Q hQ Ω] at hg'
  obtain ⟨s, hs, _, ⟨q, hq, rfl⟩, rfl⟩ := hg'
  have hexch := D.sharpFixer_subset_mul_sharpNormalizerFixer hG hi hΩ hne (-ν) hνneg
  rw [neg_neg] at hexch
  obtain ⟨uv, ⟨u, hu, v, hv, rfl⟩, t, ht, huvt⟩ := hexch hs
  change u * v * t = s at huvt
  obtain ⟨htS, htN, htfix⟩ := KPApartmentData.mem_sharpNormalizerFixer.1 ht
  refine ⟨u, hu, v, hv, ⟨t, htN⟩ * q, ?_, fun x hx => ?_, ?_⟩
  · change t * (q : rationalPoints G) ∈ H
    exact H.mul_mem (hS Ω htS) (hQH ⟨q, hq, rfl⟩)
  · rw [mul_smul, hQ q hq x]
    exact htfix x hx
  · rw [← huvt]
    change u * v * t * (q : rationalPoints G) = u * v * (t * (q : rationalPoints G))
    rw [mul_assoc]

/-- The proposed join is always contained in the ambient subgroup and its pointwise fixer. -/
theorem trivialNormalizer_sup_sharpFixer_le_subgroup_pointwiseFixer
    (H : Subgroup (rationalPoints G)) (Q : Subgroup (normalizerPoints i))
    (hQ : ∀ n ∈ Q, ∀ x : D.Apartment, n • x = x)
    (hQH : Q.map (normalizerPoints i).subtype ≤ H)
    (hS : ∀ Ω : Set D.Apartment, D.sharpFixer Ω ≤ H) (Ω : Set D.Apartment) :
    Q.map (normalizerPoints i).subtype ⊔ D.sharpFixer Ω ≤
      H ⊓ D.pointwiseFixer (D.apartmentMap '' Ω) :=
  sup_le (le_inf hQH (D.map_trivialNormalizer_le_pointwiseFixer_image Q hQ Ω))
    (le_inf (hS Ω) (D.sharpFixer_le_pointwiseFixer_image Ω))

/-- The insertion step of KP Lemma 7.7.4 for an arbitrary ambient subgroup. -/
theorem mem_trivialNormalizer_sup_sharpFixer_insert
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (H : Subgroup (rationalPoints G)) (Q : Subgroup (normalizerPoints i))
    (hQ : ∀ n ∈ Q, ∀ x : D.Apartment, n • x = x)
    (hQH : Q.map (normalizerPoints i).subtype ≤ H)
    (hS : ∀ Ω : Set D.Apartment, D.sharpFixer Ω ≤ H)
    (hN : D.HasNormalizerSharpFixers H Q)
    {Ω : Set D.Apartment} (hΩ : Ω.Finite) (hne : Ω.Nonempty) (x : D.Apartment)
    {g : rationalPoints G}
    (hgx : g ∈ H ⊓ D.pointwiseFixer (D.apartmentMap '' insert x Ω))
    (hgΩ : g ∈ Q.map (normalizerPoints i).subtype ⊔ D.sharpFixer Ω) :
    g ∈ Q.map (normalizerPoints i).subtype ⊔ D.sharpFixer (insert x Ω) := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨w, hw⟩ := KPApartmentData.exists_mk_vadd_eq (D := D) y x
  obtain ⟨ν, hν, hadapt⟩ := exists_genericCocharacter_eval_nonneg_of_isMaximalSplitTorus hG hi w
  have hνneg : IsGenericCocharacter i (-ν) := by
    intro a ha
    simpa only [map_neg] using neg_ne_zero.mpr (hν a ha)
  obtain ⟨u, hu, v, hv, n, hnH, hnfix, rfl⟩ :=
    D.exists_mul_mul_normalizer_of_mem_trivialNormalizer_sup_sharpFixer
      hG hi H Q hQ hQH hS hΩ ⟨y, hy⟩ ν hν hgΩ
  have hSle : D.sharpFixer (insert x Ω) ≤
      Q.map (normalizerPoints i).subtype ⊔ D.sharpFixer (insert x Ω) := le_sup_right
  have hleF := D.trivialNormalizer_sup_sharpFixer_le_subgroup_pointwiseFixer
    H Q hQ hQH hS (insert x Ω)
  have hu' : u ∈ D.sharpFixer (insert x Ω) := by
    suffices hle : (⨆ b : positiveRelativeRoots i ν, D.rootFixer b Ω) ≤
        D.sharpFixer (insert x Ω) from hle hu
    refine iSup_le fun b => ?_
    refine le_trans ?_ (D.rootFixer_le_sharpFixer ⟨b, b.2.1⟩ (insert x Ω))
    intro t ht
    obtain ⟨htU, htΩ⟩ := D.mem_rootFixer.1 ht
    refine D.mem_rootFixer.2 ⟨htU, fun z hz => ?_⟩
    rcases Set.mem_insert_iff.1 hz with rfl | hz
    · have hty := htΩ y hy
      rw [hw, KPApartmentData.filtration_mk_vadd]
      refine ⟨htU, le_trans ?_ hty.2⟩
      have := hadapt b b.2.1 b.2.2
      exact WithTop.coe_le_coe.2 (by linarith)
    · exact htΩ z hz
  have huP := hSle hu'
  have huF := hleF huP
  have hvn : v * (n : rationalPoints G) ∈
      H ⊓ D.pointwiseFixer (D.apartmentMap '' insert x Ω) := by
    have h := (H ⊓ D.pointwiseFixer (D.apartmentMap '' insert x Ω)).mul_mem
      ((H ⊓ D.pointwiseFixer (D.apartmentMap '' insert x Ω)).inv_mem huF) hgx
    rwa [mul_assoc, inv_mul_cancel_left] at h
  have hvU : v ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom (-ν) ≫ i)).carrier (Over.mk (𝟙 _)) := by
    suffices hle : (⨆ b : positiveRelativeRoots i (-ν), D.rootFixer b Ω) ≤
        (Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ i)).carrier (Over.mk (𝟙 _))
      from hle hv
    refine iSup_le fun b => ?_
    exact inf_le_left.trans
      (RelativeRoot.subgroup_le_dynamicUnipotent i (-ν) b.2.2 (Over.mk (𝟙 _)))
  have hnx : n • x = x :=
    D.smul_eq_self_of_unipotent_mul_smul_apartmentMap_eq_of_isMaximalSplitTorus
      hG hi x (-ν) hνneg hvU n
      ((D.mem_pointwiseFixer_image_iff.1 hvn.2) x (Set.mem_insert x Ω))
  have hnP : (n : rationalPoints G) ∈
      Q.map (normalizerPoints i).subtype ⊔ D.sharpFixer (insert x Ω) :=
    hN (insert x Ω) (hΩ.insert x) (Set.insert_nonempty x Ω) n hnH
      fun z hz => by
        rcases Set.mem_insert_iff.1 hz with rfl | hz
        · exact hnx
        · exact hnfix z hz
  have hvF : v ∈ H ⊓ D.pointwiseFixer (D.apartmentMap '' insert x Ω) := by
    have h := (H ⊓ D.pointwiseFixer (D.apartmentMap '' insert x Ω)).mul_mem hvn
      ((H ⊓ D.pointwiseFixer (D.apartmentMap '' insert x Ω)).inv_mem (hleF hnP))
    rwa [mul_inv_cancel_right] at h
  have hv' : v ∈ D.sharpFixer (insert x Ω) := by
    have hmem : v ∈ ⨅ z ∈ insert x Ω, ⨆ b : positiveRelativeRoots i (-ν),
        D.chamberRootGroup z false b := by
      refine Subgroup.mem_iInf.2 fun z => Subgroup.mem_iInf.2 fun hz => ?_
      exact D.mem_positiveRootGroups_of_mem_unipotent_of_smul_apartmentMap_eq
        hG hi z (-ν) hνneg hvU ((D.mem_pointwiseFixer_image_iff.1 hvF.2) z hz)
    rw [D.iInf_iSup_chamberRootGroup_eq_iSup_rootFixer_of_rankOne
      hG hi (-ν) (Set.insert_nonempty x Ω)] at hmem
    suffices hle : (⨆ b : positiveRelativeRoots i (-ν), D.rootFixer b (insert x Ω)) ≤
        D.sharpFixer (insert x Ω) from hle hmem
    refine iSup_le fun b => ?_
    exact D.rootFixer_le_sharpFixer ⟨b, b.2.1⟩ (insert x Ω)
  exact (Q.map (normalizerPoints i).subtype ⊔ D.sharpFixer (insert x Ω)).mul_mem
    ((Q.map (normalizerPoints i).subtype ⊔ D.sharpFixer (insert x Ω)).mul_mem huP
      (hSle hv')) hnP

/-- Finite-set comparison follows from the exact normalizer premise, over any field. -/
theorem subgroup_pointwiseFixer_le_trivialNormalizer_sup_sharpFixer_of_finite
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (H : Subgroup (rationalPoints G)) (Q : Subgroup (normalizerPoints i))
    (hQ : ∀ n ∈ Q, ∀ x : D.Apartment, n • x = x)
    (hQH : Q.map (normalizerPoints i).subtype ≤ H)
    (hS : ∀ Ω : Set D.Apartment, D.sharpFixer Ω ≤ H)
    (hN : D.HasNormalizerSharpFixers H Q)
    {Ω : Set D.Apartment} (hΩ : Ω.Finite) (hne : Ω.Nonempty) :
    H ⊓ D.pointwiseFixer (D.apartmentMap '' Ω) ≤
      Q.map (normalizerPoints i).subtype ⊔ D.sharpFixer Ω := by
  revert hne
  induction Ω, hΩ using Set.Finite.induction_on with
  | empty => exact fun hne => absurd hne Set.not_nonempty_empty
  | @insert a s ha hs ih =>
    intro _
    rcases s.eq_empty_or_nonempty with rfl | hsne
    · rw [insert_empty_eq]
      exact D.subgroup_pointwiseFixer_singleton_le_trivialNormalizer_sup_sharpFixer H Q hS hN a
    · intro g hg
      exact D.mem_trivialNormalizer_sup_sharpFixer_insert hG hi H Q hQ hQH hS hN hs hsne a hg
        (ih hsne ⟨hg.1, D.pointwiseFixer_image_anti (Set.subset_insert a s) hg.2⟩)

/-- Equality with the proposed join for every finite nonempty apartment subset. -/
theorem subgroup_pointwiseFixer_eq_trivialNormalizer_sup_sharpFixer_of_finite
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (H : Subgroup (rationalPoints G)) (Q : Subgroup (normalizerPoints i))
    (hQ : ∀ n ∈ Q, ∀ x : D.Apartment, n • x = x)
    (hQH : Q.map (normalizerPoints i).subtype ≤ H)
    (hS : ∀ Ω : Set D.Apartment, D.sharpFixer Ω ≤ H)
    (hN : D.HasNormalizerSharpFixers H Q)
    {Ω : Set D.Apartment} (hΩ : Ω.Finite) (hne : Ω.Nonempty) :
    H ⊓ D.pointwiseFixer (D.apartmentMap '' Ω) =
      Q.map (normalizerPoints i).subtype ⊔ D.sharpFixer Ω :=
  le_antisymm
    (D.subgroup_pointwiseFixer_le_trivialNormalizer_sup_sharpFixer_of_finite
      hG hi H Q hQ hQH hS hN hΩ hne)
    (D.trivialNormalizer_sup_sharpFixer_le_subgroup_pointwiseFixer H Q hQ hQH hS Ω)

/-- Choose `Q` as the intersection of `H` with the kernel of the apartment action. The
conditional finite-set comparison then has the whole-apartment fixer as constant factor. -/
theorem subgroup_pointwiseFixer_eq_wholeApartment_sup_sharpFixer_of_finite
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (H : Subgroup (rationalPoints G))
    (hS : ∀ Ω : Set D.Apartment, D.sharpFixer Ω ≤ H)
    (hN : D.HasNormalizerSharpFixers H
      (H.subgroupOf (normalizerPoints i) ⊓ D.normalizerAffineEquiv.ker))
    {Ω : Set D.Apartment} (hΩ : Ω.Finite) (hne : Ω.Nonempty) :
    H ⊓ D.pointwiseFixer (D.apartmentMap '' Ω) =
      (H ⊓ D.pointwiseFixer (D.apartmentMap '' Set.univ)) ⊔ D.sharpFixer Ω := by
  let Q := H.subgroupOf (normalizerPoints i) ⊓ D.normalizerAffineEquiv.ker
  have hQH : Q.map (normalizerPoints i).subtype ≤ H := by
    rintro g ⟨n, hn, rfl⟩
    exact hn.1
  have hQ : ∀ n ∈ Q, ∀ x : D.Apartment, n • x = x := by
    intro n hn x
    have heq : D.normalizerAffineEquiv n = 1 := hn.2
    have h := congrArg (fun e : D.Apartment ≃ᵃ[ℝ] D.Apartment => e x) heq
    simpa only [normalizerAffineEquiv_apply, AffineEquiv.coe_one, id_eq] using h
  have hfinite := D.subgroup_pointwiseFixer_le_trivialNormalizer_sup_sharpFixer_of_finite
    hG hi H Q hQ hQH hS hN hΩ hne
  apply le_antisymm
  · exact hfinite.trans (sup_le
      ((le_inf hQH (D.map_trivialNormalizer_le_pointwiseFixer_image Q hQ Set.univ)).trans
        le_sup_left) le_sup_right)
  · exact sup_le
      (le_inf inf_le_left (inf_le_right.trans (D.pointwiseFixer_image_anti (Set.subset_univ Ω))))
      (le_inf (hS Ω) (D.sharpFixer_le_pointwiseFixer_image Ω))

end Langlands.Geometry.Building.KPApartmentData
