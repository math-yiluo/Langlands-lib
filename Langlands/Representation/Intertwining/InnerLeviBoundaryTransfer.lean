import Langlands.Representation.Aubert.General.SemidirectIntersection
import Langlands.Representation.Intertwining.InnerLeviIntegrationDomain
import Langlands.Representation.Intertwining.PQRegularity
import Langlands.Representation.Exponents.LeviRadicalCompactSubgroups
import Langlands.Topology.CompactNormCharacter
import Langlands.Weil.Representation.ContinuityProof

/-! # Boundary supports and the half modulus for Renard VII.3.5 (ii)

For represented parabolics `P₁, P₂ ⊂ Q = LU` of `G` and their traces `P₁', P₂'` in `L`:

* the identity double coset `P₁(F)P₂(F)` meets `L(F)` exactly in `P₁'(F)P₂'(F)`, so a point of
  the boundary `closure(P₁'P₂') \ P₁'P₂'` in `L(F)` maps to the boundary
  `closure(P₁P₂) \ P₁P₂` in `G(F)`;
* the half modulus `c = δ_U^{1/2}` of `Q(F)` is trivial on the rational points of the
  unipotent radical of a parabolic of `L`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.HaarModulus

/-- The half modulus `δ_U^{1/2}` is trivial on every compact subgroup. -/
theorem closedHalfCharacter_eq_one_of_mem_isCompact {G : Type*} [Group G] [TopologicalSpace G]
    [LocallyCompactSpace G] [NonarchimedeanGroup G]
    (U P : Subgroup G) (hU : IsClosed (U : Set G)) (hPU : P ≤ Subgroup.normalizer (U : Set G))
    (J : Subgroup P) (hJ : IsCompact (J : Set P)) {p : P} (hp : p ∈ J) :
    closedHalfCharacter U hU P hPU p = 1 := by
  have hδ := RankinSelberg.LastRowReduction.eq_one_of_isCompact
    (closedRestrictCharacter U hU P hPU)
    (Weil.continuous_of_open_kernel _ (isOpen_ker_closedRestrictCharacter U hU P hPU)) J hJ hp
  let := hU.locallyCompactSpace
  change p ∈ (closedHalfCharacter U hU P hPU).ker
  rw [closedHalfCharacter_eq, halfCharacter_ker]
  exact hδ

end Langlands.HaarModulus

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- The identity double coset `P · 1 · Q` is the product set `P Q`. -/
theorem mem_identityDoubleCoset_iff {G : Type*} [Group G] (P Q : Subgroup G) (g : G) :
    g ∈ DoubleCoset.quotToDoubleCoset P Q (DoubleCoset.mk P Q 1) ↔
      g ∈ (P : Set G) * (Q : Set G) := by
  rw [DoubleCoset.mem_quotToDoubleCoset_iff, eq_comm, DoubleCoset.eq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, by rw [mul_one]⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, by rw [mul_one]⟩

variable {k : Type u} [Field k]

section LocalField

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]

/-- Renard VII.3.5 (ii): a point of `L(F)` whose image lies in `P₁(F)P₂(F)` lies in
`P₁'(F)P₂'(F)`, for parabolics `P₁, P₂ ⊂ Q = LU` with traces `Pᵢ'(F) = Pᵢ(F) ∩ L(F)`. -/
theorem mem_mul_of_map_mem_mul
    {G M P₁ N₁ P₂ N₂ Q L U P₁' N₁' P₂' N₂' : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G)
    (p₁ : P₁ ⟶ G) (l₁ : M ⟶ P₁) (r₁ : N₁ ⟶ P₁)
    (hp₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
    (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
    (hmul₁ : IsIso (subgroupMultiplication l₁ r₁))
    (p₂ : P₂ ⟶ G) (l₂ : M ⟶ P₂) (r₂ : N₂ ⟶ P₂)
    (hp₂ : IsParabolicSubgroup p₂) (hl₂ : IsRationalLeviSubgroup l₂)
    (hr₂ : LeviSubgroup.IsGeometricUnipotentRadical r₂)
    (hmul₂ : IsIso (subgroupMultiplication l₂ r₂))
    (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q)
    (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
    (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
    (hmulQ : IsIso (subgroupMultiplication lQ rQ))
    (hPQ₁ : pointImage p₁ ≤ pointImage q) (hPQ₂ : pointImage p₂ ≤ pointImage q)
    (p₁' : P₁' ⟶ L) (l₁' : M ⟶ P₁') (r₁' : N₁' ⟶ P₁')
    (hp₁' : IsParabolicSubgroup p₁') (hl₁' : IsRationalLeviSubgroup l₁')
    (hr₁' : LeviSubgroup.IsGeometricUnipotentRadical r₁')
    (hmul₁' : IsIso (subgroupMultiplication l₁' r₁'))
    (p₂' : P₂' ⟶ L) (l₂' : M ⟶ P₂') (r₂' : N₂' ⟶ P₂')
    (hp₂' : IsParabolicSubgroup p₂') (hl₂' : IsRationalLeviSubgroup l₂')
    (hr₂' : LeviSubgroup.IsGeometricUnipotentRadical r₂')
    (hmul₂' : IsIso (subgroupMultiplication l₂' r₂'))
    (hM₁ : l₁' ≫ p₁' ≫ lQ ≫ q = l₁ ≫ p₁) (hM₂ : l₂' ≫ p₂' ≫ lQ ≫ q = l₂ ≫ p₂)
    (hPL₁ : pointImage (p₁' ≫ lQ ≫ q) = pointImage p₁ ⊓ pointImage (lQ ≫ q))
    (hPL₂ : pointImage (p₂' ≫ lQ ≫ q) = pointImage p₂ ⊓ pointImage (lQ ≫ q))
    (x : rationalPoints L)
    (hx : rationalPoints.map (lQ ≫ q) x ∈
      (pointImage p₁ : Set (rationalPoints G)) * (pointImage p₂ : Set (rationalPoints G))) :
    x ∈ (pointImage p₁' : Set (rationalPoints L)) * (pointImage p₂' : Set (rationalPoints L)) := by
  have hjc : IsClosedSubgroup (lQ ≫ q) := hlQ.isClosedSubgroup.comp hq.isClosedSubgroup
  have : IsClosedImmersion (lQ ≫ q).hom.hom.left := hjc
  have : Mono (lQ ≫ q).hom.hom := Over.mono_of_mono_left _
  have hinj : Function.Injective (rationalPoints.map (lQ ≫ q)) := fun a b hab =>
    (cancel_mono (lQ ≫ q).hom.hom).mp hab
  obtain ⟨-, -, hdec₁⟩ := nestedParabolicPointDecomposition k G hG P₁ M N₁ Q L U P₁' N₁'
    p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁'
    hPQ₁ hM₁ (by rw [inf_comm]; exact hPL₁)
  obtain ⟨-, -, hdec₂⟩ := nestedParabolicPointDecomposition k G hG P₂ M N₂ Q L U P₂' N₂'
    p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ q lQ rQ hq hlQ hrQ hmulQ p₂' l₂' r₂' hp₂' hl₂' hr₂' hmul₂'
    hPQ₂ hM₂ (by rw [inf_comm]; exact hPL₂)
  have hsd := isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ
  obtain ⟨a, ha, b, hb, hab⟩ := hx
  have ha' : a ∈ ((pointImage (p₁' ≫ lQ ≫ q) : Set (rationalPoints G)) *
      (pointImage (rQ ≫ q) : Set (rationalPoints G))) := by
    rw [← hdec₁]
    exact ha
  have hb' : b ∈ ((pointImage (p₂' ≫ lQ ≫ q) : Set (rationalPoints G)) *
      (pointImage (rQ ≫ q) : Set (rationalPoints G))) := by
    rw [← hdec₂]
    exact hb
  obtain ⟨a', ⟨y₁, rfl⟩, u₁, hu₁, rfl⟩ := ha'
  obtain ⟨b', ⟨y₂, rfl⟩, u₂, hu₂, rfl⟩ := hb'
  -- the `L(F)`-parts are images of `yᵢ' = p_i'(yᵢ)`
  have hy₁ : rationalPoints.map (p₁' ≫ lQ ≫ q) y₁ =
      rationalPoints.map (lQ ≫ q) (rationalPoints.map p₁' y₁) := by
    simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
  have hy₂ : rationalPoints.map (p₂' ≫ lQ ≫ q) y₂ =
      rationalPoints.map (lQ ≫ q) (rationalPoints.map p₂' y₂) := by
    simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
  rw [hy₁, hy₂] at hab
  set z₁ := rationalPoints.map p₁' y₁
  set z₂ := rationalPoints.map p₂' y₂
  set e₁ := rationalPoints.map (lQ ≫ q) z₁
  set e₂ := rationalPoints.map (lQ ≫ q) z₂
  have he₂Q : e₂ ∈ pointImage q := pointImage_comp_le q lQ ⟨z₂, rfl⟩
  have hconj : e₂⁻¹ * u₁ * e₂ ∈ pointImage (rQ ≫ q) := by
    have h := (Subgroup.mem_normalizer_iff.mp (hsd.le_normalizer (inv_mem he₂Q)) u₁).mp hu₁
    simpa only [inv_inv] using h
  set u := e₂⁻¹ * u₁ * e₂ * u₂
  have huU : u ∈ pointImage (rQ ≫ q) := mul_mem hconj hu₂
  have hxe : rationalPoints.map (lQ ≫ q) x = e₁ * e₂ * u := by
    rw [← hab]
    simp only [u]
    group
  have huL : u ∈ pointImage (lQ ≫ q) := by
    have : u = (e₁ * e₂)⁻¹ * rationalPoints.map (lQ ≫ q) x := by
      rw [hxe]
      group
    rw [this]
    exact mul_mem (inv_mem (mul_mem ⟨z₁, rfl⟩ ⟨z₂, rfl⟩)) ⟨x, rfl⟩
  have hu1 : u = 1 := IsSemidirectDecomposition.eq_one_of_mem_of_mem hsd huL huU
  rw [hu1, mul_one, ← map_mul] at hxe
  exact ⟨z₁, ⟨y₁, rfl⟩, z₂, ⟨y₂, rfl⟩, (hinj hxe).symm⟩

/-- The identity double coset `P · 1 · Q`, as a set, is the product set `P Q`. -/
theorem identityDoubleCoset_eq {H : Type*} [Group H] (P Q : Subgroup H) :
    DoubleCoset.quotToDoubleCoset P Q (DoubleCoset.mk P Q 1) = (P : Set H) * (Q : Set H) :=
  Set.ext (mem_identityDoubleCoset_iff P Q)

section Topology

variable {G Q L U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance boundaryAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

/-- Renard VII.3.5 (ii): the half modulus `c = δ_U^{1/2}` of `Q(F) = L(F)U(F)` is trivial on
the rational points of the unipotent radical `N'` of a closed subgroup `P'` of `L`
(for instance a parabolic of `L`): these points form a union of compact subgroups. -/
theorem halfModulus_eq_one_of_mem_innerRadical
    [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
    {P' N' : GroupScheme (Spec (CommRingCat.of k))}
    (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q)
    (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
    (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
    (hmulQ : IsIso (subgroupMultiplication lQ rQ))
    (p' : P' ⟶ L) (r' : N' ⟶ P') (hp' : IsClosedSubgroup p')
    (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
    {x : rationalPoints L} (hx : x ∈ pointImage (r' ≫ p')) :
    HaarModulus.closedHalfCharacter (pointImage (rQ ≫ q))
        (isClosed_pointImage_comp q rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup)
        (pointImage q)
        (isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ).le_normalizer
        (Subgroup.inclusion (pointImage_comp_le q lQ) (leviPointsEquiv q lQ hq hlQ x)) = 1 := by
  have hj : IsClosedSubgroup (p' ≫ lQ ≫ q) :=
    hp'.comp (hlQ.isClosedSubgroup.comp hq.isClosedSubgroup)
  have hlim := isLimitOfCompactSubgroups_pointImage_radical (p' ≫ lQ ≫ q) r' hj hr'.1
  have hxN : rationalPoints.map (lQ ≫ q) x ∈ pointImage (r' ≫ p' ≫ lQ ≫ q) := by
    have h := map_mem_pointImage_comp (lQ ≫ q) hx
    simpa only [Category.assoc] using h
  have hNQ : pointImage (r' ≫ p' ≫ lQ ≫ q) ≤ pointImage q := by
    have h := pointImage_comp_le q (r' ≫ p' ≫ lQ)
    simpa only [Category.assoc] using h
  obtain ⟨K, hK, hxK⟩ := hlim {⟨_, hxN⟩} isCompact_singleton
  let J : Subgroup (pointImage q) := K.map (Subgroup.inclusion hNQ)
  have hJ : IsCompact (J : Set (pointImage q)) := by
    change IsCompact (Subgroup.inclusion hNQ '' (K : Set _))
    exact hK.image (continuous_subtype_val.subtype_mk _)
  apply HaarModulus.closedHalfCharacter_eq_one_of_mem_isCompact _ _ _ _ J hJ
  refine ⟨⟨_, hxN⟩, hxK rfl, ?_⟩
  rfl

variable {M P₁ N₁ P₂ N₂ P₁' N₁' P₂' N₂' : GroupScheme (Spec (CommRingCat.of k))}

/-- Renard VII.3.5 (ii): a point of the boundary `closure(P₁'P₂') \ P₁'P₂'` in `L(F)` maps to
the boundary `closure(P₁P₂) \ P₁P₂` in `G(F)`. -/
theorem map_mem_identityBoundary
    (hG : IsConnectedReductive G)
    (p₁ : P₁ ⟶ G) (l₁ : M ⟶ P₁) (r₁ : N₁ ⟶ P₁)
    (hp₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
    (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
    (hmul₁ : IsIso (subgroupMultiplication l₁ r₁))
    (p₂ : P₂ ⟶ G) (l₂ : M ⟶ P₂) (r₂ : N₂ ⟶ P₂)
    (hp₂ : IsParabolicSubgroup p₂) (hl₂ : IsRationalLeviSubgroup l₂)
    (hr₂ : LeviSubgroup.IsGeometricUnipotentRadical r₂)
    (hmul₂ : IsIso (subgroupMultiplication l₂ r₂))
    (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q)
    (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
    (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
    (hmulQ : IsIso (subgroupMultiplication lQ rQ))
    (hPQ₁ : pointImage p₁ ≤ pointImage q) (hPQ₂ : pointImage p₂ ≤ pointImage q)
    (p₁' : P₁' ⟶ L) (l₁' : M ⟶ P₁') (r₁' : N₁' ⟶ P₁')
    (hp₁' : IsParabolicSubgroup p₁') (hl₁' : IsRationalLeviSubgroup l₁')
    (hr₁' : LeviSubgroup.IsGeometricUnipotentRadical r₁')
    (hmul₁' : IsIso (subgroupMultiplication l₁' r₁'))
    (p₂' : P₂' ⟶ L) (l₂' : M ⟶ P₂') (r₂' : N₂' ⟶ P₂')
    (hp₂' : IsParabolicSubgroup p₂') (hl₂' : IsRationalLeviSubgroup l₂')
    (hr₂' : LeviSubgroup.IsGeometricUnipotentRadical r₂')
    (hmul₂' : IsIso (subgroupMultiplication l₂' r₂'))
    (hM₁ : l₁' ≫ p₁' ≫ lQ ≫ q = l₁ ≫ p₁) (hM₂ : l₂' ≫ p₂' ≫ lQ ≫ q = l₂ ≫ p₂)
    (hPL₁ : pointImage (p₁' ≫ lQ ≫ q) = pointImage p₁ ⊓ pointImage (lQ ≫ q))
    (hPL₂ : pointImage (p₂' ≫ lQ ≫ q) = pointImage p₂ ⊓ pointImage (lQ ≫ q)) :
    haveI := hlQ.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints L) := RationalPointFamily.pointTopology
    ∀ x : rationalPoints L,
      x ∈ closure (DoubleCoset.quotToDoubleCoset (pointImage p₁') (pointImage p₂')
          (identityParabolicDoubleCoset p₁' p₂')) \
        DoubleCoset.quotToDoubleCoset (pointImage p₁') (pointImage p₂')
          (identityParabolicDoubleCoset p₁' p₂') →
      rationalPoints.map (lQ ≫ q) x ∈
        closure (DoubleCoset.quotToDoubleCoset (pointImage p₁) (pointImage p₂)
          (identityParabolicDoubleCoset p₁ p₂)) \
        DoubleCoset.quotToDoubleCoset (pointImage p₁) (pointImage p₂)
          (identityParabolicDoubleCoset p₁ p₂) := by
  let := hlQ.isConnectedReductive.isAffineHom
  intro x hx
  have hcont : Continuous (rationalPoints.map (lQ ≫ q)) :=
    (isEmbedding_leviPoints q lQ hq hlQ).continuous
  simp only [identityParabolicDoubleCoset, identityDoubleCoset_eq] at hx ⊢
  obtain ⟨hcl, hnot⟩ := hx
  refine ⟨?_, fun h => hnot (mem_mul_of_map_mem_mul hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
    p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ q lQ rQ hq hlQ hrQ hmulQ hPQ₁ hPQ₂
    p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' p₂' l₂' r₂' hp₂' hl₂' hr₂' hmul₂' hM₁ hM₂ hPL₁ hPL₂ x h)⟩
  have himg : rationalPoints.map (lQ ≫ q) ''
      ((pointImage p₁' : Set (rationalPoints L)) * (pointImage p₂' : Set (rationalPoints L))) ⊆
      (pointImage p₁ : Set (rationalPoints G)) * (pointImage p₂ : Set (rationalPoints G)) := by
    rintro _ ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    refine ⟨rationalPoints.map (lQ ≫ q) a, ?_, rationalPoints.map (lQ ≫ q) b, ?_,
      (map_mul _ a b).symm⟩
    · have h := map_mem_pointImage_comp (lQ ≫ q) ha
      rw [hPL₁] at h
      exact h.1
    · have h := map_mem_pointImage_comp (lQ ≫ q) hb
      rw [hPL₂] at h
      exact h.1
  exact closure_mono himg (image_closure_subset_closure_image hcont ⟨x, hcl, rfl⟩)

end Topology

end LocalField

end Langlands.Aubert.General.RepresentedParabolic
