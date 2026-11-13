import Langlands.Global.AdelicSplitFundamentalSetFromRankOne
import Langlands.Global.AdelicParabolicCompactCover
import Langlands.Global.SplitRankOneAdelic

/-! # Springer's split fundamental set from the split rank-one bound alone -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Pointwise

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints RepresentationGrowth

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (ν : cocharacterLattice T)
  (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)

/-- A compact norm-one cover of the minimal parabolic and the parabolic factors give
the `n m a k` factorization of every ambient norm-one point, with `k` in the cover. -/
theorem HasMinimalParabolicNormFactors.exists_cover_factors
    (h : HasMinimalParabolicNormFactors F G T i ν T₀ j)
    (Ω : Set (AdelicGroupPoints F G))
    (hΩ1 : Ω ⊆ (normOneSubgroup F G : Set (AdelicGroupPoints F G)))
    (hcov : Set.range (map F (Standard.parabolicScheme i ν ∅) G
      (Standard.parabolicHom i ν ∅)) * Ω = Set.univ)
    (g : normOneSubgroup F G) :
    ∃ (n : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅))
      (m : normOneSubgroup F (Standard.leviScheme i ν ∅))
      (a : PositiveRealTorus.intrinsicSubgroup F T₀),
      ∃ k ∈ Ω, map F _ G (Standard.unipotentHom i ν ∅) n *
        map F _ G (Standard.leviHom i ν ∅) m *
        positiveMap F G T i T₀ j a * k = g := by
  have hg : (g : AdelicGroupPoints F G) ∈
      Set.range (map F (Standard.parabolicScheme i ν ∅) G
        (Standard.parabolicHom i ν ∅)) * Ω := by
    rw [hcov]
    exact Set.mem_univ _
  obtain ⟨_, ⟨p, rfl⟩, k, hk, hpk⟩ := hg
  have hpone : map F _ G (Standard.parabolicHom i ν ∅) p ∈ normOneSubgroup F G := by
    have hp : map F _ G (Standard.parabolicHom i ν ∅) p =
        (g : AdelicGroupPoints F G) * k⁻¹ := by
      rw [← hpk, mul_inv_cancel_right]
    rw [hp]
    exact (normOneSubgroup F G).mul_mem g.2 ((normOneSubgroup F G).inv_mem (hΩ1 hk))
  obtain ⟨n, m, a, hma⟩ := h ⟨_, hpone⟩ ⟨p, rfl⟩
  exact ⟨n, m, a, k, hk, by rw [hma]; exact hpk⟩

/-- The weak-chamber factorization for fixed actual algebraic data and one compact
**set** `Ω` of adelic points: the set version of `HasWeakChamberReduction`, with
`k ∈ Ω` in place of membership in a compact subgroup. -/
def HasWeakChamberCoverReduction (Ω : Set (AdelicGroupPoints F G)) : Prop :=
  ∃ t : ℝ≥0ˣ, ∀ g : normOneSubgroup F G, ∃ q : RationalGroupPoints F G,
    ∃ (n : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅))
      (m : normOneSubgroup F (Standard.leviScheme i ν ∅))
      (a : PositiveRealTorus.intrinsicSubgroup F T₀),
      a ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t ∧
        ∃ k ∈ Ω,
          map F _ G (Standard.unipotentHom i ν ∅) n *
              map F _ G (Standard.leviHom i ν ∅) m *
              positiveMap F G T i T₀ j a * k = rational F G q * g

/-- A weak-chamber reduction for a subgroup `K` is one for the underlying set of `K`. -/
theorem HasWeakChamberReduction.hasWeakChamberCoverReduction
    {K : Subgroup (AdelicGroupPoints F G)}
    (h : HasWeakChamberReduction F G T i ν T₀ j K) :
    HasWeakChamberCoverReduction F G T i ν T₀ j (K : Set (AdelicGroupPoints F G)) :=
  h

/-- The weak chamber factorization of `hasWeakChamberReduction_of_rootLeviHeightBounds`
with the Iwasawa compact subgroup replaced by a compact norm-one cover `Ω` of the minimal
parabolic. The proof is that one, with `Ω⁻¹` as the compact set for height transport. -/
theorem exists_weakChamberFactorization_of_rootLeviHeightBounds_of_cover
    [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G)
    (hS : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    (hroot : HasRootLeviHeightBounds F G T i ν)
    (Ω : Set (AdelicGroupPoints F G)) (hΩc : IsCompact Ω)
    (hΩ1 : Ω ⊆ (normOneSubgroup F G : Set (AdelicGroupPoints F G)))
    (hcov : Set.range (map F (Standard.parabolicScheme i ν ∅) G
      (Standard.parabolicHom i ν ∅)) * Ω = Set.univ) :
    ∃ t : ℝ≥0ˣ, ∀ g : normOneSubgroup F G, ∃ q : RationalGroupPoints F G,
      ∃ (n : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅))
        (m : normOneSubgroup F (Standard.leviScheme i ν ∅))
        (a : PositiveRealTorus.intrinsicSubgroup F T₀),
        a ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t ∧
          ∃ k ∈ Ω,
            map F _ G (Standard.unipotentHom i ν ∅) n *
                map F _ G (Standard.leviHom i ν ∅) m *
                positiveMap F G T i T₀ j a * k = rational F G q * g := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  classical
  let Δ := simpleRelativeRoots i ν
  have hfinite : Δ.Finite := hS.1.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  let : Fintype Δ := hfinite.fintype
  let r := Fintype.card Δ
  let e : Fin r ≃ Δ := (Fintype.equivFin Δ).symm
  let α : ℕ → characterLattice T := fun l =>
    if h : l < r then (e ⟨l, h⟩).val else 0
  have hα (l : ℕ) (hl : l < r) : α l ∈ Δ := by
    simpa only [α, dite_eq_left hl] using (e ⟨l, hl⟩).property
  have hinj (a l : ℕ) (ha : a < r) (hl : l < r) (heq : α a = α l) : a = l := by
    simp only [α, dite_eq_left ha, dite_eq_left hl] at heq
    exact congrArg Fin.val (e.injective (Subtype.ext heq))
  have hcover (β : characterLattice T) (hβ : β ∈ Δ) :
      ∃ l, l < r ∧ α l = β := by
    let l := e.symm ⟨β, hβ⟩
    refine ⟨l.val, l.isLt, ?_⟩
    simp only [α, dite_eq_left l.isLt, Fin.eta]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨β, hβ⟩)
  let J : ℕ → Set (characterLattice T) := fun l => Δ \ {α l}
  have hJ (l : ℕ) : J l ⊆ simpleRelativeRoots i ν := fun _ h => h.1
  obtain ⟨d, b, ρ, hstab, _, hmin⟩ :=
    exists_adapted_standardParabolicPrefix_minima F G T i ν J
  let d' : ℕ → ℕ := fun l => d l + 1
  let Q := closedPrefixRationalSubgroup F G
    (fun l => Standard.parabolicScheme i ν (J l))
    (fun l => Standard.parabolicHom i ν (J l))
  have hv (l : ℕ) (_ : l < r) :
      (Pi.single (b l) 1 : Fin (d' l) → F) ≠ 0 := by
    intro hz
    have he := congrFun hz (b l)
    simp at he
  obtain ⟨D, hD, htransport⟩ := exists_pos_chainHeightMinimalSet_compact_transport
    F G r d' ρ (fun l _ => Nat.zero_lt_succ (d l)) hΩc.inv
  let S : Set (AdelicGroupPoints F T.toGrp) := {s |
    ∃ (m : normOneSubgroup F (Standard.leviScheme i ν ∅))
      (x : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅)),
      map F _ G (Standard.leviHom i ν ∅) m * map F _ G i s *
          map F _ G (Standard.unipotentHom i ν ∅) x ∈
        adelicChainHeightMinimalSet F G r d' ρ (fun l => Pi.single (b l) 1) Q D}
  have hbound : PositiveRealTorus.HasUniformSimpleRootBound F G T i ν S := by
    apply PositiveRealTorus.hasUniformSimpleRootBound_of_character_bounds
      F G T i ν hfinite S
    intro β hβ
    obtain ⟨l, hl, rfl⟩ := hcover β hβ
    apply hasUniformRootBound_of_minimal_coordinates_and_prefix_minima_of_rootLevi
      F G T i ν hroot hG hS.1 hS.2.1 J hJ r d' ρ b l hl (hstab l)
        (α l) (hα l hl) (by simp [J]) (fun a ha => ?_) D hD S
    · exact fun _ hs => hs
    · refine ⟨hα l hl, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro heq
      have heq' := hinj l a hl (ha.trans hl) heq
      omega
  obtain ⟨t, ht⟩ := hbound.exists_lower_inv F G T i ν
  let s : PositiveRealTorus.intrinsicSubgroup F T₀ → AdelicGroupPoints F T.toGrp :=
    fun a => map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) a
  have hs (a : PositiveRealTorus.intrinsicSubgroup F T₀) :
      map F T.toGrp G i (s a) = positiveMap F G T i T₀ j a := by
    change (a.val ≫ (CommGroupScheme.groupHom j).hom.hom) ≫ i.hom.hom =
      a.val ≫ (CommGroupScheme.groupHom j ≫ i).hom.hom
    rw [Grp.comp_hom_hom, Category.assoc]
  refine ⟨t, fun g => ?_⟩
  obtain ⟨q, hq⟩ := hmin r g⁻¹
  let y : normOneSubgroup F G := g⁻¹ * rationalNormOne F G q
  let z : normOneSubgroup F G := rationalNormOne F G q⁻¹ * g
  have hzy : z⁻¹ = y := by
    simp only [z, y, mul_inv_rev, map_inv, inv_inv]
  obtain ⟨x, m, a, k, hk, heq⟩ := HasMinimalParabolicNormFactors.exists_cover_factors
    F G T i ν T₀ j (hS.hasMinimalParabolicNormFactors F G T i ν T₀ j hG) Ω hΩ1 hcov z
  let p₀ := map F _ G (Standard.unipotentHom i ν ∅) x *
    map F _ G (Standard.leviHom i ν ∅) m * positiveMap F G T i T₀ j a
  have hp₀ : p₀ = (z : AdelicGroupPoints F G) * k⁻¹ := by
    rw [← heq]
    simp only [p₀, mul_inv_cancel_right]
  have hpone : p₀⁻¹ ∈ normOneSubgroup F G := by
    rw [hp₀]
    exact (normOneSubgroup F G).inv_mem ((normOneSubgroup F G).mul_mem z.property
      ((normOneSubgroup F G).inv_mem (hΩ1 hk)))
  let p : normOneSubgroup F G := ⟨p₀⁻¹, hpone⟩
  let k' : normOneSubgroup F G := ⟨k⁻¹, (normOneSubgroup F G).inv_mem (hΩ1 hk)⟩
  have hk'p : k' * p = y := by
    apply Subtype.ext
    change k⁻¹ * p₀⁻¹ = (y : AdelicGroupPoints F G)
    rw [← mul_inv_rev]
    change (p₀ * k)⁻¹ = (y : AdelicGroupPoints F G)
    rw [heq]
    exact congrArg Subtype.val hzy
  have hpmin : p ∈ chainHeightMinimalSet F G r d' ρ
      (fun l => Pi.single (b l) 1) Q D := by
    have h := (htransport (fun l => Pi.single (b l) 1) hv Q k' (Set.inv_mem_inv.mpr hk)
      p 1 zero_le_one).2 (hk'p.symm ▸ hq)
    simpa only [mul_one] using h
  have hporder :
      map F _ G (Standard.leviHom i ν ∅) (m⁻¹ : normOneSubgroup F _) *
        map F _ G i (s a)⁻¹ * map F _ G (Standard.unipotentHom i ν ∅) x⁻¹ =
          (p : AdelicGroupPoints F G) := by
    have hc := (hS.commute_torus_minimalLevi F G T i ν T₀ j (s a) m).inv_inv
    simp only [hs] at hc
    change _ = p₀⁻¹
    simp only [p₀, mul_inv_rev, Subgroup.coe_inv, map_inv, hs]
    rw [← mul_assoc, hc.eq]
  have hsa : (s a)⁻¹ ∈ S := by
    refine ⟨m⁻¹, x⁻¹, ?_⟩
    rw [hporder]
    exact hpmin
  have ha : a ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t := by
    intro β hβ
    have h := ht β hβ (s a)⁻¹ hsa
    rw [inv_inv] at h
    exact (PositiveRealTorus.normCharacter_pullback F T₀ T j β a).symm ▸ h
  refine ⟨q⁻¹, x, m, a, ha, k, hk, ?_⟩
  simpa only [z, Subgroup.coe_mul, rationalNormOne_val] using heq

/-- `exists_weakChamberFactorization_of_rootLeviHeightBounds_of_cover`, stated with
`HasWeakChamberCoverReduction`. -/
theorem hasWeakChamberCoverReduction_of_rootLeviHeightBounds
    [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G)
    (hS : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    (hroot : HasRootLeviHeightBounds F G T i ν)
    (Ω : Set (AdelicGroupPoints F G)) (hΩc : IsCompact Ω)
    (hΩ1 : Ω ⊆ (normOneSubgroup F G : Set (AdelicGroupPoints F G)))
    (hcov : Set.range (map F (Standard.parabolicScheme i ν ∅) G
      (Standard.parabolicHom i ν ∅)) * Ω = Set.univ) :
    HasWeakChamberCoverReduction F G T i ν T₀ j Ω :=
  exists_weakChamberFactorization_of_rootLeviHeightBounds_of_cover
    F G T i ν T₀ j hG hS hroot Ω hΩc hΩ1 hcov

/-- A compact norm-one cover of the minimal parabolic and the root-Levi height bounds
give Springer's right fundamental set. Apply the factorization to `g⁻¹` and invert; the
compact factor is `Ω⁻¹`. This is `HasWeakChamberReduction.hasRightAdelicFundamentalSet`
with a compact set in place of a compact subgroup. -/
theorem hasRightAdelicFundamentalSet_of_rootLeviHeightBounds_of_cover
    [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G)
    (hS : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    (hroot : HasRootLeviHeightBounds F G T i ν)
    (Ω : Set (AdelicGroupPoints F G)) (hΩc : IsCompact Ω)
    (hΩ1 : Ω ⊆ (normOneSubgroup F G : Set (AdelicGroupPoints F G)))
    (hcov : Set.range (map F (Standard.parabolicScheme i ν ∅) G
      (Standard.parabolicHom i ν ∅)) * Ω = Set.univ) :
    HasRightAdelicFundamentalSet F G T i ν := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨t, ht⟩ := exists_weakChamberFactorization_of_rootLeviHeightBounds_of_cover
    F G T i ν T₀ j hG hS hroot Ω hΩc hΩ1 hcov
  have hΩinv : Ω⁻¹ ⊆ (normOneSubgroup F G : Set (AdelicGroupPoints F G)) := by
    intro y hy
    have hy' := (normOneSubgroup F G).inv_mem (hΩ1 (Set.mem_inv.mp hy))
    rwa [inv_inv] at hy'
  refine ⟨{x | (x : AdelicGroupPoints F G) ∈ Ω⁻¹}, ?_, t⁻¹, fun g => ?_⟩
  · rw [Subtype.isCompact_iff]
    convert hΩc.inv using 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, hΩinv hy⟩, hy, rfl⟩
  obtain ⟨q, n, m, a, ha, k, hk, heq⟩ := ht g⁻¹
  let s : AdelicGroupPoints F T.toGrp :=
    (map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) (a : AdelicGroupPoints F T₀.toGrp))⁻¹
  have hs : map F T.toGrp G i s = (positiveMap F G T i T₀ j a)⁻¹ := by
    simp only [s, map_inv]
    congr 1
  have hlevi : map F _ _ (Standard.leviToParabolic i ν ∅)
      ((m : AdelicGroupPoints F _)⁻¹) ∈ normOneSubgroup F (Standard.parabolicScheme i ν ∅) :=
    map_normOneSubgroup_le F _ _ (Standard.leviToParabolic i ν ∅)
      ⟨_, (normOneSubgroup F _).inv_mem m.property, rfl⟩
  have hunip : map F _ _ (Standard.unipotentToParabolic i ν ∅) n⁻¹ ∈
      normOneSubgroup F (Standard.parabolicScheme i ν ∅) :=
    range_le_normOne_of_charactersTrivialAlong F _ _ (Standard.unipotentToParabolic i ν ∅)
      (charactersTrivialAlong_of_isUnipotent F _ _ _
        (hS.isUnipotent_standard F G T i ν T₀ j)) ⟨n⁻¹, rfl⟩
  let p : normOneSubgroup F (Standard.parabolicScheme i ν ∅) :=
    ⟨_, (normOneSubgroup F _).mul_mem hlevi hunip⟩
  have hp : map F _ G (Standard.parabolicHom i ν ∅) p =
      (map F _ G (Standard.leviHom i ν ∅) m)⁻¹ *
        (map F _ G (Standard.unipotentHom i ν ∅) n)⁻¹ := by
    change map F _ G (Standard.parabolicHom i ν ∅)
        (map F _ _ (Standard.leviToParabolic i ν ∅) ((m : AdelicGroupPoints F _)⁻¹) *
          map F _ _ (Standard.unipotentToParabolic i ν ∅) n⁻¹) = _
    rw [map_mul, ← adelicPointsMap_comp_apply, ← adelicPointsMap_comp_apply,
      Standard.leviToParabolic_comp, Standard.unipotentToParabolic_comp, map_inv, map_inv]
  refine ⟨q, s, p, ?_, ?_, ⟨k⁻¹, (normOneSubgroup F G).inv_mem (hΩ1 hk)⟩,
    Set.inv_mem_inv.mpr hk, ?_⟩
  · rw [hs]
    exact (normOneSubgroup F G).inv_mem (hS.positiveMap_mem_normOne F G T i ν T₀ j a)
  · intro α hα
    have h := ha α hα
    rw [PositiveRealTorus.normCharacter_pullback] at h
    simp only [s, map_inv]
    exact inv_le_inv' h
  · rw [hs, hp]
    change k⁻¹ * (positiveMap F G T i T₀ j a)⁻¹ *
      ((map F _ G (Standard.leviHom i ν ∅) m)⁻¹ *
        (map F _ G (Standard.unipotentHom i ν ∅) n)⁻¹) * rational F G q = g
    calc k⁻¹ * (positiveMap F G T i T₀ j a)⁻¹ *
          ((map F _ G (Standard.leviHom i ν ∅) m)⁻¹ *
            (map F _ G (Standard.unipotentHom i ν ∅) n)⁻¹) * rational F G q
        = (map F _ G (Standard.unipotentHom i ν ∅) n *
            map F _ G (Standard.leviHom i ν ∅) m *
            positiveMap F G T i T₀ j a * k)⁻¹ * rational F G q := by group
      _ = g := by rw [heq, Subgroup.coe_inv]; group

/-- The root-Levi height bounds alone give Springer's right fundamental set: the compact
norm-one cover is supplied unconditionally by
`IsSiegelAlgebraicSetup.hasCompactNormOneParabolicCover`. -/
theorem hasRightAdelicFundamentalSet_of_rootLeviHeightBounds
    [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G)
    (hS : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    (hroot : HasRootLeviHeightBounds F G T i ν) :
    HasRightAdelicFundamentalSet F G T i ν := by
  obtain ⟨Ω, hΩc, hΩ1, hcov⟩ := hS.hasCompactNormOneParabolicCover F G T i ν T₀ j hG
  exact hasRightAdelicFundamentalSet_of_rootLeviHeightBounds_of_cover
    F G T i ν T₀ j hG hS hroot Ω hΩc hΩ1 hcov

/-- **Split fundamental sets from the split rank-one bound alone.** The split rank-one
height bound gives Springer's split fundamental-set theorem, with no Iwasawa premise. -/
theorem splitAdelicFundamentalSet_of_splitRankOne
    (hsplit : SplitRankOneParabolicRationalOrbitHeightBoundStatement.{u}) :
    SplitAdelicFundamentalSetStatement.{u} := by
  intro F _ _ G _ _ hG T i ν T₀ j hS hT
  exact hasRightAdelicFundamentalSet_of_rootLeviHeightBounds F G T i ν T₀ j hG hS
    (hasRootLeviHeightBounds_of_splitRankOne F G T i ν hsplit hG hS.1 hT hS.2.1)

/-- **Springer's split fundamental-set theorem.** Every split connected reductive group
over a number field has a right adelic fundamental set: the conditional theorem
`splitAdelicFundamentalSet_of_splitRankOne` applied to the published split rank-one
height bound. -/
theorem splitAdelicFundamentalSet : SplitAdelicFundamentalSetStatement.{u} :=
  splitAdelicFundamentalSet_of_splitRankOne splitRankOneParabolicRationalOrbitHeightBound

end Langlands.Global.AdelicSiegelFactors
