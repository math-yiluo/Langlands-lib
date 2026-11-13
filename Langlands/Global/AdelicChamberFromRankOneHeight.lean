import Langlands.Global.AdelicChamberFromRootLeviBounds
import Langlands.Global.AdelicPositiveDecompositionReduction
import Langlands.Global.PositiveTorusProductLifting
import Langlands.Global.AdelicSiegelNormOne
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof

/-! # Minimal-parabolic norm-one factors and chamber reduction from the rank-one bound -/

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

/-- Every ambient norm-one point of the actual minimal parabolic `P(𝔸_F)` is an
ordered product `n m a` of a unipotent point, a norm-one minimal-Levi point and an
intrinsic positive point of `T₀`. Only existence of the factors is asserted. -/
def HasMinimalParabolicNormFactors : Prop :=
  ∀ p : normOneSubgroup F G, (p : AdelicGroupPoints F G) ∈ standardParabolicImage F G T i ν →
    ∃ (n : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅))
      (m : normOneSubgroup F (Standard.leviScheme i ν ∅))
      (a : PositiveRealTorus.intrinsicSubgroup F T₀),
      map F _ G (Standard.unipotentHom i ν ∅) n *
        map F _ G (Standard.leviHom i ν ∅) m *
        positiveMap F G T i T₀ j a = p

omit [IsAffineHom G.X.hom] in
/-- The adelic-point map of a composite is the composite of the adelic-point maps. -/
theorem adelicPointsMap_comp_apply {H K : GroupScheme (Spec (CommRingCat.of F))}
    (f : H ⟶ K) (g : K ⟶ G) (x : AdelicGroupPoints F H) :
    map F H G (f ≫ g) x = map F K G g (map F H K f x) := by
  simp only [map_apply, GroupScheme.affinePointsTarget_apply, Grp.comp_hom_hom,
    Category.assoc]

/-- The actual algebraic Siegel setup supplies the minimal-parabolic norm-one factors.
The Levi retraction splits off the unipotent factor; the positive decomposition of the
minimal Levi along its central maximal split torus `T` splits off a positive point of `T`;
this point lifts through the surjective product `T₀ × Z₀ → T`; and the `Z₀` part is
trivial because `Z₀` is a split component of `G` and every other factor is norm one. -/
theorem IsSiegelAlgebraicSetup.hasMinimalParabolicNormFactors
    (hG : IsConnectedReductive G)
    (hS : IsSiegelAlgebraicSetup F G T i ν T₀ j) :
    HasMinimalParabolicNormFactors F G T i ν T₀ j := by
  classical
  intro p hp
  have hSetup := hS
  obtain ⟨hTmax, -, -, hRL, -, hlevi, -, ⟨D, d, t₀, -, hT₀max, -⟩, Z₀, z, hZ, hsurj⟩ :=
    hSetup
  -- the Levi retraction
  obtain ⟨f, -, hfM, hfid, hfker⟩ := exists_standardLeviPart F G T i ν T₀ j hS
  let pp : standardParabolicImage F G T i ν := ⟨p, hp⟩
  have hfpP : f pp ∈ standardParabolicImage F G T i ν :=
    standardLeviImage_le_parabolic F G T i ν (hfM pp)
  have hu : (p : AdelicGroupPoints F G) * (f pp)⁻¹ ∈ standardUnipotentImage F G T i ν := by
    have h := (hfker (pp * (⟨f pp, hfpP⟩ : standardParabolicImage F G T i ν)⁻¹)).mp (by
      rw [map_mul, map_inv, hfid _ (hfM pp), mul_inv_cancel])
    exact h
  obtain ⟨n, hn⟩ := hu
  obtain ⟨mM, hmM⟩ := hfM pp
  -- the positive decomposition of the minimal Levi
  have hMc := Standard.isClosedSubgroup_leviHom i ν ∅
  have : IsAffineHom (Standard.leviScheme i ν ∅).X.hom := hMc.isAffineHom
  have hmax : IsMaximalSplitTorus (torusToStandardLevi F G T i ν) :=
    hTmax.isMaximalSplitTorus_standardLeviTorusFactor i ν ∅
      (Standard.isRepresentedBy_leviHom i ν ∅) hMc
  have hcent : IsCentral (torusToStandardLevi F G T i ν) := by
    apply isCentral_of_range_le_torusCentralizer
      (Standard.isRepresentedBy_leviHom i ν ∅).1
    rw [torusToStandardLevi_comp, (Standard.isRepresentedBy_leviHom i ν ∅).2, hlevi]
  have hsplitM : IsSplitComponent (torusToStandardLevi F G T i ν) :=
    ⟨⟨hmax.1, hcent⟩, fun A' i' hi' g hg => hmax.2 A' i' hi'.1 g hg⟩
  obtain ⟨⟨aT, nM⟩, hEM⟩ := (PositiveRealTorus.splitComponentNormOneDecomposition
    centralSplitTorusCharacter F (Standard.leviScheme i ν ∅) hRL.isConnectedReductive T
    (torusToStandardLevi F G T i ν) hsplitM).surjective mM
  rw [PositiveRealTorus.splitComponentNormOneDecomposition_apply] at hEM
  -- lifting the positive torus point through `T₀ × Z₀ → T`
  obtain ⟨a₀, z₀, haz⟩ :=
    PositiveRealTorus.hasPositiveProductFactorization_of_surjective_product F T T₀ Z₀ j z
      hTmax.isSplitSubtorus.1 hT₀max.isSplitSubtorus.1 hZ.1.1.1 hsurj aT
  -- the ambient values of the factors
  set U := map F _ G (Standard.unipotentHom i ν ∅) n with hUdef
  set L := map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) (nM : AdelicGroupPoints F (Standard.leviScheme i ν ∅)) with hLdef
  set P₀ := positiveMap F G T i T₀ j a₀ with hP₀def
  set Z := map F Z₀.toGrp G (CommGroupScheme.groupHom z ≫ i)
    (z₀ : AdelicGroupPoints F Z₀.toGrp) with hZdef
  have hiaT : map F T.toGrp G i (aT : AdelicGroupPoints F T.toGrp) = P₀ * Z := by
    rw [← haz, map_mul]
    congr 1
  have hmM' : map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) mM = L * (P₀ * Z) := by
    rw [← hEM, (PositiveRealTorus.positivePointMap_commute F (Standard.leviScheme i ν ∅) T _ hcent aT nM).eq,
      map_mul, ← hiaT, PositiveRealTorus.positivePointMap_apply,
      ← adelicPointsMap_comp_apply, torusToStandardLevi_comp]
  have hpU : (p : AdelicGroupPoints F G) = U * (L * (P₀ * Z)) := by
    rw [← hmM']
    change _ = (map F _ G (Standard.unipotentHom i ν ∅)).toMonoidHom n *
      (map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅)).toMonoidHom mM
    rw [hn, hmM, inv_mul_cancel_right]
  -- every factor except `Z` is norm one
  have hU1 : U ∈ normOneSubgroup F G :=
    range_le_normOne_of_charactersTrivialAlong F _ G _
      (hS.charactersTrivialAlong_unipotent F G T i ν T₀ j) ⟨n, rfl⟩
  have hL1 : L ∈ normOneSubgroup F G :=
    map_normOneSubgroup_le F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) ⟨nM, nM.property, rfl⟩
  have hP₀1 : P₀ ∈ normOneSubgroup F G := hS.positiveMap_mem_normOne F G T i ν T₀ j a₀
  have hX1 : U * L * P₀ ∈ normOneSubgroup F G :=
    (normOneSubgroup F G).mul_mem ((normOneSubgroup F G).mul_mem hU1 hL1) hP₀1
  have hZ1 : Z ∈ normOneSubgroup F G := by
    have hZeq : Z = (U * L * P₀)⁻¹ * p := by
      rw [hpU]
      group
    rw [hZeq]
    exact (normOneSubgroup F G).mul_mem ((normOneSubgroup F G).inv_mem hX1) p.property
  -- the positive decomposition of `G` along its split component `Z₀` forces `Z = 1`
  have hZone : Z = 1 := by
    let EG := PositiveRealTorus.splitComponentNormOneDecomposition
      centralSplitTorusCharacter F G hG Z₀ (CommGroupScheme.groupHom z ≫ i) hZ
    have heq : EG (z₀, 1) = EG (1, ⟨Z, hZ1⟩) := by
      simp only [EG, PositiveRealTorus.splitComponentNormOneDecomposition_apply,
        PositiveRealTorus.positivePointMap_apply, map_one, OneMemClass.coe_one, mul_one,
        one_mul]
      rfl
    have h2 := congrArg (fun x => ((Prod.snd x : normOneSubgroup F G) : AdelicGroupPoints F G))
      (EG.injective heq)
    exact h2.symm
  refine ⟨n, nM, a₀, ?_⟩
  rw [hpU, hZone, mul_one, mul_assoc]

/-- Iwasawa coverage and the parabolic factors give the unrestricted `n m a k`
factorization of every ambient norm-one point. -/
theorem HasMinimalParabolicNormFactors.exists_iwasawa_factors
    (h : HasMinimalParabolicNormFactors F G T i ν T₀ j)
    (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsParabolicIwasawaCompact F G
      (Standard.parabolicScheme i ν ∅) (Standard.parabolicHom i ν ∅) K)
    (g : normOneSubgroup F G) :
    ∃ (n : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅))
      (m : normOneSubgroup F (Standard.leviScheme i ν ∅))
      (a : PositiveRealTorus.intrinsicSubgroup F T₀),
      ∃ k ∈ K, map F _ G (Standard.unipotentHom i ν ∅) n *
        map F _ G (Standard.leviHom i ν ∅) m *
        positiveMap F G T i T₀ j a * k = g := by
  have hg : (g : AdelicGroupPoints F G) ∈
      Set.range (map F (Standard.parabolicScheme i ν ∅) G
        (Standard.parabolicHom i ν ∅)) * (K : Set (AdelicGroupPoints F G)) := by
    rw [hK.2]
    exact Set.mem_univ _
  obtain ⟨_, ⟨p, rfl⟩, k, hk, hpk⟩ := hg
  have hkone := compactSubgroup_le_normOneSubgroup F G K hK.1.1 hk
  have hpone : map F _ G (Standard.parabolicHom i ν ∅) p ∈ normOneSubgroup F G := by
    have hp : map F _ G (Standard.parabolicHom i ν ∅) p =
        (g : AdelicGroupPoints F G) * k⁻¹ := by
      rw [← hpk, mul_inv_cancel_right]
    rw [hp]
    exact (normOneSubgroup F G).mul_mem g.2 ((normOneSubgroup F G).inv_mem hkone)
  obtain ⟨n, m, a, hma⟩ := h ⟨_, hpone⟩ ⟨p, rfl⟩
  exact ⟨n, m, a, k, hk, by rw [hma]; exact hpk⟩

/-- For a fixed actual Siegel setup with its prescribed Iwasawa compact subgroup, the
universal rank-one arithmetic height bound gives the weak chamber reduction. This is the
published root-Levi chamber assembly with its positive-coordinate premise replaced by the
factors proved above. -/
theorem hasWeakChamberReduction_of_rankOne_height
    [LocallyOfFiniteType G.X.hom]
    (harith : RankOneParabolicRationalOrbitHeightBoundStatement.{u})
    (hG : IsConnectedReductive G)
    (hS : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsParabolicIwasawaCompact F G
      (Standard.parabolicScheme i ν ∅) (Standard.parabolicHom i ν ∅) K) :
    HasWeakChamberReduction F G T i ν T₀ j K := by
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
    F G r d' ρ (fun l _ => Nat.zero_lt_succ (d l)) hK.1.1
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
    apply hasUniformRootBound_of_minimal_coordinates_and_prefix_minima
      F G T i ν harith hG hS.1 hS.2.1 J hJ r d' ρ b l hl (hstab l)
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
  obtain ⟨x, m, a, k, hk, heq⟩ := HasMinimalParabolicNormFactors.exists_iwasawa_factors
    F G T i ν T₀ j (hS.hasMinimalParabolicNormFactors F G T i ν T₀ j hG) K hK z
  let p₀ := map F _ G (Standard.unipotentHom i ν ∅) x *
    map F _ G (Standard.leviHom i ν ∅) m * positiveMap F G T i T₀ j a
  have hp₀ : p₀ = (z : AdelicGroupPoints F G) * k⁻¹ := by
    rw [← heq]
    simp only [p₀, mul_inv_cancel_right]
  have hpone : p₀⁻¹ ∈ normOneSubgroup F G := by
    rw [hp₀]
    exact (normOneSubgroup F G).inv_mem ((normOneSubgroup F G).mul_mem z.property
      ((normOneSubgroup F G).inv_mem
        (compactSubgroup_le_normOneSubgroup F G K hK.1.1 hk)))
  let p : normOneSubgroup F G := ⟨p₀⁻¹, hpone⟩
  let k' : normOneSubgroup F G := ⟨k⁻¹,
    compactSubgroup_le_normOneSubgroup F G K hK.1.1 (K.inv_mem hk)⟩
  have hk'p : k' * p = y := by
    apply Subtype.ext
    change k⁻¹ * p₀⁻¹ = (y : AdelicGroupPoints F G)
    rw [← mul_inv_rev]
    change (p₀ * k)⁻¹ = (y : AdelicGroupPoints F G)
    rw [heq]
    exact congrArg Subtype.val hzy
  have hpmin : p ∈ chainHeightMinimalSet F G r d' ρ
      (fun l => Pi.single (b l) 1) Q D := by
    have h := (htransport (fun l => Pi.single (b l) 1) hv Q k' (K.inv_mem hk)
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


/-- The chamber form of the fundamental set theorem follows from the universal rank-one
arithmetic height bound alone; the minimal-parabolic factors are proved above. -/
theorem adelicSiegelChamberReduction_of_rankOne_height
    (harith : RankOneParabolicRationalOrbitHeightBoundStatement.{u}) :
    AdelicSiegelChamberReductionStatement.{u} := by
  intro F _ _ G _ _ hG T i ν T₀ j hS K hK
  exact hasWeakChamberReduction_of_rankOne_height F G T i ν T₀ j harith hG hS K hK

end Langlands.Global.AdelicSiegelFactors
