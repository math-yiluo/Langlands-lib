import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviXiLowerBoundStatement
import Langlands.BruhatTits.SpecialCompact.StandardLeviWeakChamberTransport
import Langlands.GroupScheme.Rational.CocharacterCone

/-! # The spherical lower bound in an actual standard Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter
open scoped CategoryTheory.MonObj Topology
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact
open Langlands.Aubert.General.RationalPointFamily

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

section Chamber

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {J : Set (characterLattice S)}
  {q : A.toGrp ⟶ S.toGrp}

local instance : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J

private theorem map_mem_leviComponentCAplus (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) (hA : IsCompatibleStandardSplitComponent i ν ∅ A q)
    {a : rationalPoints S.toGrp} (ha : a ∈ CocharacterUniformizer.CAplus F S J) :
    rationalPoints.map (Standard.leviTorusHom i ν J) a ∈
      standardComponentCAplus (Standard.leviTorusHom i ν J) ν ∅ q := by
  obtain ⟨c, rfl⟩ := ha.1
  have hc := (CocharacterCone.latticeSection_mem_CAplus_iff S J c.toAdd).mp ha
  obtain ⟨d, hd⟩ := hA.exists_cocharacter_lift_of_annihilates i ν hi
    ⟨ν, isStandardCocharacter_empty_self i ν⟩ c.toAdd (by simp)
  refine ⟨CocharacterUniformizer.latticeSection F A (Multiplicative.ofAdd d), ?_, ?_⟩
  · apply (CocharacterCone.latticeSection_mem_CAplus_iff A _ d).mpr
    rintro _ ⟨α, hα, rfl⟩
    have hsimple := simpleRelativeRoots_leviScheme i ν J hG hi hν hJ
    have hαJ : α ∈ J := hsimple ▸ hα.1
    rw [componentCharacterRestriction_pairing (q := q), hd]
    exact hc α hαJ
  · rw [rationalPoints_map_comp_apply]
    apply congrArg (rationalPoints.map (Standard.leviTorusHom i ν J))
    have h := CocharacterUniformizer.map_latticeSection (F := F) (Additive.ofMul q) d
    rw [hd] at h
    exact h

end Chamber

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- Waldspurger's lower-bound argument on the full standard-Levi chamber,
with one compact basis member for all the prescribed centralizer translates. -/
theorem rationalLeviXiLowerBound : RationalLeviXiLowerBoundStatement.{u} := by
  classical
  intro F _ _ _ _ G _ _ hG S i hi ν hν J hJ K0 _ _ hbasis K hKo hKc hM F0
  obtain ⟨B, hB, hfaces⟩ := hbasis
  have hKne : ∀ᶠ x in 𝓝 (1 : rationalPoints G), x ∈ K := hKo.mem_nhds K.one_mem
  have hFne : ∀ᶠ x in 𝓝 (1 : rationalPoints G), ∀ f ∈ F0,
      (f : rationalPoints G)⁻¹ * x * f ∈ K := by
    refine F0.eventually_all.mpr fun f _ => ?_
    have hcont : Continuous fun x : rationalPoints G => (f : rationalPoints G)⁻¹ * x * f :=
      (continuous_const.mul continuous_id).mul continuous_const
    have hone : (f : rationalPoints G)⁻¹ * (1 : rationalPoints G) * f ∈ K := by simp
    exact (hKo.preimage hcont).mem_nhds hone
  obtain ⟨H, hHB, hH⟩ := hB.2.mem_iff.mp (hKne.and hFne)
  have hHK : H ≤ K := fun _ hx => (hH hx).1
  obtain ⟨-, A, q, hA, hmembers⟩ := hfaces ∅ (Set.empty_subset _)
  have hmember := hmembers H hHB
  let L := Standard.leviScheme i ν J
  let iL := Standard.leviTorusHom i ν J
  let jF := rationalPoints.map (Standard.leviHom i ν J)
  have : IsAffineHom L.X.hom := leviScheme_isAffineHom i ν J
  have : LocallyOfFiniteType L.X.hom := leviScheme_locallyOfFiniteType i ν J
  let HL := leviSchemeCompact H i ν J
  let KL := leviSchemeCompact K i ν J
  have hHLo : IsOpen (HL : Set (rationalPoints L)) :=
    isOpen_leviSchemeCompact (hB.1 H hHB).2.2.1
  have hHKL : HL ≤ KL := fun _ hx => hHK hx
  have hKLo : IsOpen (KL : Set (rationalPoints L)) := isOpen_leviSchemeCompact hKo
  have hKLc : IsCompact (KL : Set (rationalPoints L)) := isCompact_leviSchemeCompact hKc
  have : CompactSpace KL := isCompact_iff_compactSpace.mp hKLc
  have hPL := isIwasawaPair_leviSchemeCompact hG hi hν hJ hM
  have hIwahori := hasIwahoriIntersectionDecomposition_leviScheme i ν J hG hi hν hJ
    (Set.empty_subset J) hmember.1
  have hweak := weakChamberContraction_leviScheme i ν J hG hi hν hJ
    (Set.empty_subset J) hA hmember.2.2.1
  let T : Set (rationalPoints L) := {x | ∃ f ∈ F0, ∃ a ∈ CocharacterUniformizer.CAplus F S J,
    jF x = (f : rationalPoints G) * rationalPoints.map i a}
  have hbound : XiLowerBound (rationalXi hKLc hPL) T
      (iwasawaWeight hPL (rationalMinimalModulus iL ν)) := by
    unfold rationalXi
    refine xiLowerBound_of_factorization (hPK := hPL)
      (rationalMinimalModulus_eq_one iL ν hKLo hKLc) hKLo hHKL hHLo
      (V := ((HL ⊓ standardOppositeUnipotentPoints iL ν ∅ : Subgroup (rationalPoints L)) :
        Set (rationalPoints L))) ?_ ?_
    · intro h hh
      obtain ⟨⟨l, m, n⟩, heq⟩ := hIwahori.2 ⟨h⁻¹, HL.inv_mem hh⟩
      have heq' : h⁻¹ = (l : rationalPoints L) * m * n := (congrArg Subtype.val heq).symm
      refine ⟨(n : rationalPoints L)⁻¹ * (m : rationalPoints L)⁻¹, ?_, ?_,
        (l : rationalPoints L)⁻¹, ?_, ?_⟩
      · exact (standardParabolicPoints iL ν ∅).mul_mem
          ((standardParabolicPoints iL ν ∅).inv_mem
            (standardUnipotent_le_standardParabolic iL ν ∅ _ n.2.2))
          ((standardParabolicPoints iL ν ∅).inv_mem
            (standardLevi_le_standardParabolic iL ν ∅ _ m.2.2))
      · exact HL.mul_mem (HL.inv_mem n.2.1) (HL.inv_mem m.2.1)
      · exact ⟨HL.inv_mem l.2.1, (standardOppositeUnipotentPoints iL ν ∅).inv_mem l.2.2⟩
      · calc h = (h⁻¹)⁻¹ := (inv_inv h).symm
          _ = (n : rationalPoints L)⁻¹ * (m : rationalPoints L)⁻¹ *
              (l : rationalPoints L)⁻¹ := by rw [heq']; simp only [mul_inv_rev, mul_assoc]
    · intro x hx v hv
      obtain ⟨f, hf, a, ha, hxeq⟩ := hx
      let aL := rationalPoints.map iL a
      have haL := map_mem_leviComponentCAplus hG hi hν hJ hA ha
      have haeq : jF aL = rationalPoints.map i a := by
        change rationalPoints.map (Standard.leviHom i ν J) (rationalPoints.map iL a) = _
        rw [← rationalPoints_map_comp_apply, Standard.leviTorusHom_comp]
      have hv' : aL⁻¹ * v * aL ∈ HL ⊓ standardOppositeUnipotentPoints iL ν ∅ :=
        (hweak aL haL).2 ⟨v, hv, by rw [inv_inv]⟩
      have havH : jF (aL⁻¹ * v * aL) ∈ H := hv'.1
      have hcomm : rationalPoints.map i a * (f : rationalPoints G) =
          (f : rationalPoints G) * rationalPoints.map i a :=
        centralizerPoints_le_pointCentralizer i f.2 _ ⟨a, rfl⟩
      have heq : jF (x⁻¹ * v * x) = (f : rationalPoints G)⁻¹ * jF (aL⁻¹ * v * aL) * f := by
        simp only [map_mul, map_inv, hxeq, haeq, ← hcomm, mul_inv_rev, mul_assoc]
      change jF (x⁻¹ * v * x) ∈ K
      rw [heq]
      exact (hH havH).2 f hf
  have hweight (x : rationalPoints L) :
      iwasawaWeight hM (standardLeviMinimalModulusOf i ν J) (leviSchemePointsEquiv i ν J x) =
        iwasawaWeight hPL (rationalMinimalModulus iL ν) x := by
    refine iwasawaWeight_map (leviSchemePointsEquiv i ν J)
      (standardLeviMinimalModulusOf_eq_one hKo hKc hG hi hν hJ)
      (fun p hp => ?_) (fun k hk => (mem_leviSchemeCompact_iff k).mp hk) (fun p => ?_) x
    · rw [Subgroup.mem_subgroupOf, leviSchemePointsEquiv_coe]
      exact (mem_standardParabolicPoints_leviTorusHom_iff hG hi hν hJ p).mp hp
    · rw [standardLeviMinimalModulusOf_apply]
      exact standardLeviMinimalModulus_leviHom hG hi hν hJ p
  obtain ⟨C, hC⟩ := hbound
  refine ⟨max C 1, zero_lt_one.trans_le (le_max_right _ _), fun m hm => ?_⟩
  let x := (leviSchemePointsEquiv i ν J).symm m
  have hx : x ∈ T := by
    obtain ⟨f, hf, a, ha, hma⟩ := hm
    refine ⟨f, hf, a, ha, ?_⟩
    change rationalPoints.map (Standard.leviHom i ν J) x = _
    rw [map_leviSchemePointsEquiv_symm, hma]
  have he : leviSchemePointsEquiv i ν J x = m := (leviSchemePointsEquiv i ν J).apply_symm_apply m
  have h := hC x hx
  rw [← hweight x, rationalXi_leviScheme hG hi hν hJ hKo hKc hM x, he] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (rationalLeviXi_pos hKo hKc hG hi hν hJ hM m).le)

end Langlands.HarishChandraSchwartz
