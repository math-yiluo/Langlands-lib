import Langlands.Geometry.Building.RootGroupZeroFixer
import Langlands.Geometry.Building.ParahoricNonnegativeRootGenerators
import Langlands.Geometry.Building.ParahoricFiniteReduction
import Langlands.Geometry.Building.PositiveRootFixerCoordinates
import Langlands.Geometry.Building.AffineWeylPointStabilizer
import Langlands.Geometry.Building.IwahoriWeylNormalizerAffineWeylReduction
import Langlands.Geometry.Building.RootFixerExchange
import Langlands.Geometry.Building.FilteredRootReflectionCells
import Langlands.Geometry.Building.ActualAffineRootLocalFiniteness
import Langlands.Geometry.Building.RankOneReflectionGeneration
import Langlands.Geometry.Building.ChamberIwahoriProof
import Langlands.Geometry.Building.KPParahoricProduct
import Langlands.LinearAlgebra.RootFaceReflection

/-! # Reducing `G(F)^0_Ω ⊆ P_Ω` to the normalizer (KP Lemma 7.7.4)

For building data `P` satisfying the apartment axioms, this module shows that the fixer
`G(F)^0_Ω` of a bounded non-empty `Ω ⊆ A` is `P_Ω`, provided every element of `N(F) ∩ G(F)^0`
fixing a finite non-empty set `Ω` pointwise lies in `P_Ω` (`HasNormalizerParahoricFixers`). That
proviso holds when `N(F) ∩ G(F)^0` acts on `A` through `W(Ψ)`. -/

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

/-! ### Reflections in affine roots vanishing on `Ω` -/

/-- A reflection `r_ψ` in an affine root `ψ ∈ Ψ` that vanishes on `Ω` is the action of an
element of `N(F) ∩ G(F)^♯_Ω`: the element `m(u) = u′ u u″` for `u ∈ U_ψ ∖ U_{ψ+}`. -/
theorem exists_sharpFixer_normalizer_eq_affineReflection (hP : P.SatisfiesApartmentAxioms)
    {Ω : Set P.Apartment} {ψ : P.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ P.affineRoots)
    (hΩ : ∀ y ∈ Ω, ψ y = 0) {v : TranslationSpace P.i}
    (hv : AffineRootSystem.IsCoroot P.affineRoots ψ v) :
    ∃ m : normalizerPoints P.i, (m : rationalPoints G) ∈ P.sharpFixer Ω ∧
      P.apartment.normalizerAffineEquiv m = AffineRootSystem.affineReflection ψ hv.1 := by
  obtain ⟨α, hlin, hne⟩ := P.apartment.affineRoots_subset_extendedAffineRoots hψ
  obtain ⟨u, hu, hnu⟩ : ∃ u ∈ P.affineRootGroup α ψ,
      u ∉ P.apartment.affineRootGroupPlus α ψ := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm (P.apartment.affineRootGroupPlus_le α ψ) hcon)
  obtain ⟨huα, hu1, hlevel⟩ := P.reflectionFunctional_eq_of_mem_diff hlin hu hnu
  obtain ⟨p, hp⟩ := P.hasOppositeFactorPairs α α.2 u huα hu1
  have hneg : -(α : characterLattice P.S) ∈ relativeRoots P.i :=
    P.neg_mem_relativeRoots_of_hasOppositeFactorPairs P.hasOppositeFactorPairs α
  obtain ⟨hp1, hp2⟩ := P.oppositeFactors_mem_neg_affineRootGroup huα hu1 hp hlevel
  have hfixα : u ∈ P.apartment.rootFixer α Ω := by
    refine P.apartment.mem_rootFixer.2 ⟨huα, fun y hy => ?_⟩
    have h := Subgroup.mem_iInf.1 hu y
    rwa [hΩ y hy] at h
  have hfixneg : ∀ {q : rationalPoints G},
      q ∈ P.affineRootGroup (-(α : characterLattice P.S)) (-ψ) →
        q ∈ P.apartment.rootFixer (-(α : characterLattice P.S)) Ω := by
    intro q hq
    refine P.apartment.mem_rootFixer.2
      ⟨P.apartment.filtration_le_rootGroupPoints (Classical.arbitrary P.Apartment) _ _
        (Subgroup.mem_iInf.1 hq _), fun y hy => ?_⟩
    have h := Subgroup.mem_iInf.1 hq y
    rwa [AffineMap.coe_neg, Pi.neg_apply, hΩ y hy, neg_zero] at h
  refine ⟨P.reflectionElement hp, ?_, ?_⟩
  · rw [ValuationBuildingData.coe_reflectionElement]
    refine (P.sharpFixer Ω).mul_mem ((P.sharpFixer Ω).mul_mem ?_ ?_) ?_
    · exact P.apartment.rootFixer_le_sharpFixer ⟨_, hneg⟩ Ω (hfixneg hp1)
    · exact P.apartment.rootFixer_le_sharpFixer α Ω hfixα
    · exact P.apartment.rootFixer_le_sharpFixer ⟨_, hneg⟩ Ω (hfixneg hp2)
  · subst hlevel
    exact P.normalizerAffineEquiv_reflectionElement_eq_of_isCoroot hP huα hu1 hp hv

/-! ### Normalizer elements fixing a finite set -/

/-- Every element of `N(F) ∩ G(F)^0` that fixes a finite non-empty `Ω ⊆ A` pointwise lies in
`P_Ω`: in KP's notation, `N(F)^0_Ω ⊆ P_Ω` for finite non-empty `Ω`. -/
def HasNormalizerParahoricFixers : Prop :=
  ∀ Ω : Set P.Apartment, Ω.Finite → Ω.Nonempty → ∀ n : normalizerPoints P.i,
    (n : rationalPoints G) ∈ P.zeroSubgroup → (∀ x ∈ Ω, n • x = x) →
      (n : rationalPoints G) ∈ P.parahoric Ω

/-- An element of `N(F) ∩ G(F)^0` that acts on `A` through `W(Ψ)` and fixes a finite non-empty
`Ω ⊆ A` pointwise lies in `P_Ω`. -/
theorem normalizer_mem_parahoric (hP : P.SatisfiesApartmentAxioms)
    {Ω : Set P.Apartment} (hΩ : Ω.Finite) (hne : Ω.Nonempty) (n : normalizerPoints P.i)
    (hn0 : (n : rationalPoints G) ∈ P.zeroSubgroup)
    (hnW : P.apartment.normalizerAffineEquiv n ∈ AffineRootSystem.affineWeylGroup P.affineRoots)
    (hfix : ∀ x ∈ Ω, n • x = x) :
    (n : rationalPoints G) ∈ P.parahoric Ω := by
  classical
  have hΨ := P.isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs
    P.hasOppositeFactorPairs
  obtain ⟨z, hzfix, hzgen⟩ := AffineRootSystem.exists_generic_point hΨ hΩ.toFinset
    (hΩ.toFinset_nonempty.2 hne)
  let w : AffineRootSystem.affineWeylGroup P.affineRoots :=
    ⟨P.apartment.normalizerAffineEquiv n, hnW⟩
  have hwz : (w : P.Apartment ≃ᵃ[ℝ] P.Apartment) z = z :=
    hzfix _ fun y hy => hfix y (hΩ.mem_toFinset.1 hy)
  have hcl := AffineRootSystem.mem_closure_pointReflections_of_apply_eq hΨ w hwz
  have hle : Subgroup.closure (AffineRootSystem.pointReflections P.affineRoots z) ≤
      ((P.sharpFixer Ω).subgroupOf (normalizerPoints P.i)).map
        P.apartment.normalizerAffineEquiv := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨ψ, hψ, hψz, v, hv, rfl⟩
    obtain ⟨m, hm, hmeq⟩ := P.exists_sharpFixer_normalizer_eq_affineReflection hP hψ
      (fun y hy => hzgen ψ hψ hψz y (hΩ.mem_toFinset.2 hy)) hv
    exact ⟨m, Subgroup.mem_subgroupOf.2 hm, hmeq⟩
  obtain ⟨m, hm, hmeq⟩ := hle hcl
  have hm' : (m : rationalPoints G) ∈ P.parahoric Ω :=
    le_sup_right (a := P.centralizerZero.map (rationalPoints.map P.centralizer.j))
      (Subgroup.mem_subgroupOf.1 hm)
  have hm0 : (m : rationalPoints G) ∈ P.zeroSubgroup := P.parahoric_le_zeroSubgroup hP Ω hm'
  have hk : (m⁻¹ * n : normalizerPoints P.i) ∈ P.normalizerZeroComponent := by
    change _ ∈ P.zeroSubgroup.subgroupOf (normalizerPoints P.i)
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact P.zeroSubgroup.mul_mem (P.zeroSubgroup.inv_mem hm0) hn0
  have hk1 : P.apartment.normalizerAffineEquiv (m⁻¹ * n) = 1 := by
    rw [map_mul, map_inv, hmeq]
    exact inv_mul_cancel _
  have hkZ := (P.normalizerAffineEquiv_eq_one_iff P.centralizerZeroIntersection ⟨_, hk⟩).1 hk1
  have hkZ' := (P.mem_normalizerZero_iff).1 hkZ
  have hnm : (n : rationalPoints G) =
      (m : rationalPoints G) * ((m⁻¹ * n : normalizerPoints P.i) : rationalPoints G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [hnm]
  exact (P.parahoric Ω).mul_mem hm' (P.map_centralizerZero_le_parahoric Ω hkZ')

/-- If every element of `N(F) ∩ G(F)^0` acts on `A` through `W(Ψ)`, then
`HasNormalizerParahoricFixers` holds. -/
theorem hasNormalizerParahoricFixers_of_mem_affineWeylGroup (hP : P.SatisfiesApartmentAxioms)
    (hNW : ∀ n : normalizerPoints P.i, (n : rationalPoints G) ∈ P.zeroSubgroup →
      P.apartment.normalizerAffineEquiv n ∈ AffineRootSystem.affineWeylGroup P.affineRoots) :
    P.HasNormalizerParahoricFixers := fun _ hΩ hne n hn0 hfix =>
  P.normalizer_mem_parahoric hP hΩ hne n hn0 (hNW n hn0) hfix

/-! ### The point case -/

theorem zeroFixer_anti {Ω Ω' : Set P.Apartment} (h : Ω ⊆ Ω') :
    P.zeroFixer Ω' ≤ P.zeroFixer Ω := fun _ hg =>
  P.mem_zeroFixer.2 ⟨(P.mem_zeroFixer.1 hg).1, fun x hx => (P.mem_zeroFixer.1 hg).2 x (h hx)⟩

/-- Given `HasNormalizerParahoricFixers`, `G(F)^0_x ⊆ P_x` for a point `x`. -/
theorem zeroFixer_singleton_le_parahoric (hP : P.SatisfiesApartmentAxioms)
    (hN : P.HasNormalizerParahoricFixers) (x : P.Apartment) :
    P.zeroFixer {x} ≤ P.parahoric {x} := by
  intro g hg
  obtain ⟨hg0, hgx⟩ := (P.mem_zeroFixer).1 hg
  obtain ⟨n, hnx, s, hs, hgsn⟩ :=
    (ApartmentQuotient.mem_stabilizer_apartment_iff P.apartment.sharpFixerFamily x g).1
      (MulAction.mem_stabilizer_iff.2 (hgx x (Set.mem_singleton x)))
  have hs' : s ∈ P.sharpFixer {x} := hs
  have hsP : s ∈ P.parahoric {x} := P.sharpFixer_le_parahoric {x} hs'
  have hn0 : (n : rationalPoints G) ∈ P.zeroSubgroup := by
    have h := P.zeroSubgroup.mul_mem (P.zeroSubgroup.inv_mem
      (P.parahoric_le_zeroSubgroup hP {x} hsP)) hg0
    rwa [hgsn, inv_mul_cancel_left] at h
  have hnP := hN {x} (Set.finite_singleton x) (Set.singleton_nonempty x) n hn0
    (fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hnx)
  rw [hgsn]
  exact (P.parahoric {x}).mul_mem hsP hnP

/-! ### A generic cocharacter adapted to a direction -/

/-- For every `w ∈ V(S)` there is a generic cocharacter `ν` such that every relative root `b`
with `⟨b, ν⟩ > 0` satisfies `b(w) ≥ 0`. -/
theorem exists_genericCocharacter_eval_nonneg (w : V P.S) :
    ∃ ν : cocharacterLattice P.S, IsGenericCocharacter P.i ν ∧
      ∀ b ∈ relativeRoots P.i, 0 < latticePairing P.S b ν → 0 ≤ eval P.S b w := by
  classical
  have : Smooth G.X.hom := P.isConnectedReductive.smooth
  have hT : IsSplitTorus P.S.toGrp := P.isMaximalSplitTorus.isSplitSubtorus.1
  have hfin := hT.finite_relativeRoots P.i
  obtain ⟨ν₀, hν₀⟩ := P.isMaximalSplitTorus.isSplitSubtorus.1.exists_genericCocharacter P.i
  obtain ⟨mu, hmu⟩ := Langlands.LinearAlgebra.RootFaceCone.exists_int_sign_realization
    hfin.toFinset (fun b => latticePairing P.S (-b)) (fun b => -eval P.S b)
    (fun b t n => by
      rw [LinearMap.neg_apply, eval_tmul, map_neg, LinearMap.neg_apply, Int.cast_neg, mul_neg]) w
  set M : ℤ := 1 + ∑ b ∈ hfin.toFinset, |latticePairing P.S b ν₀| with hMdef
  have hM : ∀ b ∈ relativeRoots P.i, |latticePairing P.S b ν₀| < M := by
    intro b hb
    have h := Finset.single_le_sum (f := fun b => |latticePairing P.S b ν₀|)
      (fun _ _ => abs_nonneg _) (hfin.mem_toFinset.2 hb)
    omega
  have hpair : ∀ b, latticePairing P.S b (M • mu + ν₀) =
      M * latticePairing P.S b mu + latticePairing P.S b ν₀ := by
    intro b
    rw [map_add, map_zsmul, smul_eq_mul]
  have hneg : ∀ b ∈ relativeRoots P.i, eval P.S b w < 0 → latticePairing P.S b mu < 0 := by
    intro b hb hw
    have h := (hmu b (hfin.mem_toFinset.2 hb)).2 (by
      rw [LinearMap.neg_apply]
      linarith)
    rw [map_neg, LinearMap.neg_apply] at h
    omega
  refine ⟨M • mu + ν₀, fun b hb => ?_, fun b hb hpos => ?_⟩
  · rw [hpair]
    have hq := abs_lt.1 (hM b hb)
    rcases lt_trichotomy (latticePairing P.S b mu) 0 with hp | hp | hp
    · nlinarith
    · rw [hp, mul_zero, zero_add]
      exact hν₀ b hb
    · nlinarith
  · by_contra hw
    have hp := hneg b hb (lt_of_not_ge hw)
    rw [hpair] at hpos
    have hq := abs_lt.1 (hM b hb)
    nlinarith

/-! ### Normalizer factors of stabilizing products -/

/-- If `v n` fixes the image of `x` in `B(G)`, with `v` in the unipotent group of a generic
cocharacter and `n ∈ N(F)`, then `n` fixes `x`. -/
theorem smul_eq_self_of_unipotent_mul_smul_apartmentMap_eq (hP : P.SatisfiesApartmentAxioms)
    (x : P.Apartment) (ν : cocharacterLattice P.S) (hν : IsGenericCocharacter P.i ν)
    {v : rationalPoints G}
    (hvU : v ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom ν ≫ P.i)).carrier (Over.mk (𝟙 _)))
    (n : normalizerPoints P.i)
    (hx : (v * (n : rationalPoints G)) • P.apartmentMap x = P.apartmentMap x) :
    n • x = x := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hrank := rootRankOneFactorization F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus
  have hνneg : IsGenericCocharacter P.i (-ν) := by
    intro a ha
    simpa only [map_neg] using neg_ne_zero.mpr (hν a ha)
  have hsharp := P.toValuationBuildingData.sharpFixer_subset_mul_sharpNormalizerStabilizer
    hP hrank x (-ν) hνneg
  rw [neg_neg] at hsharp
  obtain ⟨m, hmx, s, hs, hgsm⟩ :=
    (ApartmentQuotient.mem_stabilizer_apartment_iff P.apartment.sharpFixerFamily x _).1
      (MulAction.mem_stabilizer_iff.2 hx)
  obtain ⟨vw, ⟨v', hv', w, hw, rfl⟩, k, hk, hvwk⟩ := hsharp hs
  change v' * w * k = s at hvwk
  obtain ⟨-, hkN, hkx⟩ := KPApartmentData.mem_sharpNormalizerStabilizer.mp hk
  set n' : normalizerPoints P.i := ⟨k, hkN⟩ * m * n⁻¹ with hn'def
  have hv'U := (P.apartment.positiveChamberRootGroups_le_sharpUnipotentPoints x ν hv').1
  have hwU := (P.apartment.positiveChamberRootGroups_le_sharpUnipotentPoints x (-ν) hw).1
  have hpos : v'⁻¹ * v ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom ν ≫ P.i)).carrier (Over.mk (𝟙 _)) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hv'U) hvU
  have hopp : w⁻¹ ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter
      (CommGroupScheme.groupHom ν ≫ P.i))).carrier (Over.mk (𝟙 _)) := by
    rw [← groupHom_neg_comp_eq_oppositeCocharacter P.i ν]
    exact Subgroup.inv_mem _ hwU
  have heq : (n' : rationalPoints G) = w⁻¹ * (v'⁻¹ * v) := by
    rw [hn'def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    change k * (m : rationalPoints G) * (n : rationalPoints G)⁻¹ = _
    rw [← hvwk] at hgsm
    calc k * (m : rationalPoints G) * (n : rationalPoints G)⁻¹
        = w⁻¹ * v'⁻¹ * (v' * w * k * (m : rationalPoints G)) * (n : rationalPoints G)⁻¹ := by
          group
      _ = w⁻¹ * (v'⁻¹ * v) := by
          rw [← hgsm]
          group
  have hn' : n' = 1 :=
    normalizer_eq_one_of_unipotent_product P.i ν n' ⟨_, hopp⟩ ⟨_, hpos⟩ heq
  have hn : n = ⟨k, hkN⟩ * m := (mul_inv_eq_one.1 (hn'def ▸ hn')).symm
  rw [hn, mul_smul, hmx, hkx]

/-! ### Decomposition of `P_Ω` for a finite `Ω` -/

/-- For a finite non-empty `Ω` and a generic cocharacter `ν`, every `g ∈ P_Ω` is a product
`u v n` with `u` in the subgroup generated by the `U_{b,Ω,0}`, `⟨b, ν⟩ > 0`, `v` in the
subgroup generated by the `U_{b,Ω,0}`, `⟨b, ν⟩ < 0`, and `n ∈ N(F) ∩ G(F)^0` fixing `Ω`. -/
theorem exists_mul_mul_normalizer_of_mem_parahoric (hP : P.SatisfiesApartmentAxioms)
    {Ω : Set P.Apartment} (hΩ : Ω.Finite) (hne : Ω.Nonempty)
    (ν : cocharacterLattice P.S) (hν : IsGenericCocharacter P.i ν)
    {g : rationalPoints G} (hg : g ∈ P.parahoric Ω) :
    ∃ u ∈ (⨆ b : positiveRelativeRoots P.i ν, P.apartment.rootFixer b Ω),
      ∃ v ∈ (⨆ b : positiveRelativeRoots P.i (-ν), P.apartment.rootFixer b Ω),
        ∃ n : normalizerPoints P.i, (n : rationalPoints G) ∈ P.zeroSubgroup ∧
          (∀ x ∈ Ω, n • x = x) ∧ g = u * v * n := by
  have hνneg : IsGenericCocharacter P.i (-ν) := by
    intro a ha
    simpa only [map_neg] using neg_ne_zero.mpr (hν a ha)
  have hg' : g ∈ (P.parahoric Ω : Set (rationalPoints G)) := hg
  rw [P.coe_parahoric_eq_mul_reverse Ω] at hg'
  obtain ⟨s, hs, _, ⟨z, hz, rfl⟩, rfl⟩ := hg'
  have hexch := finiteSharpFixerExchange F G P.toValuationBuildingData hP Ω hΩ hne (-ν) hνneg
  rw [neg_neg] at hexch
  obtain ⟨uv, ⟨u, hu, v, hv, rfl⟩, h, hh, huvh⟩ := hexch hs
  change u * v * h = s at huvh
  obtain ⟨hhS, hhN, hhfix⟩ := KPApartmentData.mem_sharpNormalizerFixer.1 hh
  have hz1 : P.apartment.normalizerAffineEquiv (P.centralizer.toNormalizer z) = 1 :=
    P.normalizerAffineEquiv_eq_one_of_mem_normalizerZero ⟨z, hz, rfl⟩
  refine ⟨u, hu, v, hv, ⟨h, hhN⟩ * P.centralizer.toNormalizer z, ?_, fun x hx => ?_, ?_⟩
  · change h * rationalPoints.map P.centralizer.j z ∈ P.zeroSubgroup
    exact P.zeroSubgroup.mul_mem
      (P.parahoric_le_zeroSubgroup hP Ω (P.sharpFixer_le_parahoric Ω hhS))
      (P.parahoric_le_zeroSubgroup hP Ω (P.map_centralizerZero_le_parahoric Ω ⟨z, hz, rfl⟩))
  · have hzx : P.centralizer.toNormalizer z • x = x := by
      have h1 := congrArg (fun e : P.Apartment ≃ᵃ[ℝ] P.Apartment => e x) hz1
      simpa only [KPApartmentData.normalizerAffineEquiv_apply, AffineEquiv.coe_one, id_eq]
        using h1
    rw [mul_smul, hzx]
    exact hhfix x hx
  · rw [← huvh]
    show u * v * h * rationalPoints.map P.centralizer.j z =
      u * v * (h * rationalPoints.map P.centralizer.j z)
    rw [mul_assoc]

/-! ### The induction step (KP Lemma 7.7.4) -/

/-- The induction step of KP Lemma 7.7.4: given `HasNormalizerParahoricFixers`, if `g ∈ P_Ω`
fixes the image of `insert x Ω`, then `g ∈ P_{insert x Ω}`. -/
theorem mem_parahoric_insert (hP : P.SatisfiesApartmentAxioms)
    (hN : P.HasNormalizerParahoricFixers)
    {Ω : Set P.Apartment} (hΩ : Ω.Finite) (hne : Ω.Nonempty) (x : P.Apartment)
    {g : rationalPoints G} (hgx : g ∈ P.zeroFixer (insert x Ω)) (hgΩ : g ∈ P.parahoric Ω) :
    g ∈ P.parahoric (insert x Ω) := by
  have hrank := rootRankOneFactorization F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus
  obtain ⟨y, hy⟩ := hne
  obtain ⟨w, hw⟩ := KPApartmentData.exists_mk_vadd_eq (D := P.apartment) y x
  obtain ⟨ν, hν, hadapt⟩ := P.exists_genericCocharacter_eval_nonneg w
  have hνneg : IsGenericCocharacter P.i (-ν) := by
    intro a ha
    simpa only [map_neg] using neg_ne_zero.mpr (hν a ha)
  obtain ⟨u, hu, v, hv, n, hn0, hnfix, rfl⟩ :=
    P.exists_mul_mul_normalizer_of_mem_parahoric hP hΩ ⟨y, hy⟩ ν hν hgΩ
  -- the positive factor fixes `x`
  have hu' : u ∈ P.sharpFixer (insert x Ω) := by
    suffices hle : (⨆ b : positiveRelativeRoots P.i ν, P.apartment.rootFixer b Ω) ≤
        P.sharpFixer (insert x Ω) from hle hu
    refine iSup_le fun b => ?_
    refine le_trans ?_ (P.apartment.rootFixer_le_sharpFixer ⟨b, b.2.1⟩ (insert x Ω))
    intro t ht
    obtain ⟨htU, htΩ⟩ := P.apartment.mem_rootFixer.1 ht
    refine P.apartment.mem_rootFixer.2 ⟨htU, fun z hz => ?_⟩
    rcases Set.mem_insert_iff.1 hz with rfl | hz
    · have hty := htΩ y hy
      rw [hw, KPApartmentData.filtration_mk_vadd]
      refine ⟨htU, le_trans ?_ hty.2⟩
      have := hadapt b b.2.1 b.2.2
      exact WithTop.coe_le_coe.2 (by linarith)
    · exact htΩ z hz
  have huP : u ∈ P.parahoric (insert x Ω) := P.sharpFixer_le_parahoric _ hu'
  have huF := P.parahoric_le_zeroFixer hP _ huP
  -- the product `v n` fixes the image of `insert x Ω`
  have hvn : v * (n : rationalPoints G) ∈ P.zeroFixer (insert x Ω) := by
    have h := (P.zeroFixer (insert x Ω)).mul_mem ((P.zeroFixer (insert x Ω)).inv_mem huF) hgx
    rwa [mul_assoc, inv_mul_cancel_left] at h
  have hvU : v ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom (-ν) ≫ P.i)).carrier (Over.mk (𝟙 _)) := by
    suffices hle : (⨆ b : positiveRelativeRoots P.i (-ν), P.apartment.rootFixer b Ω) ≤
        (Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ P.i)).carrier (Over.mk (𝟙 _))
      from hle hv
    refine iSup_le fun b => ?_
    exact inf_le_left.trans
      (RelativeRoot.subgroup_le_dynamicUnipotent P.i (-ν) b.2.2 (Over.mk (𝟙 _)))
  have hnx : n • x = x := P.smul_eq_self_of_unipotent_mul_smul_apartmentMap_eq hP x (-ν) hνneg
    hvU n ((P.mem_zeroFixer.1 hvn).2 x (Set.mem_insert x Ω))
  have hnP : (n : rationalPoints G) ∈ P.parahoric (insert x Ω) :=
    hN (insert x Ω) (hΩ.insert x) (Set.insert_nonempty x Ω) n hn0
      fun z hz => by
        rcases Set.mem_insert_iff.1 hz with rfl | hz
        · exact hnx
        · exact hnfix z hz
  -- the negative factor fixes the image of `insert x Ω`
  have hvF : v ∈ P.zeroFixer (insert x Ω) := by
    have h := (P.zeroFixer (insert x Ω)).mul_mem hvn
      ((P.zeroFixer (insert x Ω)).inv_mem (P.parahoric_le_zeroFixer hP _ hnP))
    rwa [mul_inv_cancel_right] at h
  have hv' : v ∈ P.sharpFixer (insert x Ω) := by
    have hmem : v ∈ ⨅ z ∈ insert x Ω, ⨆ b : positiveRelativeRoots P.i (-ν),
        P.apartment.chamberRootGroup z false b := by
      refine Subgroup.mem_iInf.2 fun z => Subgroup.mem_iInf.2 fun hz => ?_
      exact P.mem_positiveRootGroups_of_mem_unipotent_of_smul_apartmentMap_eq hP hrank z (-ν)
        hνneg hvU ((P.mem_zeroFixer.1 hvF).2 z hz)
    rw [P.iInf_iSup_chamberRootGroup_eq_iSup_rootFixer hP (-ν) (Set.insert_nonempty x Ω)]
      at hmem
    suffices hle : (⨆ b : positiveRelativeRoots P.i (-ν), P.apartment.rootFixer b (insert x Ω)) ≤
        P.sharpFixer (insert x Ω) from hle hmem
    refine iSup_le fun b => ?_
    exact P.apartment.rootFixer_le_sharpFixer ⟨b, b.2.1⟩ (insert x Ω)
  exact (P.parahoric _).mul_mem ((P.parahoric _).mul_mem huP
    (P.sharpFixer_le_parahoric _ hv')) hnP

/-! ### Finite and bounded sets -/

/-- Given `HasNormalizerParahoricFixers`, `G(F)^0_Ω ⊆ P_Ω` for finite non-empty `Ω`. -/
theorem zeroFixer_le_parahoric_of_finite (hP : P.SatisfiesApartmentAxioms)
    (hN : P.HasNormalizerParahoricFixers)
    {Ω : Set P.Apartment} (hΩ : Ω.Finite) (hne : Ω.Nonempty) :
    P.zeroFixer Ω ≤ P.parahoric Ω := by
  revert hne
  induction Ω, hΩ using Set.Finite.induction_on with
  | empty => exact fun hne => absurd hne Set.not_nonempty_empty
  | @insert a s ha hs ih =>
    intro _
    rcases s.eq_empty_or_nonempty with rfl | hsne
    · rw [insert_empty_eq]
      exact P.zeroFixer_singleton_le_parahoric hP hN a
    · intro g hg
      exact P.mem_parahoric_insert hP hN hs hsne a hg
        (ih hsne (P.zeroFixer_anti (Set.subset_insert a s) hg))

/-- Given `HasNormalizerParahoricFixers`, `G(F)^0_Ω ⊆ P_Ω` for bounded non-empty `Ω`. -/
theorem zeroFixer_le_parahoric (hP : P.SatisfiesApartmentAxioms)
    (hN : P.HasNormalizerParahoricFixers)
    {Ω : Set P.Apartment} (hne : Ω.Nonempty) (hb : P.IsBoundedSubset Ω) :
    P.zeroFixer Ω ≤ P.parahoric Ω := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨Ω', hΩ', hfin, hx₀', -, hpar⟩ := P.exists_finite_subset_parahoric_eq hb hx₀
  rw [← hpar]
  exact (P.zeroFixer_anti hΩ').trans
    (P.zeroFixer_le_parahoric_of_finite hP hN hfin ⟨x₀, hx₀'⟩)

/-- KP Axiom 4.1.8 (2) for `P`, given `HasNormalizerParahoricFixers`: for every bounded non-empty
`Ω ⊆ A`, `G(F)^0_Ω` is generated by `Z(F)^0` and the `U_ψ` with `ψ ∈ Ψ` non-negative on `Ω`. -/
theorem hasZeroFixerGenerators_of_hasNormalizerParahoricFixers
    (hP : P.SatisfiesApartmentAxioms) (hN : P.HasNormalizerParahoricFixers) :
    P.HasZeroFixerGenerators := by
  intro Ω hne hb
  rw [← P.parahoric_eq_nonnegativeRootSubgroup hP Ω]
  exact le_antisymm (P.zeroFixer_le_parahoric hP hN hne hb) (P.parahoric_le_zeroFixer hP Ω)

end ParahoricBuildingData

end Langlands.Geometry.Building
