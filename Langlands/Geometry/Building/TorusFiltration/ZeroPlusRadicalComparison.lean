import Langlands.Geometry.Building.TorusFiltration.PositiveUnipotentProof
import Langlands.Geometry.Building.TorusFiltration.ZeroPlusNormCover
import Langlands.GroupScheme.IntegralModel.CongruenceNeighborhoodBasisProof
import Langlands.GroupScheme.Absolute.SolvableSemisimpleCentralizer.DerivedStages
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof
import Langlands.GroupScheme.Rational.PositiveCharacteristicTorusPower
import Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceProof

/-! # The standard zero-plus group and the special-fibre radical -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.BruhatTits.IntegralModels Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open scoped CategoryTheory.MonObj NNReal ValuativeRel

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 180000

namespace Langlands.Geometry.Building

private theorem mem_subgroup_of_coprime_pow {G : Type u} [Group G] (H : Subgroup G)
    {m n : ℕ} (hcop : m.Coprime n) {x : G} (hm : x ^ m = 1) (hn : x ^ n ∈ H) :
    x ∈ H := by
  have hcop' : IsCoprime (m : ℤ) (n : ℤ) :=
    Int.isCoprime_iff_nat_coprime.mpr (by simpa using hcop)
  obtain ⟨a, b, hab⟩ := hcop'
  have h : x ^ (a * (m : ℤ) + b * (n : ℤ)) ∈ H := by
    rw [zpow_add, mul_comm a, mul_comm b, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast,
      hm, one_zpow, one_mul]
    exact H.zpow_mem hn _
  rwa [hab, zpow_one] at h

private theorem splitTorusPoint_eq_one_of_pPower {k : Type u} [Field k]
    {p : ℕ} [Fact p.Prime] [CharP k p] {D : GroupScheme (Spec (CommRingCat.of k))}
    (hD : IsSplitTorus D) (x : rationalPoints D) (d : ℕ) (hx : x ^ (p ^ d) = 1) :
    x = 1 := by
  obtain ⟨J, hJ, ⟨e⟩⟩ := hD
  let : Finite J := hJ
  let c := (rationalPoints.mapEquiv e).trans
    (splitTorus.affinePointsEquiv J (𝟙 (Spec (CommRingCat.of k))))
  apply c.injective
  rw [map_one]
  funext j
  apply Units.ext
  have h := congrArg c hx
  rw [map_pow, map_one] at h
  have hj : ((c x j : k) ^ (p ^ d)) = 1 :=
    congrArg (fun v : J → kˣ => (v j : k)) h
  have hzero : ((c x j : k) - 1) ^ (p ^ d) = 0 := by
    rw [sub_pow_char_pow _ _ d (p := p), hj, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero)).mp hzero)

section Model

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
  [IsAffine T.X.left] (hT : IsTorus T.toGrp)

local notation "O" => fixedFieldIntegers F
local notation "K" => inertiaFixedField F
local notation "κ" => IsLocalRing.ResidueField O
local notation "p" => ringChar κ
local notation "A" => sepClosureIntegers F
local notation "M₀" => connectedNeronModel F T hT
local notation "Std⁺" =>
  (⋃ r : Set.Ioi (0 : ℝ≥0), (localTorusFiltration F T hT r : Set (rationalPoints T.toGrp)))

private local instance residueChar_prime : Fact (Nat.Prime p) := by
  let : Algebra 𝓀[F] κ := (residueToFixedField F).toAlgebra
  exact ⟨by rw [← Algebra.ringChar_eq 𝓀[F] κ]; exact CharP.prime_ringChar 𝓀[F]⟩

private local instance residueAlgClosed : IsAlgClosed κ :=
  (fixedFieldResidueIsAlgClosure F).isAlgClosed

private local instance henselianIntegers : HenselianLocalRing O :=
  (fixedFieldIntegers_strictHenselian F).2.1

private local instance modelSmooth : Smooth (M₀).group.X.hom :=
  connectedNeronModel_isSmooth F T hT

private local instance residueConnected : ConnectedSpace (M₀).specialFibre.X.left :=
  (M₀).hasConnectedSpecialFibre_of_geometricallyConnected
    ((M₀).hasGeometricallyConnectedSpecialFibre_of_geometricallyConnected
      (connectedNeronModel_hasGeometricallyConnectedFibres F T hT))

set_option maxHeartbeats 1000000 in
private local instance residueCommutative : IsCommMonObj (M₀).specialFibre.X := by
  let : IsCommMonObj T.toGrp.X := T.comm
  apply SemisimpleCentralizer.isCommMonObj_of_commuting_points
  have hM := connectedNeronModel_isSmooth F T hT
  intro x y
  obtain ⟨a, rfl⟩ := (M₀).reduction_surjective hM x
  obtain ⟨b, rfl⟩ := (M₀).reduction_surjective hM y
  have hab : a * b = b * a := (M₀).integralPointMap_injective (by
    rw [map_mul, map_mul]
    exact mul_comm _ _)
  rw [← map_mul, ← map_mul, hab]

set_option maxHeartbeats 850000 in
private theorem residue_mem_radical_iff_pPower {U : GroupScheme (Spec (CommRingCat.of κ))}
    (i : U ⟶ (M₀).specialFibre) (hi : IsUnipotentRadical i) (y : rationalPoints (M₀).specialFibre) :
    y ∈ (rationalPoints.map i).range ↔ ∃ d : ℕ, y ^ (p ^ d) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    let : Smooth U.X.hom := hi.smooth
    let : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
    let : IsAffineHom U.X.hom := by rw [← Over.w i.hom.hom]; infer_instance
    obtain ⟨d, hd⟩ := exists_hasUniformPowerExponent_of_isUnipotent p hi.isUnipotent
    exact ⟨d, by rw [← map_pow, hd _ u, map_one]⟩
  · rintro ⟨d, hd⟩
    obtain ⟨B, D, a, q, ha, hsm, hc, hu, hn, hq, hD⟩ := solvableTorusQuotient κ (M₀).specialFibre
      (isNilpotentGroupScheme_of_isCommMonObj (M₀).specialFibre).isSolvableGroupScheme
    have hyD : rationalPoints.map q y = 1 :=
      splitTorusPoint_eq_one_of_pPower hD _ d (by rw [← map_pow, hd, map_one])
    have hy : y ∈ (SubgroupFunctor.range a).carrier (Over.mk (𝟙 (Spec (CommRingCat.of κ)))) := by
      rw [← hq.2.2.2, mem_range_kernelι_iff]
      exact hyD
    exact (hi.greatest B a ha hsm hc hu hn) _ hy

set_option maxHeartbeats 950000 in
private theorem torsionSection_eq_one_of_reduction_one (x : (M₀).integralSections)
    {m : ℕ} (hm : m.Coprime p) (hx : x ^ m = 1) (hy : (M₀).reduction x = 1) :
    x = 1 := by
  let : IsDiscreteValuationRing O := (fixedFieldIntegers_strictHenselian F).1
  have h₁ : x ∈ (M₀).congruenceKernelAt 1 := by
    rw [(M₀).congruenceKernelAt_one]
    exact ((M₀).mem_congruenceKernel x).mpr hy
  have hn : ∀ n : ℕ, x ∈ (M₀).congruenceKernelAt ⟨n + 1, Nat.succ_pos n⟩ := by
    intro n
    have hpow := (M₀).pow_pow_mem_congruenceKernelAt 1 p
      (IntegralModel.residueChar_mem_maximalIdeal (R := O)) h₁ n
    have he : (⟨((1 : ℕ+) : ℕ) + n, Nat.add_pos_left (1 : ℕ+).pos n⟩ : ℕ+) =
        ⟨n + 1, Nat.succ_pos n⟩ := Subtype.ext (Nat.add_comm _ _)
    rw [he] at hpow
    exact mem_subgroup_of_coprime_pow _ (hm.pow_right n) hx hpow
  apply (M₀).eq_of_reductionAt_eq x 1
  intro n
  rw [map_one, ← (M₀).mem_congruenceKernelAt]
  have he : (⟨(n : ℕ) - 1 + 1, Nat.succ_pos _⟩ : ℕ+) = n :=
    Subtype.ext (Nat.sub_add_cancel n.pos)
  rw [← he]
  exact hn _

set_option maxHeartbeats 1050000 in
private theorem reduction_pPower_of_mem_minimal (x : (M₀).integralSections)
    {r : ℝ≥0} (hr : 0 < r) (hx : (M₀).integralPointMap x ∈ minimalCongruentPoints F T hT r) :
    ∃ d : ℕ, ((M₀).reduction x) ^ (p ^ d) = 1 := by
  let N := minimalCongruentModel F T hT r
  have hN : N.val.IsSmooth := N.property.1
  have hNpts := N.property.2.2
  have hIncl : N.val.integralPoints.map (rationalPoints.map (𝟙 T.toGrp)) ≤ (M₀).integralPoints := by
    rintro _ ⟨y, hy, rfl⟩
    simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id, minimalCongruentPoints_zero]
      using minimalCongruentPoints_antitone F T hT (show 0 ≤ r from zero_le) (hNpts.le hy)
  obtain ⟨φ⟩ := exists_hom_of_map_integralPoints_le IntegralModel.smoothHomExtension F hN rfl hIncl
  obtain ⟨y, hy⟩ := hNpts.ge hx
  have he : rationalPoints.map φ.hom y = x := (M₀).integralPointMap_injective (by
    rw [φ.integralPointMap_naturality, rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id]
    exact hy)
  let : Smooth N.val.group.X.hom := hN
  have hu := minimalCongruentPositiveUnipotent F T hT r N.val hr hN hNpts
  obtain ⟨d, hd⟩ := exists_hasUniformPowerExponent_of_isUnipotent p hu
  refine ⟨d, ?_⟩
  rw [← he, φ.reduction_naturality, ← map_pow, hd _ _, map_one]

set_option maxHeartbeats 1000000 in
theorem inducedImages_le_standard_at_positiveDepth {r : ℝ≥0} (hr : 0 < r) :
    inducedTorusStandardImages F T r ≤ localTorusFiltration F T hT r := by
  refine iSup_le fun S => iSup_le fun hS => iSup_le fun f => ?_
  let : IsAffine S.X.left := SplittingAssembly.isAffine_of_isTorus S.toGrp hS.isTorus
  let L := localTorusSplittingData F S hS.isTorus
  have hStd : localTorusFiltration F S hS.isTorus r = localGeometricCharacterCongruence F S r := by
    rw [localTorusFiltration_eq_of_splitting F L.L S hS.isTorus L.splits]
    exact localTorusFiltrationAtSplitting_eq_geometric_of_induced F L.L S L.splits hS hr
  rw [← hStd]
  exact map_localTorusFiltration_le F S hS.isTorus hT f r

set_option maxHeartbeats 1100000 in
private theorem section_decomposes (x : (M₀).integralSections) :
    ∃ (m : ℕ) (u t : (M₀).integralSections) (r : ℝ≥0),
      IsUnit (m : A) ∧ t ^ m = 1 ∧ x = u * t ∧ 0 < r ∧ r < 1 ∧
        (M₀).integralPointMap u ∈ inducedTorusStandardImages F T r := by
  obtain ⟨S, hS, n, W, hW, hWn, hD⟩ := exists_induced_normCover_decomposed F T hT
  let nGrp := CommGroupScheme.groupHom n
  obtain ⟨φ⟩ := exists_hom_of_map_integralPoints_le IntegralModel.smoothHomExtension F
    (n := nGrp) hW hWn le_rfl
  obtain ⟨_, ⟨x₀, rfl⟩, hx₀⟩ := hWn.ge (show (M₀).integralPointMap x ∈ (M₀).integralPoints from ⟨x, rfl⟩)
  obtain ⟨m, u, t, r, hm, ht, he, hr, hr₁, hu⟩ := hD x₀
  let f := rationalPoints.map φ.hom
  have hx : f x₀ = x := (M₀).integralPointMap_injective ((φ.integralPointMap_naturality x₀).trans hx₀)
  refine ⟨m, f u, f t, r, hm, ?_, ?_, hr, hr₁, ?_⟩
  · rw [← map_pow, ht, map_one]
  · rw [← hx, he, map_mul]
  · have hi : (localGeometricCharacterCongruence F S r).map
        (rationalPoints.map nGrp) ≤ inducedTorusStandardImages F T r :=
      le_iSup_of_le S (le_iSup_of_le hS (le_iSup_of_le n le_rfl))
    exact hi ⟨_, hu, (φ.integralPointMap_naturality u).symm⟩

private theorem standardPositive_le_geometric {r : ℝ≥0} (hr : 0 < r) :
    localTorusFiltration F T hT r ≤ localGeometricCharacterCongruence F T r := by
  let L := localTorusSplittingData F T hT
  rw [localTorusFiltration_eq_of_splitting F L.L T hT L.splits, localTorusFiltrationAtSplitting,
    ite_eq_right hr.ne']
  exact inf_le_right

set_option maxHeartbeats 2400000 in
private theorem standard_mem_iff_reduction_pPower (x : (M₀).integralSections) :
    ((M₀).integralPointMap x ∈ Std⁺ ↔ ∃ d : ℕ, ((M₀).reduction x) ^ (p ^ d) = 1) ∧
      ((∃ d : ℕ, ((M₀).reduction x) ^ (p ^ d) = 1) →
        ∃ r : ℝ≥0, 0 < r ∧ r < 1 ∧ (M₀).integralPointMap x ∈ inducedTorusStandardImages F T r) := by
  obtain ⟨m, u, t, r, hm, ht, hx, hr, hr₁, hu⟩ := section_decomposes F T hT x
  let q : Set.Iio (1 : ℝ≥0) := ⟨r, hr₁⟩
  have huMin : (M₀).integralPointMap u ∈ minimalCongruentPoints F T hT r := by
    rw [← show (q : ℝ≥0) = r from rfl, minimalCongruentPoints_of_lt_one,
      minimalCongruentShallowSubgroup, ite_eq_right hr.ne']
    exact (le_sup_right : inducedTorusStandardImages F T r ≤
      (M₀).congruenceSubgroup ⊔ inducedTorusStandardImages F T r) hu
  obtain ⟨d, hd⟩ := reduction_pPower_of_mem_minimal F T hT u hr huMin
  have huStd := inducedImages_le_standard_at_positiveDepth F T hT hr hu
  have hdvd : ¬ p ∣ m := by
    intro h
    have hmκ : (m : κ) = 0 := (CharP.cast_eq_zero_iff κ p m).mpr h
    apply ((IsLocalRing.residue_ne_zero_iff_isUnit (m : A)).mpr hm)
    rw [map_natCast, ← map_natCast (fixedFieldResidueInclusion F), hmκ, map_zero]
  have hcop : m.Coprime p := ((residueChar_prime F).out.coprime_iff_not_dvd.mpr hdvd).symm
  have htmul : t = u⁻¹ * x := by rw [hx, inv_mul_cancel_left]
  have hPrincipal (h : ∃ d : ℕ, ((M₀).reduction x) ^ (p ^ d) = 1) : x = u := by
    obtain ⟨e, he⟩ := h
    have htu : ((M₀).reduction t) ^ (p ^ (d + e)) = 1 := by
      rw [htmul, map_mul, map_inv, mul_pow, inv_pow]
      have hu' : ((M₀).reduction u) ^ (p ^ (d + e)) = 1 := by rw [pow_add, pow_mul, hd, one_pow]
      have hx' : ((M₀).reduction x) ^ (p ^ (d + e)) = 1 := by
        rw [add_comm d e, pow_add, pow_mul, he, one_pow]
      rw [hu', hx', inv_one, one_mul]
    have htm : ((M₀).reduction t) ^ m = 1 := by rw [← map_pow, ht, map_one]
    have htr : (M₀).reduction t = 1 := Subgroup.mem_bot.mp
      (mem_subgroup_of_coprime_pow ⊥ (hcop.pow_right (d + e)) htm (Subgroup.mem_bot.mpr htu))
    rw [hx, torsionSection_eq_one_of_reduction_one F T hT t hcop ht htr, mul_one]
  refine ⟨⟨?_, fun h => Set.mem_iUnion.mpr ⟨⟨r, hr⟩, by rw [hPrincipal h]; exact huStd⟩⟩,
    fun h => ⟨r, hr, hr₁, by rw [hPrincipal h]; exact hu⟩⟩
  intro hxStd
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hxStd
  let a := min (s : ℝ≥0) r
  have ha : 0 < a := lt_min s.property hr
  let H := localGeometricCharacterCongruence F T a
  have hxH : (M₀).integralPointMap x ∈ H :=
    standardPositive_le_geometric F T hT ha (localTorusFiltration_antitone F T hT (min_le_left _ _) hs)
  have huH : (M₀).integralPointMap u ∈ H :=
    standardPositive_le_geometric F T hT ha (localTorusFiltration_antitone F T hT (min_le_right _ _) huStd)
  have htH : (M₀).integralPointMap t ∈ H := by simpa only [htmul, map_mul, map_inv] using H.mul_mem (H.inv_mem huH) hxH
  have ht₀ := eq_one_of_positiveDepth_of_pow F T hT ha htH hm (by rw [← map_pow, ht, map_one])
  have het : t = 1 := (M₀).integralPointMap_injective (ht₀.trans (map_one _).symm)
  exact ⟨d, by rw [hx, het, mul_one, hd]⟩

set_option maxHeartbeats 1400000 in
/-- The standard strictly positive union within the connected Néron points
is the radical preimage, and each section in this preimage comes from a shallow
induced image. -/
theorem exists_standardZeroPlus_radicalPreimage :
    ∃ (U : GroupScheme (Spec (CommRingCat.of κ))) (i : U ⟶ (M₀).specialFibre),
      IsUnipotentRadical i ∧
      ((M₀).integralPoints : Set (rationalPoints T.toGrp)) ∩ Std⁺ =
        ↑(((rationalPoints.map i).range.comap (M₀).reduction).map (M₀).integralPointMap) ∧
      ∀ x : (M₀).integralSections, (M₀).reduction x ∈ (rationalPoints.map i).range →
        ∃ r : ℝ≥0, 0 < r ∧ r < 1 ∧ (M₀).integralPointMap x ∈ inducedTorusStandardImages F T r := by
  obtain ⟨U, i, hi⟩ := unipotentRadicalExistence κ (M₀).specialFibre
  refine ⟨U, i, hi, Set.Subset.antisymm ?_ ?_, ?_⟩
  · rintro _ ⟨⟨x, rfl⟩, hx⟩
    exact ⟨x, (residue_mem_radical_iff_pPower F T hT i hi _).mpr
      ((standard_mem_iff_reduction_pPower F T hT x).1.mp hx), rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, (standard_mem_iff_reduction_pPower F T hT x).1.mpr
      ((residue_mem_radical_iff_pPower F T hT i hi _).mp hx)⟩
  · intro x hx
    exact (standard_mem_iff_reduction_pPower F T hT x).2
      ((residue_mem_radical_iff_pPower F T hT i hi _).mp hx)

end Model

end Langlands.Geometry.Building
