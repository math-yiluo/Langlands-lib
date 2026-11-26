import Langlands.Correspondence.HenniartPadicArtinTransport
import Langlands.Correspondence.HenniartWeilElementaryLayer
import Langlands.Correspondence.RankOneOperationCompatibility
import Langlands.Correspondence.UnramifiedReciprocityBridge
import Langlands.ClassFieldTheory.Local.OpenFiniteIndexSeparationProof
import Langlands.ClassFieldTheory.Local.AbsoluteReciprocityProof
import Langlands.ClassFieldTheory.Local.WeilReciprocityProof
import Langlands.LocalFactor.DeligneHenniartUpperUnits
import Langlands.LocalFactor.Ramification.InertiaPresentationProof
import Langlands.LocalFactor.Ramification.RankOneArtinSum
import Langlands.ClassFieldTheory.Local.GradedUnitCoordinates
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Henniart's rank-one Weil orbit counts -/

noncomputable section

namespace Langlands.Henniart

open Correspondence LocalClassField Ramification Ramification.Padic Weil.Local
open VirtualRepresentation.LocalWeil.Ramification (upperGroup mem_upperGroup)

universe uK uW

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

private local instance : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology

local notation "T" => K.canonicalTopologicalData

/-- The finite upper group at a nonnegative level is the image of the corresponding
Weil upper group, and the Weil upper group lies in inertia. -/
private theorem trivial_upper_iff_finite
    (L : FiniteGaloisIntermediateField K.Carrier (AlgebraicClosure K.Carrier))
    (ψ : localWeilGroup K →* ℂˣ)
    (ρ : inertia (absoluteFiniteExtension K L).canonicalTopologicalData K.Carrier →* ℂˣ)
    (hρ : ∀ w : localInertia K, ρ (weilInertiaRestriction K L w) = ψ w)
    (v : ℝ) (hv : 0 ≤ v) :
    (∀ w ∈ upperGroup K v, ψ w = 1) ↔
      ∀ σ : inertia (absoluteFiniteExtension K L).canonicalTopologicalData K.Carrier,
        (σ : Gal(L/K.Carrier)) ∈
          upperRamificationGroup (absoluteFiniteExtension K L).canonicalTopologicalData
            K.Carrier v → ρ σ = 1 := by
  have himg : (absoluteUpperRamificationGroup K v).map
      (absoluteFiniteRestriction K L).toMonoidHom =
      upperRamificationGroup (absoluteFiniteExtension K L).canonicalTopologicalData
        K.Carrier v :=
    HerbrandBridge.absoluteUpperFiniteImage K L v (by linarith)
  have hI : absoluteUpperRamificationGroup K v ≤ K.absoluteInertia T := by
    rw [← HerbrandBridge.absoluteUpperCanonicalInertia K]
    exact absoluteUpperRamificationGroup_antitone K hv
  constructor
  · intro h σ hσ
    rw [← himg] at hσ
    obtain ⟨g, hg, heq⟩ := Subgroup.mem_map.mp hσ
    let w : localInertia K := (localInertiaEquiv K).symm ⟨g, hI hg⟩
    have hw : localProjection K w = g :=
      congrArg Subtype.val ((localInertiaEquiv K).apply_symm_apply ⟨g, hI hg⟩)
    have hres : weilInertiaRestriction K L w = σ := by
      apply Subtype.ext
      rw [weilInertiaRestriction_coe, hw]
      exact heq
    rw [← hres, hρ]
    exact h w ((mem_upperGroup K v w).2 (hw ▸ hg))
  · intro h w hw
    have hg := (mem_upperGroup K v w).1 hw
    have hwI : w ∈ localInertia K := by
      rw [localInertia_eq_comap K]
      exact hI hg
    rw [← hρ ⟨w, hwI⟩]
    apply h (weilInertiaRestriction K L ⟨w, hwI⟩)
    rw [← himg, weilInertiaRestriction_coe]
    exact ⟨localProjection K w, hg, rfl⟩

/-- The Artin expression at a finite inertia presentation of the character line
is its field character's unit-filtration conductor. -/
private theorem rankOne_presentation_conductor (e : ReciprocityCandidate K)
    (he : IsGeometricReciprocity K e) (χ : QuasiCharacter K)
    (P : FiniteInertiaPresentation K
      (FiniteRepresentation.characterLine.{uK, uW}
        (LocalFactor.RankOne.weilCharacter K e χ).toMonoidHom))
    (hP : Function.Surjective (weilInertiaRestriction K P.extension)) :
    P.artinConductor hP = ((T).multiplicativeConductor χ : ℚ) := by
  let ψ := (LocalFactor.RankOne.weilCharacter K e χ).toMonoidHom
  let π := (weilInertiaRestriction K P.extension).toMonoidHom
  let η := ψ.comp (localInertia K).subtype
  have hker : π.ker ≤ η.ker := by
    intro w hw
    have h : (FiniteRepresentation.characterLine.{uK, uW} ψ).representation w = 1 :=
      P.kernel_le hw
    have h1 := congrArg (fun f : Module.End ℂ (ULift.{uW} ℂ) => (f (ULift.up 1)).down) h
    apply MonoidHom.mem_ker.mpr
    apply Units.val_eq_one.mp
    change (ψ w : ℂ) * 1 = 1 at h1
    exact (mul_one _).symm.trans h1
  let ρ := π.liftOfSurjective hP ⟨η, hker⟩
  have hρ (w : localInertia K) : ρ (weilInertiaRestriction K P.extension w) = ψ w :=
    π.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv hP) ⟨η, hker⟩ w
  let E := (absoluteFiniteExtension K P.extension).canonicalTopologicalData
  have hlin : (P.representation hP).Equiv (rankOneCharacterRepresentation ρ) :=
    Representation.Equiv.mk ULift.moduleEquiv (by
      intro σ
      obtain ⟨w, rfl⟩ := hP σ
      rw [P.representation_apply, LinearMap.ext_iff]
      intro x
      change (ψ w : ℂ) * x.down = (ρ (weilInertiaRestriction K P.extension w) : ℂ) * x.down
      rw [hρ])
  change inertiaArtinConductor E K.Carrier (P.representation hP) = _
  rw [inertiaArtinConductor_equiv E K.Carrier hlin]
  apply inertiaArtinConductor_rankOne_eq_of_upper_levels
  intro v hv
  rw [← trivial_upper_iff_finite K P.extension ψ ρ hρ v hv,
    (T).multiplicativeConductor_le_iff_unitFiltration_le_ker χ,
    ← LocalFactor.NonabelianSystem.DeligneHenniart.upperGroup_map_reciprocityUnits K
      absoluteUpperReciprocityTheorems.{uK}.2.2.1
      (HerbrandBridge.absoluteUpperInertia K T) e he hv]
  constructor
  · intro h w hw
    exact h ⟨w, hw, rfl⟩
  · rintro h _ ⟨w, hw, rfl⟩
    exact h w hw

private theorem rankOne_hasArtinConductor_iff (e : ReciprocityCandidate K)
    (he : IsGeometricReciprocity K e) (χ : QuasiCharacter K) (a : ℕ) :
    Numerical.HasArtinConductor K (k := 0) (rankOneWeilCharacterClass.{uK, uW} K e χ) a ↔
      a = (T).multiplicativeConductor χ := by
  let ψ := LocalFactor.RankOne.weilCharacter K e χ
  let A := FiniteRepresentation.characterLine.{uK, uW} ψ.toMonoidHom
  obtain ⟨P⟩ := HerbrandBridge.continuousWeilFiniteInertiaPresentation K A
    (FiniteRepresentation.characterLine_isContinuous ψ)
  have hP := HerbrandBridge.weilInertiaRestriction_surjective K P.extension
  have ha := rankOne_presentation_conductor K e he χ P hP
  refine (Numerical.hasArtinConductor_iff_exists_padicPresentation K (k := 0) _ a).trans ?_
  constructor
  · rintro ⟨B, Q, hQ, hB, hb⟩
    change FiniteRepresentation.classOf B = FiniteRepresentation.classOf A at hB
    obtain ⟨f⟩ := (FiniteRepresentation.classOf_eq_iff B A).1 hB
    have h := (finiteInertiaConductorEquivalence K B A f Q P hQ hP).1
    rw [hb, ha] at h
    exact_mod_cast h
  · rintro rfl
    exact ⟨A, P, hP, rfl, ha⟩

private theorem mem_units_iff_ord (x : K.Carrierˣ) :
    x ∈ (T).unitFiltration 0 ↔ (T).ord (x : K.Carrier) = 0 := by
  rw [(T).unitFiltration_zero, (T).mem_unitSubgroup_iff_orderHom]
  rfl

/-- The unramified twist with parameter `z` multiplies the field character by
`z ^ ord`. -/
private theorem rankOne_twist (e : ReciprocityCandidate K) (he : IsGeometricReciprocity K e)
    (χ : QuasiCharacter K) (z : ℂˣ) :
    Numerical.weilUnramifiedTwist K 0 z (rankOneWeilCharacterClass.{uK, uW} K e χ) =
      rankOneWeilCharacterClass K e ((T).unramifiedCharacterContinuous z * χ) := by
  have hu : LocalFactor.RankOne.weilCharacter K e ((T).unramifiedCharacterContinuous z) =
      localUnramifiedCharacter K z := by
    apply ContinuousMonoidHom.ext
    intro w
    change z ^ (T).ord (reciprocityHom K e w : K.Carrier) = z ^ localDegreeInt K w
    rw [ord_reciprocityHom K he]
  have htw := IsRankOneWeilCharacter.twist K (rankOneWeilCharacterClass_spec.{uK, uW} K e χ)
    (LocalFactor.RankOne.weilCharacter K e ((T).unramifiedCharacterContinuous z))
  -- The scalar character of the twist is the pullback of the product.
  change IsRankOneWeilCharacter K (weilCharacter K e ((T).unramifiedCharacterContinuous z * χ))
    (FiniteRepresentation.continuousIrreducibleTwistEquiv _ 1 _) at htw
  rw [hu] at htw
  exact IsRankOneWeilCharacter.class_unique K htw (rankOneWeilCharacterClass_spec K e _)

private theorem rankOne_torsionNumber (e : ReciprocityCandidate K)
    (he : IsGeometricReciprocity K e) (χ : QuasiCharacter K) :
    Numerical.weilTorsionNumber K (k := 0) (rankOneWeilCharacterClass.{uK, uW} K e χ) = 1 := by
  let σ := rankOneWeilCharacterClass.{uK, uW} K e χ
  have fixed_iff (z : ℂˣ) : Numerical.weilUnramifiedTwist K 0 z σ = σ ↔ z = 1 := by
    rw [rankOne_twist K e he]
    change rankOneWeilCharacterClass.{uK, uW} K e
      ((T).unramifiedCharacterContinuous z * χ) = rankOneWeilCharacterClass K e χ ↔ z = 1
    rw [(rankOneWeilCharacterClass_injective K e).eq_iff]
    constructor
    · intro h
      have hπ := congrArg (fun η : QuasiCharacter K => η (T).uniformizerUnit) h
      change (T).unramifiedCharacter z (T).uniformizerUnit * χ (T).uniformizerUnit = _ at hπ
      rw [(T).unramifiedCharacter_uniformizer] at hπ
      exact mul_right_cancel (hπ.trans (one_mul _).symm)
    · rintro rfl
      apply ContinuousMonoidHom.ext
      intro x
      change (1 : ℂˣ) ^ (T).ord (x : K.Carrier) * χ x = χ x
      rw [one_zpow, one_mul]
  change Nat.card {z : ℂˣ // Numerical.weilUnramifiedTwist K 0 z σ = σ} = 1
  rw [Nat.card_congr (Equiv.subtypeEquivRight fixed_iff)]
  exact Nat.card_unique

private abbrev rankOneOrbit (e : ReciprocityCandidate K) (χ : QuasiCharacter K) :
    VirtualRepresentation.Weil.UnramifiedOrbitClasses.{uK, uW} (localDegree K) :=
  VirtualRepresentation.Weil.unramifiedOrbitClass (localDegree K)
    ⟨1, rankOneWeilCharacterClass.{uK, uW} K e χ⟩

/-- Two characters give the same actual Weil twist orbit exactly when their
restrictions to valuation units are equal. -/
private theorem rankOne_orbit_eq_iff (e : ReciprocityCandidate K) (he : IsGeometricReciprocity K e)
    (χ η : QuasiCharacter K) :
    rankOneOrbit.{uK, uW} K e χ = rankOneOrbit.{uK, uW} K e η ↔
      ∀ x ∈ (T).unitFiltration 0, χ x = η x := by
  rw [VirtualRepresentation.Weil.unramifiedOrbitClass_eq_iff]
  constructor
  · rintro ⟨z, hz⟩ x hx
    have ht : Numerical.weilUnramifiedTwist K 0 z (rankOneWeilCharacterClass.{uK, uW} K e η) =
        rankOneWeilCharacterClass K e χ := eq_of_heq (Sigma.mk.inj hz).2
    rw [rankOne_twist K e he] at ht
    have h := (rankOneWeilCharacterClass_injective K e) ht
    have hx' := congrArg (fun ψ : QuasiCharacter K => ψ x) h
    change z ^ (T).ord (x : K.Carrier) * η x = χ x at hx'
    rw [(mem_units_iff_ord K x).mp hx, zpow_zero, one_mul] at hx'
    exact hx'.symm
  · intro h
    let δ := χ.toMonoidHom / η.toMonoidHom
    have hδ : (T).IsUnramifiedCharacter δ := by
      rw [PadicField.TopologicalData.IsUnramifiedCharacter, ← (T).ker_ordUnits]
      intro x hx
      have hx' : x ∈ (T).unitFiltration 0 := (mem_units_iff_ord K x).2 hx
      change χ x / η x = 1
      rw [h x hx', div_self']
    let z := δ (T).uniformizerUnit
    have hχ : (T).unramifiedCharacterContinuous z * η = χ := by
      apply ContinuousMonoidHom.ext
      intro x
      change (T).unramifiedCharacter z x * η x = χ x
      rw [← (T).eq_unramifiedCharacter δ hδ]
      exact div_mul_cancel _ _
    refine ⟨z, ?_⟩
    have ht := rankOne_twist.{uK, uW} K e he η z
    rw [hχ] at ht
    exact Sigma.ext rfl (heq_of_eq ht)

/-- Remove the uniformizer component from a field unit. -/
private def unitRetraction : K.Carrierˣ →* (T).unitFiltration 0 := by
  let s : Multiplicative ℤ →* K.Carrierˣ := zpowersHom _ (T).uniformizerUnit
  have hs (z : Multiplicative ℤ) : (T).orderHom (s z) = z := by
    change (T).orderHom ((T).uniformizerUnit ^ z.toAdd) = z
    rw [map_zpow]
    have hπ : (T).orderHom (T).uniformizerUnit = Multiplicative.ofAdd (1 : ℤ) :=
      congrArg Multiplicative.ofAdd (LocalFactor.PadicAbelian.uniformizerUnit_ord T)
    rw [hπ]
    change Multiplicative.ofAdd (z.toAdd • (1 : ℤ)) = z
    simp
  let r : K.Carrierˣ →* K.Carrierˣ := (MonoidHom.id _) / (s.comp (T).orderHom)
  refine r.codRestrict _ fun x => ?_
  rw [(T).unitFiltration_zero, (T).mem_unitSubgroup_iff_orderHom]
  change (T).orderHom (x / s ((T).orderHom x)) = 1
  rw [map_div, hs, div_self']

private theorem unitRetraction_apply_of_mem {x : K.Carrierˣ} (hx : x ∈ (T).unitFiltration 0) :
    unitRetraction K x = ⟨x, hx⟩ := by
  apply Subtype.ext
  change x / (T).uniformizerUnit ^ (T).ord (x : K.Carrier) = x
  rw [(mem_units_iff_ord K x).mp hx, zpow_zero, div_one]

private abbrev UnitQuotient (n : ℕ) :=
  ((T).unitFiltration 0) ⧸ ((T).unitFiltration n).subgroupOf ((T).unitFiltration 0)

private def unitQuotientProjection (n : ℕ) : K.Carrierˣ →* UnitQuotient K n :=
  (QuotientGroup.mk' _).comp (unitRetraction K)

private theorem unitQuotientProjection_apply_of_mem (n : ℕ) {x : K.Carrierˣ}
    (hx : x ∈ (T).unitFiltration 0) :
    unitQuotientProjection K n x = QuotientGroup.mk' _ ⟨x, hx⟩ := by
  rw [unitQuotientProjection, MonoidHom.comp_apply, unitRetraction_apply_of_mem K hx]

private theorem unitQuotientProjection_eq_one (n : ℕ) {x : K.Carrierˣ}
    (hx : x ∈ (T).unitFiltration n) : unitQuotientProjection K n x = 1 := by
  rw [unitQuotientProjection_apply_of_mem K n ((T).unitFiltration_antitone (Nat.zero_le n) hx)]
  exact (QuotientGroup.eq_one_iff _).mpr hx

/-- Extend a character of `U⁰/Uⁿ` to `Kˣ`, taking value one on the uniformizer. -/
private def extendUnitCharacter (n : ℕ) (ψ : UnitQuotient K n →* ℂˣ) : QuasiCharacter K where
  toMonoidHom := ψ.comp (unitQuotientProjection K n)
  continuous_toFun := by
    let := (T).valuativeRel
    let := (T).localField
    apply continuous_of_tendsto_nhds_one (ψ.comp (unitQuotientProjection K n))
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [((T).isOpen_unitFiltration n).mem_nhds ((T).unitFiltration n).one_mem] with x hx
    simp only [MonoidHom.comp_apply, unitQuotientProjection_eq_one K n hx, map_one]

private theorem extendUnitCharacter_apply_of_mem (n : ℕ) (ψ : UnitQuotient K n →* ℂˣ)
    {x : K.Carrierˣ} (hx : x ∈ (T).unitFiltration 0) :
    extendUnitCharacter K n ψ x = ψ (QuotientGroup.mk' _ ⟨x, hx⟩) :=
  congrArg ψ (unitQuotientProjection_apply_of_mem K n hx)

private theorem extendUnitCharacter_conductor_le (n : ℕ) (ψ : UnitQuotient K n →* ℂˣ) :
    (T).multiplicativeConductor (extendUnitCharacter K n ψ) ≤ n := by
  rw [(T).multiplicativeConductor_le_iff_unitFiltration_le_ker]
  intro x hx
  change ψ (unitQuotientProjection K n x) = 1
  rw [unitQuotientProjection_eq_one K n hx, map_one]

/-- The cumulative set of rank-one Weil twist orbits at conductor at most `n`. -/
private def rankOneBounded (e : ReciprocityCandidate K) (n : ℕ) :
    Set (VirtualRepresentation.Weil.UnramifiedOrbitClasses.{uK, uW} (localDegree K)) :=
  {c | ∃ χ : QuasiCharacter K,
    rankOneOrbit.{uK, uW} K e χ = c ∧ (T).multiplicativeConductor χ ≤ n}

private theorem rankOneBounded_mono (e : ReciprocityCandidate K) :
    Monotone (rankOneBounded.{uK, uW} K e) := by
  intro m n h c hc
  obtain ⟨χ, heq, hχ⟩ := hc
  exact ⟨χ, heq, hχ.trans h⟩

private theorem rankOneOrbit_mem_bounded (e : ReciprocityCandidate K)
    (he : IsGeometricReciprocity K e) (χ : QuasiCharacter K) (n : ℕ) :
    rankOneOrbit.{uK, uW} K e χ ∈ rankOneBounded.{uK, uW} K e n ↔
      (T).multiplicativeConductor χ ≤ n := by
  constructor
  · rintro ⟨η, heq, hη⟩
    rw [(T).multiplicativeConductor_le_iff_unitFiltration_le_ker] at hη ⊢
    intro x hx
    have h := (rankOne_orbit_eq_iff K e he η χ).mp heq x
      ((T).unitFiltration_antitone (Nat.zero_le n) hx)
    exact h.symm.trans (hη hx)
  · intro h
    exact ⟨χ, rfl, h⟩

/-- The size of `U⁰/U^(n+1)` follows from the successive residue-field quotients. -/
private theorem unitQuotient_card (n : ℕ) :
    Nat.card (UnitQuotient K (n + 1)) = ((T).residueCardinality - 1) * (T).residueCardinality ^ n := by
  induction n with
  | zero =>
    change Nat.card ((T).GradedUnits 0) = _
    rw [Nat.card_congr (T).gradedUnitsZeroEquiv.toEquiv, Nat.card_units, pow_zero, mul_one]
    rfl
  | succ n ih =>
    have hstep : ((T).unitFiltration (n + 1 + 1)).relIndex ((T).unitFiltration (n + 1)) =
        (T).residueCardinality := by
      change Nat.card ((T).GradedUnits (n + 1)) = _
      exact Nat.card_congr
        ((T).gradedUnitsPositiveEquiv (T).uniformizer (T).ord_uniformizer
          (n + 1) (Nat.succ_pos n)).toEquiv
    change ((T).unitFiltration (n + 1)).relIndex ((T).unitFiltration 0) = _ at ih
    change ((T).unitFiltration (n + 1 + 1)).relIndex ((T).unitFiltration 0) = _
    rw [← Subgroup.relIndex_mul_relIndex _ ((T).unitFiltration (n + 1)) _
      ((T).unitFiltration_antitone (Nat.le_succ (n + 1)))
      ((T).unitFiltration_antitone (Nat.zero_le (n + 1))), hstep, ih, pow_succ]
    ac_rfl

private theorem rankOneBounded_encard (e : ReciprocityCandidate K)
    (he : IsGeometricReciprocity K e) (n : ℕ) :
    (rankOneBounded.{uK, uW} K e (n + 1)).encard =
      ((((T).residueCardinality - 1) * (T).residueCardinality ^ n : ℕ) : ℕ∞) := by
  let m := n + 1
  let f (ψ : UnitQuotient K m →* ℂˣ) := rankOneOrbit.{uK, uW} K e (extendUnitCharacter K m ψ)
  have hf : Function.Injective f := by
    intro ψ φ h
    apply MonoidHom.ext
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
    have h' := (rankOne_orbit_eq_iff K e he _ _).mp h x x.property
    simpa only [extendUnitCharacter_apply_of_mem K m _ x.property] using h'
  have hrange : Set.range f = rankOneBounded.{uK, uW} K e m := by
    ext c
    constructor
    · rintro ⟨ψ, rfl⟩
      exact ⟨_, rfl, extendUnitCharacter_conductor_le K m ψ⟩
    · rintro ⟨χ, hχ, hle⟩
      have hker := ((T).multiplicativeConductor_le_iff_unitFiltration_le_ker χ m).mp hle
      let φ := χ.toMonoidHom.comp ((T).unitFiltration 0).subtype
      have hφ : ((T).unitFiltration m).subgroupOf ((T).unitFiltration 0) ≤ φ.ker :=
        fun _x hx => hker hx
      refine ⟨QuotientGroup.lift _ φ hφ, ?_⟩
      rw [← hχ]
      apply (rankOne_orbit_eq_iff K e he _ _).mpr
      intro x hx
      rw [extendUnitCharacter_apply_of_mem K m _ hx]
      exact QuotientGroup.lift_mk _ hφ ⟨x, hx⟩
  have hq := (T).residueCardinality_gt_one
  have hQ : Nat.card (UnitQuotient K m) ≠ 0 := by
    rw [unitQuotient_card K n]
    exact Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega))
  let : Finite (UnitQuotient K m) := Nat.finite_of_card_ne_zero hQ
  let : NeZero (Monoid.exponent (UnitQuotient K m) : ℂ) :=
    ⟨by exact_mod_cast (Monoid.exponent_ne_zero_of_finite (G := UnitQuotient K m))⟩
  have hdual := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (UnitQuotient K m) ℂ
  let : Finite (UnitQuotient K m →* ℂˣ) := Nat.finite_of_card_ne_zero (by rw [hdual]; exact hQ)
  change (rankOneBounded.{uK, uW} K e m).encard = _
  rw [← hrange, Set.encard, ← ENat.card_congr (Equiv.ofInjective f hf), ENat.card_eq_coe_natCard,
    hdual, unitQuotient_card]

private theorem rankOne_hasSwan_iff (e : ReciprocityCandidate K)
    (he : IsGeometricReciprocity K e) (χ : QuasiCharacter K) (s : ℕ) :
    Numerical.HasWeilSwan K (k := 0) (rankOneWeilCharacterClass.{uK, uW} K e χ) s ↔
      (T).multiplicativeConductor χ - 1 = s := by
  change (∃ a : ℕ, Numerical.HasArtinConductor K (k := 0)
    (rankOneWeilCharacterClass.{uK, uW} K e χ) a ∧ a - 1 = s) ↔ _
  simp only [rankOne_hasArtinConductor_iff K e he, exists_eq_left]

private theorem rankOne_stratum_zero (e : ReciprocityCandidate K) (he : IsGeometricReciprocity K e) :
    Numerical.weilRefinedStratum.{uK, uW} K 0 0 1 = rankOneBounded.{uK, uW} K e 1 := by
  ext c
  constructor
  · rintro ⟨σ, hc, hs, -⟩
    obtain ⟨χ, rfl⟩ := rankOneWeilCharacterClass_surjective K e σ
    have hχ := (rankOne_hasSwan_iff K e he χ 0).mp hs
    exact ⟨χ, hc, by omega⟩
  · rintro ⟨χ, hc, hχ⟩
    exact ⟨rankOneWeilCharacterClass K e χ, hc,
      (rankOne_hasSwan_iff K e he χ 0).mpr (by omega), rankOne_torsionNumber K e he χ⟩

private theorem rankOne_stratum_succ (e : ReciprocityCandidate K) (he : IsGeometricReciprocity K e)
    (n : ℕ) : Numerical.weilRefinedStratum.{uK, uW} K 0 (n + 1) 1 =
      rankOneBounded.{uK, uW} K e (n + 1 + 1) \ rankOneBounded.{uK, uW} K e (n + 1) := by
  ext c
  constructor
  · rintro ⟨σ, hc, hs, -⟩
    obtain ⟨χ, rfl⟩ := rankOneWeilCharacterClass_surjective K e σ
    have hχ := (rankOne_hasSwan_iff K e he χ (n + 1)).mp hs
    change rankOneOrbit.{uK, uW} K e χ = c at hc
    rw [← hc, Set.mem_sdiff, rankOneOrbit_mem_bounded K e he, rankOneOrbit_mem_bounded K e he]
    omega
  · rintro ⟨⟨χ, hc, hχ⟩, hnot⟩
    rw [← hc, rankOneOrbit_mem_bounded K e he] at hnot
    exact ⟨rankOneWeilCharacterClass K e χ, hc,
      (rankOne_hasSwan_iff K e he χ (n + 1)).mpr (by omega), rankOne_torsionNumber K e he χ⟩

/-- The rank-one Weil orbit counts, with no restriction on either universe level. -/
theorem weilRankOneCount : WeilRankOneCountStatement.{uK, uW} := by
  intro p _ K
  obtain ⟨e, he, -⟩ := weilReciprocityTheorems.{uK}.1 p K K.canonicalTopologicalData
  constructor
  · rw [Numerical.weilTwistIrreducibleCount, rankOne_stratum_zero K e he]
    simpa only [pow_zero, mul_one] using rankOneBounded_encard.{uK, uW} K e he 0
  · intro s hs
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show s ≠ 0 by omega)
    rw [Numerical.weilTwistIrreducibleCount, rankOne_stratum_succ K e he, Nat.succ_sub_one]
    have h := Set.encard_sdiff_add_encard_of_subset
      (rankOneBounded_mono.{uK, uW} K e (Nat.le_succ (n + 1)))
    rw [rankOneBounded_encard K e he n, rankOneBounded_encard K e he (n + 1)] at h
    let q := K.canonicalTopologicalData.residueCardinality
    have hq : 1 ≤ q := K.canonicalTopologicalData.residueCardinality_gt_one.le
    have hnum : (q - 1) * q ^ (n + 1) = (q - 1) ^ 2 * q ^ n + (q - 1) * q ^ n := calc
      _ = (q - 1) * q ^ n * q := by rw [pow_succ, mul_assoc]
      _ = (q - 1) * q ^ n * (q - 1 + 1) := by rw [Nat.sub_add_cancel hq]
      _ = _ := by ring
    apply ENat.add_left_injective_of_ne_top (ENat.natCast_ne_top ((q - 1) * q ^ n))
    refine h.trans ?_
    simpa only [ENat.natCast_add] using congrArg (fun a : ℕ => (a : ℕ∞)) hnum

end Langlands.Henniart
