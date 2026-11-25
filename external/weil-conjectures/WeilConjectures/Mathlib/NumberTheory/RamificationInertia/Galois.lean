/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Unramified.Dedekind
public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.RingTheory.Smooth.Fiber
public import WeilConjectures.Mathlib.RingTheory.Invariant.Profinite

/-!
# Inertia groups and unramified intermediate extensions

Let `T / S / R` be a tower of domains, `G` a finite Galois group of `T / R` and `H ≤ G` a Galois
group of `T / S`. If the inertia group `I_G(P)` of a prime `P` of `T` is contained in `H`, then
the prime `P ∩ S` of `S` is unramified over `R`
(`Ideal.ramificationIdx_under_eq_one_of_inertia_le`): the inertia groups of `P` in `G` and `H`
then coincide, and their orders are the ramification indices `e(P | R)` and `e(P | S)`, while
`e(P | R) = e(P ∩ S | R) e(P | S)`.

Let `Ω` be a Galois extension of the fraction field `K` of a Dedekind domain `R`, and `Q` a maximal
ideal of the integral closure of `R` in `Ω`. If the inertia group of `Q` in `Gal(Ω / K)` fixes the
images of all `R`-algebra maps from a Dedekind domain `T` finite over `R` to `Ω`, then all primes
of `T` over `Q ∩ R` are unramified (`Ideal.ramificationIdx_eq_one_of_forall_inertia`): this is
reduced to the Galois closure of the image of `T`, using that inertia lifts from finite Galois
subextensions to `Ω` (`Ideal.exists_mem_inertia_eqOn`). Consequently, if `π ∈ R` vanishes exactly
at `Q ∩ R` and `A` is a finite étale `R[1/π]`-domain on whose `R`-algebra maps to `Ω` the inertia
group acts trivially, then the integral closure of `R` in `A` is finite étale over `R`
(`Ideal.etale_integralClosure_of_forall_inertia`).
-/

@[expose] public section

namespace Ideal

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
  [Algebra R T] [IsScalarTower R S T] [IsDomain R] [IsDomain S] [IsDomain T]
  [Module.Finite R T] [Module.Finite S T] [Module.Flat R T] [Module.Flat S T]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G T] [IsGaloisGroup G R T]
  (H : Subgroup G) [IsGaloisGroup H S T]

/-- **Primes below the inertia field are unramified.** If the inertia group of a prime `P` of
`T` in `Gal(T / R)` is contained in `Gal(T / S)`, then `P ∩ S` is unramified over `R`. -/
theorem ramificationIdx_under_eq_one_of_inertia_le (p : Ideal R) [p.IsPrime] (P : Ideal T)
    [P.IsPrime] [P.LiesOver p] [PerfectField p.ResidueField]
    [PerfectField (P.under S).ResidueField] (h : P.inertia G ≤ H) :
    (P.under S).ramificationIdx R = 1 := by
  have hG : Nat.card (P.inertia G) = P.ramificationIdx R := by
    rw [card_inertia_eq_ramificationIdxIn p P, ramificationIdxIn_eq_ramificationIdx p P G]
  have hH : Nat.card (P.inertia H) = P.ramificationIdx S := by
    rw [card_inertia_eq_ramificationIdxIn (P.under S) P,
      ramificationIdxIn_eq_ramificationIdx (P.under S) P H]
  have hGH : Nat.card (P.inertia H) = Nat.card (P.inertia G) := by
    have : P.inertia H = (P.inertia G).subgroupOf H := rfl
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  have htower := ramificationIdx_tower (R := R) (P.under S) P
  have hne : P.ramificationIdx R ≠ 0 := by
    rw [← hG]
    exact Nat.card_pos.ne'
  rw [← hH, hGH, hG] at htower
  exact (mul_eq_right₀ hne).1 htower.symm

private lemma perfectField_residueField_of_finite {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] (p : Ideal A) [p.IsPrime] (q : Ideal B)
    [q.IsPrime] [q.LiesOver p] [PerfectField p.ResidueField] :
    PerfectField q.ResidueField := by
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  exact Algebra.IsAlgebraic.perfectField p.ResidueField

end Ideal

section SeparableClosure

open IntermediateField

variable {R K Ω : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω]

namespace Ideal

/-- The map from a ring `T` with an `R`-algebra map `ψ : T → Ω` to the integral closure of `R`
in `Ω`, for `T` integral over `R`. -/
noncomputable def integralClosureMap {T : Type*} [CommRing T] [Algebra R T]
    [Algebra.IsIntegral R T] (ψ : T →ₐ[R] Ω) : T →+* integralClosure R Ω :=
  (ψ.codRestrict (integralClosure R Ω) fun x ↦
    (Algebra.IsIntegral.isIntegral (R := R) x).map ψ).toRingHom

omit [IsDedekindDomain R] [IsFractionRing R K] [IsGalois K Ω] in
@[simp]
lemma coe_integralClosureMap {T : Type*} [CommRing T] [Algebra R T] [Algebra.IsIntegral R T]
    (ψ : T →ₐ[R] Ω) (x : T) : (integralClosureMap ψ x : Ω) = ψ x :=
  rfl

omit [IsFractionRing R K] [IsGalois K Ω] in
/-- An `R`-algebra map from a domain integral over `R` to `Ω` is injective. -/
lemma injective_of_isIntegral {T : Type*} [CommRing T] [IsDomain T] [Algebra R T]
    [Algebra.IsIntegral R T] (ψ : T →ₐ[R] Ω) (hR : Function.Injective (algebraMap R Ω)) :
    Function.Injective ψ := by
  refine (injective_iff_map_eq_zero ψ).2 fun x hx ↦ ?_
  have hker : RingHom.ker ψ.toRingHom = ⊥ := by
    refine Ideal.eq_bot_of_under_eq_bot (R := R) ?_
    ext r
    simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes, Ideal.mem_bot]
    exact map_eq_zero_iff _ hR
  have : x ∈ RingHom.ker ψ.toRingHom := hx
  rwa [hker, Ideal.mem_bot] at this

omit [IsDedekindDomain R] [IsFractionRing R K] in
private lemma inertia_comap_integralClosureMap_le_fixingSubgroup
    {T : Type*} [CommRing T] [Algebra R T] (ψ : T →ₐ[R] Ω)
    (Q : Ideal (integralClosure R Ω)) [Q.IsMaximal]
    (M : IntermediateField K Ω) [Normal K M] (hM : adjoin K (Set.range ψ) ≤ M)
    (hI : ∀ σ ∈ Q.inertia Gal(Ω/K), ∀ x, σ (ψ x) = ψ x) :
    (Q.comap (integralClosureMap
      ((M.val.restrictScalars R).comp (integralClosure R M).val))).inertia
      Gal(M/K) ≤ fixingSubgroup Gal(M/K) (restrict hM : Set M) := by
  let TM := integralClosure R M
  let iTB : TM →+* integralClosure R Ω :=
    integralClosureMap ((M.val.restrictScalars R).comp (integralClosure R M).val)
  intro τ hτ
  obtain ⟨τ', hτ'⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) (E := Ω) τ
  have hτ'M (x : M) : τ' (x : Ω) = (τ x : Ω) := by
    rw [← hτ']
    exact (AlgEquiv.restrictNormal_commutes τ' M x).symm
  obtain ⟨σ, hσ, hσM⟩ := exists_mem_inertia_eqOn M Q τ' fun b hb ↦ by
    let t : TM := ⟨⟨b, hb⟩,
      (isIntegral_algHom_iff (M.val.restrictScalars R) Subtype.val_injective).1 b.2⟩
    have ht := hτ t
    have hiτ : iTB (τ • t) = τ' • b := Subtype.ext (hτ'M ⟨b, hb⟩).symm
    have : iTB (τ • t - t) ∈ Q := ht
    rwa [map_sub iTB, hiτ] at this
  have hσL : adjoin K (Set.range ψ) ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
    refine adjoin_le_iff.2 ?_
    rintro _ ⟨x, rfl⟩
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    have hst : σ ∈ MulAction.stabilizer Gal(Ω/K) (ψ x) := hI σ hσ x
    exact (Subgroup.zpowers_le.2 hst) hf
  rw [_root_.mem_fixingSubgroup_iff]
  intro x hx
  apply Subtype.ext
  have hxL : (x : Ω) ∈ adjoin K (Set.range ψ) := (mem_restrict hM x).1 hx
  have h1 : σ (x : Ω) = x :=
    (IntermediateField.mem_fixedField_iff _ _).1 (hσL hxL) σ (Subgroup.mem_zpowers σ)
  change (τ x : Ω) = x
  rw [← hτ'M, ← hσM _ x.2, h1]

private lemma ramificationIdx_comap_integralClosureMap_eq_one_of_normal
    {T : Type*} [CommRing T] [IsDedekindDomain T] [Algebra R T]
    [Module.Finite R T] [Module.IsTorsionFree R T]
    (ψ : T →ₐ[R] Ω) (Q : Ideal (integralClosure R Ω)) [Q.IsMaximal] (m : Ideal R)
    [m.IsMaximal] [Q.LiesOver m] [PerfectField m.ResidueField]
    (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M]
    (hL'M : adjoin K (Set.range ψ) ≤ M)
    (hI : ∀ σ ∈ Q.inertia Gal(Ω/K), ∀ x, σ (ψ x) = ψ x) :
    (Q.comap (integralClosureMap ψ)).ramificationIdx R = 1 := by
  have : Algebra.IsIntegral R T := Algebra.IsIntegral.of_finite R T
  let L' : IntermediateField K Ω := adjoin K (Set.range ψ)
  -- the integral closure of `R` in `M`, with its Galois group
  let TM := integralClosure R M
  have : IsFractionRing TM M := integralClosure.isFractionRing_of_finite_extension K M
  have : Module.Finite R TM := IsIntegralClosure.finite R K M TM
  have : IsDedekindDomain TM := integralClosure.isDedekindDomain R K M
  have : IsGaloisGroup Gal(M/K) R TM := IsGaloisGroup.of_isFractionRing _ _ _ K M
  -- the subfield `L'` of `M`, its ring of integers `S` and its Galois group `H`
  let LM : IntermediateField K M := restrict hL'M
  let H : Subgroup Gal(M/K) := fixingSubgroup Gal(M/K) (LM : Set M)
  let S := integralClosure R LM
  have : IsFractionRing S LM := integralClosure.isFractionRing_of_finite_extension K LM
  have : Module.Finite R S := IsIntegralClosure.finite R K LM S
  have : IsDedekindDomain S := integralClosure.isDedekindDomain R K LM
  have : IsScalarTower R LM M := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R K LM, IsScalarTower.algebraMap_apply R K M]
    rfl
  let iST : S →+* TM := ((IsScalarTower.toAlgHom R LM M).domRestrict
    (integralClosure R LM) |>.codRestrict (integralClosure R M) fun x ↦
      x.2.map (IsScalarTower.toAlgHom R LM M)).toRingHom
  let _ : Algebra S TM := iST.toAlgebra
  let _ : SMul S TM := Algebra.toSMul
  let _ : Module S TM := Algebra.toModule
  have : IsScalarTower S TM M := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R S TM := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.IsIntegral R TM := Algebra.IsIntegral.of_finite R TM
  have : Algebra.IsIntegral S TM := Algebra.IsIntegral.tower_top R
  have : IsGaloisGroup H S TM := IsGaloisGroup.of_isFractionRing H S TM LM M
  have : Module.Finite S TM := Module.Finite.of_restrictScalars_finite R S TM
  -- `ψ` lands in the ring of integers `S` of `L'`
  have hψL' (x : T) : ψ x ∈ L' := subset_adjoin _ _ ⟨x, rfl⟩
  let ψM : T →ₐ[R] M := ψ.codRestrict ((M.toSubalgebra).restrictScalars R) fun x ↦ hL'M (hψL' x)
  let ψLM : T →ₐ[R] LM := ψM.codRestrict ((LM.toSubalgebra).restrictScalars R) fun x ↦
    (mem_restrict hL'M _).2 (hψL' x)
  let jTS : T →ₐ[R] S := ψLM.codRestrict ((integralClosure R LM)) fun x ↦
    (Algebra.IsIntegral.isIntegral (R := R) x).map ψLM
  let _ : Algebra T S := jTS.toRingHom.toAlgebra
  have : IsScalarTower R T S := IsScalarTower.of_algebraMap_eq fun r ↦ (jTS.commutes r).symm
  have hRΩ : Function.Injective (algebraMap R Ω) := by
    rw [IsScalarTower.algebraMap_eq R K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)
  have hψinj : Function.Injective ψ := injective_of_isIntegral ψ hRΩ
  have hjinj : Function.Injective (algebraMap T S) := fun x y hxy ↦
    hψinj (congrArg (fun z : S ↦ ((z : LM) : M) : S → Ω) hxy)
  have : Module.IsTorsionFree T S :=
    Module.isTorsionFree_iff_faithfulSMul.2 ((faithfulSMul_iff_algebraMap_injective T S).2 hjinj)
  -- the prime `P` of `TM` below `Q`
  let iTB : TM →+* integralClosure R Ω :=
    integralClosureMap ((M.val.restrictScalars R).comp (integralClosure R M).val)
  let P : Ideal TM := Q.comap iTB
  have hiTB : iTB.comp (algebraMap R TM) = algebraMap R (integralClosure R Ω) := by
    ext r
    change ((algebraMap R M r : M) : Ω) = algebraMap R Ω r
    rw [IsScalarTower.algebraMap_apply R K M, IsScalarTower.algebraMap_apply R K Ω]
    rfl
  have hPm : P.LiesOver m := ⟨by
    rw [Ideal.under, Ideal.comap_comap, hiTB, Ideal.over_def Q m]⟩
  have hcomp : iTB.comp ((algebraMap S TM).comp (algebraMap T S)) = integralClosureMap ψ := by
    ext x
    rfl
  have : (P.under S).LiesOver (Q.comap (integralClosureMap ψ)) := ⟨by
    rw [Ideal.under, Ideal.under, Ideal.comap_comap, Ideal.comap_comap, ← hcomp]⟩
  -- the inertia group of `P` fixes `L'`
  have hle : P.inertia Gal(M/K) ≤ H :=
    inertia_comap_integralClosureMap_le_fixingSubgroup ψ Q M hL'M hI
  have : (P.under S).IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (P.under S) m
  have hperfS : PerfectField (P.under S).ResidueField :=
    perfectField_residueField_of_finite m (P.under S)
  have : Module.IsTorsionFree R TM := Module.isTorsionFree_iff_faithfulSMul.2
    ((faithfulSMul_iff_algebraMap_injective R TM).2 fun x y hxy ↦ hRΩ (by
      have h := congrArg iTB hxy
      have hx := RingHom.congr_fun hiTB x
      have hy := RingHom.congr_fun hiTB y
      simp only [RingHom.comp_apply] at hx hy
      rw [hx, hy] at h
      exact congrArg Subtype.val h))
  have : Module.IsTorsionFree S TM := Module.isTorsionFree_iff_faithfulSMul.2
    ((faithfulSMul_iff_algebraMap_injective S TM).2 fun x y hxy ↦
      Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun z : TM ↦ ((z : M) : Ω)) hxy))))
  have hS := Ideal.ramificationIdx_under_eq_one_of_inertia_le (S := S) H m P hle
  have htower := Ideal.ramificationIdx_tower (R := R) (Q.comap (integralClosureMap ψ)) (P.under S)
  rw [hS] at htower
  exact (mul_eq_one.1 htower.symm).1

/-- **Primes of a cover fixed by inertia are unramified.** Let `T` be a Dedekind domain finite
over `R`, with an `R`-algebra map `ψ : T → Ω`, and `Q` a maximal ideal of the integral closure of
`R` in `Ω` over a maximal ideal `m` of `R` with perfect residue field. If the inertia group of `Q`
in `Gal(Ω / K)` fixes `ψ(T)` pointwise, then the prime `ψ⁻¹ Q` of `T` is unramified over `R`. -/
theorem ramificationIdx_comap_integralClosureMap_eq_one {T : Type*} [CommRing T]
    [IsDedekindDomain T] [Algebra R T] [Module.Finite R T] [Module.IsTorsionFree R T]
    (ψ : T →ₐ[R] Ω) (Q : Ideal (integralClosure R Ω)) [Q.IsMaximal] (m : Ideal R)
    [m.IsMaximal] [Q.LiesOver m] [PerfectField m.ResidueField]
    (hI : ∀ σ ∈ Q.inertia Gal(Ω/K), ∀ x, σ (ψ x) = ψ x) :
    (Q.comap (integralClosureMap ψ)).ramificationIdx R = 1 := by
  have : Algebra.IsIntegral R T := Algebra.IsIntegral.of_finite R T
  -- the field `L'` generated by `ψ(T)` and its Galois closure `M`
  let L' : IntermediateField K Ω := adjoin K (Set.range ψ)
  have : FiniteDimensional K L' := by
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := T)
    have : L' = adjoin K (ψ '' s) := by
      refine le_antisymm (adjoin_le_iff.2 ?_) (adjoin.mono _ _ _ (Set.image_subset_range _ _))
      rintro _ ⟨x, rfl⟩
      have hx : x ∈ Submodule.span R (s : Set T) := hs ▸ Submodule.mem_top
      refine Submodule.span_induction (p := fun x _ ↦ ψ x ∈ adjoin K (ψ '' s)) ?_ ?_ ?_ ?_ hx
      · exact fun y hy ↦ subset_adjoin _ _ ⟨y, hy, rfl⟩
      · simp
      · intro a b _ _ ha hb
        rw [map_add]
        exact add_mem ha hb
      · intro r a _ ha
        rw [map_smul, algebra_compatible_smul K r]
        exact (adjoin K (ψ '' s)).smul_mem ha
    rw [this]
    refine finiteDimensional_adjoin fun y hy ↦ ?_
    exact (Algebra.IsIntegral.isIntegral (R := K) y)
  let M := normalClosure K L' Ω
  have hL'M : L' ≤ M := le_normalClosure L'
  exact ramificationIdx_comap_integralClosureMap_eq_one_of_normal ψ Q m M hL'M hI

/-- **Covers on which inertia acts trivially are unramified.** Let `T` be a Dedekind domain finite
over `R` with an `R`-algebra map to `Ω`, and `Q` a maximal ideal of the integral closure of `R`
in `Ω` over a maximal ideal `m` of `R` with perfect residue field. If the inertia group of `Q` in
`Gal(Ω / K)` fixes the image of every `R`-algebra map `T → Ω`, then every prime of `T` over `m` is
unramified over `R`. -/
theorem ramificationIdx_eq_one_of_forall_inertia {T : Type*} [CommRing T]
    [IsDedekindDomain T] [Algebra R T] [Module.Finite R T] [Module.IsTorsionFree R T]
    (ψ₀ : T →ₐ[R] Ω) (Q : Ideal (integralClosure R Ω)) [Q.IsMaximal] (m : Ideal R)
    [m.IsMaximal] [Q.LiesOver m] [PerfectField m.ResidueField]
    (hI : ∀ σ ∈ Q.inertia Gal(Ω/K), ∀ (ψ : T →ₐ[R] Ω) (x : T), σ (ψ x) = ψ x)
    (𝔭 : Ideal T) [𝔭.IsPrime] [𝔭.LiesOver m] : 𝔭.ramificationIdx R = 1 := by
  have : Algebra.IsIntegral R T := Algebra.IsIntegral.of_finite R T
  let B := integralClosure R Ω
  let φ₀ := integralClosureMap ψ₀
  let _ : Algebra T B := φ₀.toAlgebra
  have : IsScalarTower R T B := IsScalarTower.of_algebraMap_eq fun r ↦ Subtype.ext (by
    change algebraMap R Ω r = ψ₀ (algebraMap R T r)
    rw [ψ₀.commutes])
  have : Algebra.IsIntegral T B := Algebra.IsIntegral.tower_top R
  have hker : (⊥ : Ideal B).comap (algebraMap T B) ≤ 𝔭 := by
    intro x hx
    have hx' : ψ₀ x = 0 := congrArg Subtype.val hx
    have hRΩ : Function.Injective (algebraMap R Ω) := by
      rw [IsScalarTower.algebraMap_eq R K Ω]
      exact (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)
    rw [injective_of_isIntegral ψ₀ hRΩ (hx'.trans (map_zero ψ₀).symm)]
    exact 𝔭.zero_mem
  obtain ⟨Q', -, hQ', hQ'𝔭⟩ := Ideal.exists_ideal_over_prime_of_isIntegral 𝔭 ⊥ hker
  -- `Q'` is a conjugate `g • Q` of `Q`
  have hIC : IsIntegrallyClosedIn R K := inferInstance
  let _ : TopologicalSpace B := ⊥
  have : DiscreteTopology B := ⟨rfl⟩
  have := Algebra.continuousSMul_integralClosure R K Ω
  have := Algebra.isInvariant_integralClosure R K Ω
  have hunder : Q.under R = Q'.under R := by
    rw [← Ideal.over_def Q m, ← Ideal.under_under (B := T) Q', hQ'𝔭,
      ← Ideal.over_def 𝔭 m]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (G := Gal(Ω/K))
    Q Q' hunder
  let ψ : T →ₐ[R] Ω := ((g⁻¹ : Gal(Ω/K)).toAlgHom.restrictScalars R).comp ψ₀
  have hψ : Q.comap (integralClosureMap ψ) = 𝔭 := by
    rw [← hQ'𝔭, hg]
    ext x
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  rw [← hψ]
  exact ramificationIdx_comap_integralClosureMap_eq_one ψ Q m fun σ hσ x ↦ hI σ hσ ψ x

section Ring

/-- A fraction `a / s` of elements of an integrally closed domain `A`, embedded in a field `Ω`,
which is integral over `A` lies in `A`. -/
lemma IsIntegrallyClosed.exists_eq_of_mul_eq {A Ω : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Field Ω] [Algebra A Ω] (hφ : Function.Injective (algebraMap A Ω))
    {x : Ω} (hx : IsIntegral A x) {a s : A} (hs : s ≠ 0)
    (h : x * algebraMap A Ω s = algebraMap A Ω a) : ∃ b : A, algebraMap A Ω b = x := by
  let F := FractionRing A
  let φ : F →ₐ[A] Ω := IsFractionRing.liftAlgHom (K := F) (g := Algebra.ofId A Ω) hφ
  let y : F := IsLocalization.mk' F a ⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩
  have hy : φ y = x := by
    change IsFractionRing.lift (g := (Algebra.ofId A Ω : A →+* Ω)) hφ
      (IsLocalization.mk' F a ⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩) = x
    rw [IsFractionRing.lift_mk' (g := (Algebra.ofId A Ω : A →+* Ω)) hφ]
    change algebraMap A Ω a / algebraMap A Ω s = x
    rw [div_eq_iff ((map_ne_zero_iff _ hφ).2 hs)]
    exact h.symm
  have hyint : IsIntegral A y := by
    rw [← isIntegral_algHom_iff φ φ.toRingHom.injective, hy]
    exact hx
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 hyint
  refine ⟨b, ?_⟩
  rw [← hy, ← hb]
  exact (φ.commutes b).symm

end Ring

section Etale

variable (m : Ideal R) [m.IsMaximal] [PerfectField m.ResidueField]
  (Q : Ideal (integralClosure R Ω))
  [Q.IsMaximal] [Q.LiesOver m] (π : R) {R' : Type*} [CommRing R'] [Algebra R R']
  [IsLocalization.Away π R'] {A : Type*} [CommRing A] [IsDomain A] [Algebra R A]
  [Algebra R' A] [IsScalarTower R R' A] [Module.Finite R' A] [Algebra.Etale R' A]

include R' in
omit [IsDedekindDomain R] [IsFractionRing R K] [IsGalois K Ω] [IsDomain A] [Algebra.Etale R' A] in
/-- The integral closure of `R` in `A` localizes to `A` away from `π`. -/
lemma isLocalization_away_integralClosure :
    IsLocalization.Away (algebraMap R (integralClosure R A) π) A := by
  have hunit : IsUnit (algebraMap R A π) := by
    rw [IsScalarTower.algebraMap_apply R R' A]
    exact (IsLocalization.Away.algebraMap_isUnit π).map _
  have : Algebra.IsIntegral R' A := Algebra.IsIntegral.of_finite R' A
  refine ⟨?_, fun a ↦ ?_, fun {x y} h ↦ ⟨1, by simpa using Subtype.ext h⟩⟩
  · rintro ⟨_, n, rfl⟩
    rw [map_pow, ← IsScalarTower.algebraMap_apply]
    exact hunit.pow n
  · obtain ⟨⟨_, n, rfl⟩, h⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (Submonoid.powers π) (Rₘ := R') a (Algebra.IsIntegral.isIntegral a)
    refine ⟨(⟨_, h⟩, ⟨algebraMap R _ π ^ n, n, rfl⟩), ?_⟩
    change a * algebraMap _ A (algebraMap R _ π ^ n) = (π ^ n) • a
    rw [map_pow, ← IsScalarTower.algebraMap_apply, Algebra.smul_def, map_pow, mul_comm]

-- the elaboration of the localisation and integral closure instances is slow
include R' in
/-- **Covers on which inertia acts trivially extend.** Let `π ∈ R` vanish exactly at the maximal
ideal `m`, and `A` a finite étale `R[1/π]`-domain with an `R`-algebra map to `Ω`. If the inertia
group of `Q` fixes the images of all `R`-algebra maps `A → Ω`, then the integral closure of `R` in
`A` is finite étale over `R`. -/
theorem etale_integralClosure_of_forall_inertia (hπ : π ≠ 0)
    (hπm : ∀ p : Ideal R, p.IsPrime → π ∈ p → p = m) (ψ₀ : A →ₐ[R] Ω)
    (hI : ∀ σ ∈ Q.inertia Gal(Ω/K), ∀ (ψ : A →ₐ[R] Ω) (x : A), σ (ψ x) = ψ x) :
    Algebra.Etale R (integralClosure R A) ∧ Module.Finite R (integralClosure R A) := by
  set T := integralClosure R A
  have hRΩ : Function.Injective (algebraMap R Ω) := by
    rw [IsScalarTower.algebraMap_eq R K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)
  have hπ' : Submonoid.powers π ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hπ
  have : IsDomain R' := IsLocalization.isDomain_of_le_nonZeroDivisors R' hπ'
  have : IsDedekindDomain R' := IsLocalization.isDedekindDomain R hπ' R'
  have : IsDedekindDomain A := IsDedekindDomain.of_formallyUnramified R' A
  have : Algebra.IsIntegral R' A := Algebra.IsIntegral.of_finite R' A
  -- the elements of `R'` map into `K`
  have hR'K (ψ : A →ₐ[R] Ω) (r' : R') :
      ∃ k : K, algebraMap K Ω k = ψ (algebraMap R' A r') := by
    obtain ⟨⟨r, _, n, rfl⟩, hr⟩ := IsLocalization.surj (Submonoid.powers π) r'
    have hπn : algebraMap R K (π ^ n) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 (pow_ne_zero n hπ)
    refine ⟨algebraMap R K r / algebraMap R K (π ^ n), ?_⟩
    have h := congrArg (fun y ↦ ψ (algebraMap R' A y)) hr
    simp only [map_mul, ← IsScalarTower.algebraMap_apply, AlgHom.commutes] at h
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← h,
      mul_div_cancel_right₀]
    rw [IsScalarTower.algebraMap_apply R K Ω]
    exact (map_ne_zero_iff _ (algebraMap K Ω).injective).2 hπn
  -- every `R`-algebra map `A → Ω` is injective
  have hinj (ψ : A →ₐ[R] Ω) : Function.Injective ψ := by
    refine (injective_iff_map_eq_zero ψ).2 fun x hx ↦ ?_
    have hker : RingHom.ker ψ.toRingHom = ⊥ := by
      refine Ideal.eq_bot_of_under_eq_bot (R := R') ?_
      rw [Ideal.under_def, RingHom.comap_ker, eq_bot_iff]
      intro r' hr'
      obtain ⟨k, hk⟩ := hR'K ψ r'
      rw [RingHom.mem_ker] at hr'
      obtain ⟨⟨r, _, n, rfl⟩, hr⟩ := IsLocalization.surj (Submonoid.powers π) r'
      have h := congrArg (fun y ↦ ψ (algebraMap R' A y)) hr
      simp only [map_mul, ← IsScalarTower.algebraMap_apply, AlgHom.commutes] at h
      change ψ (algebraMap R' A r') = 0 at hr'
      rw [hr', zero_mul, eq_comm, map_eq_zero_iff _ hRΩ] at h
      rw [Ideal.mem_bot]
      have hu : IsUnit (algebraMap R R' (π ^ n)) :=
        IsLocalization.map_units R' (⟨π ^ n, n, rfl⟩ : Submonoid.powers π)
      rw [h, map_zero] at hr
      exact (hu.mul_left_eq_zero).1 hr
    have : x ∈ RingHom.ker ψ.toRingHom := hx
    rwa [hker, Ideal.mem_bot] at this
  -- the field `L'` generated by `ψ₀(A)`: its elements are fractions of elements of `ψ₀(A)`
  let L' : IntermediateField K Ω := adjoin K (Set.range ψ₀)
  have hfrac : ∀ x ∈ L', ∃ a b : A, b ≠ 0 ∧ x * ψ₀ b = ψ₀ a := by
    let S : IntermediateField K Ω :=
      { carrier := {x | ∃ a b : A, b ≠ 0 ∧ x * ψ₀ b = ψ₀ a}
        mul_mem' := by
          rintro x y ⟨a, b, hb, h⟩ ⟨c, d, hd, h'⟩
          exact ⟨a * c, b * d, mul_ne_zero hb hd, by
            rw [map_mul, map_mul, ← h, ← h']
            ring⟩
        add_mem' := by
          rintro x y ⟨a, b, hb, h⟩ ⟨c, d, hd, h'⟩
          exact ⟨a * d + b * c, b * d, mul_ne_zero hb hd, by
            rw [map_add, map_mul, map_mul, map_mul, ← h, ← h']
            ring⟩
        algebraMap_mem' := by
          intro k
          obtain ⟨r, t, ht, rfl⟩ := IsFractionRing.div_surjective (A := R) k
          refine ⟨algebraMap R A r, algebraMap R A t, ?_, ?_⟩
          · intro h0
            apply nonZeroDivisors.ne_zero ht
            apply hRΩ
            rw [map_zero, ← ψ₀.commutes, h0, map_zero]
          · rw [ψ₀.commutes, ψ₀.commutes, map_div₀, ← IsScalarTower.algebraMap_apply,
              ← IsScalarTower.algebraMap_apply, div_mul_cancel₀]
            exact (map_ne_zero_iff _ hRΩ).2 (nonZeroDivisors.ne_zero ht)
        inv_mem' := by
          rintro x ⟨a, b, hb, h⟩
          by_cases ha : a = 0
          · refine ⟨0, 1, one_ne_zero, ?_⟩
            rw [ha, map_zero, mul_eq_zero] at h
            rcases h with h | h
            · simp [h]
            · exact absurd ((map_eq_zero_iff _ (hinj ψ₀)).1 h) hb
          · refine ⟨b, a, ha, ?_⟩
            have hx : x ≠ 0 := by
              rintro rfl
              rw [zero_mul, eq_comm, map_eq_zero_iff _ (hinj ψ₀)] at h
              exact ha h
            rw [← h, ← mul_assoc, inv_mul_cancel₀ hx, one_mul] }
    have hle : L' ≤ S := adjoin_le_iff.2 fun _ ⟨a, ha⟩ ↦ ⟨a, 1, one_ne_zero, by simp [← ha]⟩
    exact fun x hx ↦ hle hx
  have : FiniteDimensional K L' := by
    obtain ⟨g, hg⟩ := Module.Finite.fg_top (R := R') (M := A)
    have hle : L' ≤ adjoin K (ψ₀ '' g) := by
      refine adjoin_le_iff.2 ?_
      rintro _ ⟨x, rfl⟩
      have hx : x ∈ Submodule.span R' (g : Set A) := hg ▸ Submodule.mem_top
      refine Submodule.span_induction (p := fun x _ ↦ ψ₀ x ∈ adjoin K (ψ₀ '' g)) ?_ ?_ ?_ ?_ hx
      · exact fun y hy ↦ subset_adjoin _ _ ⟨y, hy, rfl⟩
      · simp
      · intro a b _ _ ha hb
        rw [map_add]
        exact add_mem ha hb
      · intro r' a _ ha
        obtain ⟨k, hk⟩ := hR'K ψ₀ r'
        rw [Algebra.smul_def, map_mul, ← hk]
        exact mul_mem ((adjoin K (ψ₀ '' g)).algebraMap_mem k) ha
    have : FiniteDimensional K (adjoin K (ψ₀ '' g)) :=
      finiteDimensional_adjoin fun y _ ↦ Algebra.IsIntegral.isIntegral (R := K) y
    exact Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  have : Algebra.IsSeparable K L' := Algebra.isSeparable_tower_bot_of_isSeparable K L' Ω
  -- `T` is the ring of integers of `L'`
  let ψT : T →+* L' := (ψ₀.codRestrict (L'.toSubalgebra.restrictScalars R)
    (fun x ↦ subset_adjoin K _ ⟨x, rfl⟩)).toRingHom.comp T.val.toRingHom
  let _ : Algebra T L' := ψT.toAlgebra
  have : IsScalarTower R T L' := IsScalarTower.of_algebraMap_eq fun r ↦ Subtype.ext (by
    change algebraMap R Ω r = ψ₀ (algebraMap R A r)
    rw [ψ₀.commutes])
  have : IsIntegrallyClosed A := inferInstance
  have hIC : IsIntegralClosure T R L' := by
    refine ⟨fun x y h ↦ Subtype.ext (hinj ψ₀ (congrArg Subtype.val h)), fun {x} ↦ ⟨fun hx ↦ ?_, ?_⟩⟩
    · obtain ⟨a, b, hb, h⟩ := hfrac x x.2
      let _ : Algebra A Ω := ψ₀.toRingHom.toAlgebra
      have : IsScalarTower R A Ω := IsScalarTower.of_algebraMap_eq fun r ↦ (ψ₀.commutes r).symm
      have hxR : IsIntegral R (x : Ω) := by
        rw [← isIntegral_algHom_iff (L'.val.restrictScalars R) L'.val.injective] at hx
        exact hx
      obtain ⟨c, hc⟩ := IsIntegrallyClosed.exists_eq_of_mul_eq (hinj ψ₀) (hxR.tower_top) hb h
      have hcT : IsIntegral R c := by
        rw [← isIntegral_algHom_iff ψ₀ (hinj ψ₀)]
        change IsIntegral R (algebraMap A Ω c)
        rw [hc]
        exact hxR
      exact ⟨⟨c, hcT⟩, Subtype.ext hc⟩
    · rintro ⟨t, rfl⟩
      exact (Algebra.IsIntegral.isIntegral (R := R) t).map (IsScalarTower.toAlgHom R T L')
  have : IsDedekindDomain T := IsIntegralClosure.isDedekindDomain R K L' T
  have : Module.Finite R T := IsIntegralClosure.finite R K L' T
  -- `T` is flat and of finite presentation over `R`
  have hRT : Function.Injective (algebraMap R T) := fun x y h ↦ hRΩ (by
    have : ψ₀ (algebraMap T A (algebraMap R T x)) = ψ₀ (algebraMap T A (algebraMap R T y)) :=
      congrArg (fun t : T ↦ ψ₀ (algebraMap T A t)) h
    rwa [← IsScalarTower.algebraMap_apply R T A, ← IsScalarTower.algebraMap_apply R T A,
      ψ₀.commutes, ψ₀.commutes] at this)
  have : Module.IsTorsionFree R T :=
    Module.isTorsionFree_iff_faithfulSMul.2 ((faithfulSMul_iff_algebraMap_injective R T).2 hRT)
  have : Algebra.FinitePresentation R T := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hloc := isLocalization_away_integralClosure (R' := R') π (A := A)
  have : Algebra.FormallyUnramified R R' :=
    Algebra.FormallyUnramified.of_isLocalization (Submonoid.powers π)
  have : Algebra.FormallyUnramified R A := Algebra.FormallyUnramified.comp R R' A
  have hperf : PerfectField m.ResidueField := inferInstance
  -- `T` is unramified at every prime
  have hunr : Algebra.FormallyUnramified R T := by
    rw [Algebra.formallyUnramified_iff_forall]
    intro q
    by_cases hq : algebraMap R T π ∈ q.1
    · have hqm : q.1.under R = m := hπm _ (Ideal.IsPrime.under R q.1) hq
      have : q.1.LiesOver m := ⟨hqm.symm⟩
      have he := ramificationIdx_eq_one_of_forall_inertia (K := K)
        (ψ₀.comp (IsScalarTower.toAlgHom R T A)) Q m (fun σ hσ ψ x ↦ ?_) q.1
      · have : PerfectField (q.1.under R).ResidueField := hqm ▸ hperf
        exact Ideal.ramificationIdx_eq_one_iff.1 he
      · have hψu (y : Submonoid.powers (algebraMap R T π)) : IsUnit (ψ y) := by
          refine IsUnit.mk0 _ fun h0 ↦ ?_
          have := injective_of_isIntegral ψ hRΩ (h0.trans (map_zero ψ).symm)
          obtain ⟨_, n, rfl⟩ := y
          exact pow_ne_zero n (fun h ↦ hπ (hRT (h.trans (map_zero _).symm))) this
        let ψA : A →ₐ[R] Ω := IsLocalization.liftAlgHom (M := Submonoid.powers (algebraMap R T π))
          (f := ψ) hψu
        have hψA (t : T) : ψA (algebraMap T A t) = ψ t := IsLocalization.lift_eq _ _
        rw [← hψA]
        exact hI σ hσ ψA _
    · have hbo : q ∈ PrimeSpectrum.basicOpen (algebraMap R T π) := hq
      have e : Localization.Away (algebraMap R T π) ≃ₐ[T] A :=
        IsLocalization.algEquiv (Submonoid.powers (algebraMap R T π)) _ _
      have : Algebra.FormallyUnramified R (Localization.Away (algebraMap R T π)) :=
        Algebra.FormallyUnramified.of_equiv (e.symm.restrictScalars R)
      exact (Algebra.basicOpen_subset_unramifiedLocus_iff.2 this) hbo
  exact ⟨Algebra.Etale.of_formallyUnramified_of_flat, inferInstance⟩
end Etale

end Ideal

end SeparableClosure
