/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# The affine nonvanishing locus of a section of an invertible module

Source: Stacks Project, Properties, Lemma 01PV (`properties-lemma-affine-cap-s-open`),
algebra argument in the proof (blueprint: lem-sc-affine-cap-section-open-algebra).
-/

@[expose] public section

universe u v

open scoped Pointwise

namespace AlgebraicGeometry

-- Construct the localization comparison and its inverse on a trivializing chart.
private theorem section_quotient_localization (R : Type u) [CommRing R]
    (N : Type v) [AddCommGroup N] [Module R N] (s : N) (f : R)
    (e : Localization.Away f ≃ₗ[Localization.Away f] LocalizedModule.Away f N) :
    let I := Ideal.span {SymmetricAlgebra.ι R N s - 1}
    let B := SymmetricAlgebra R N ⧸ I
    let S := Localization.Away f
    let Q := Localization.Away (algebraMap R B f)
    letI : Algebra S Q := (Localization.awayMap (algebraMap R B) f).toAlgebra
    IsLocalization.Away
      (e.symm (LocalizedModule.mkLinearMap (Submonoid.powers f) N s)) Q := by
  let I := Ideal.span {SymmetricAlgebra.ι R N s - 1}
  let B := SymmetricAlgebra R N ⧸ I
  let S := Localization.Away f
  let Q := Localization.Away (algebraMap R B f)
  let ρ : S →+* Q := Localization.awayMap (algebraMap R B) f
  let : Algebra S Q := ρ.toAlgebra
  have : IsScalarTower R S Q := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R Q r = ρ (algebraMap R S r)
    dsimp [ρ, Localization.awayMap, IsLocalization.Away.map]
    rw [IsLocalization.map_eq, IsScalarTower.algebraMap_apply R B Q]
  let j : N →ₗ[R] Q := (Algebra.linearMap B Q).restrictScalars R |>.comp
    ((Ideal.Quotient.mkₐ R I).toLinearMap.comp (SymmetricAlgebra.ι R N))
  have hj : j s = 1 := by
    have hs : Ideal.Quotient.mk I (SymmetricAlgebra.ι R N s) = 1 := by
      rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      exact Ideal.subset_span (Set.mem_singleton _)
    change algebraMap B Q (Ideal.Quotient.mk I (SymmetricAlgebra.ι R N s)) = 1
    rw [hs, map_one]
  have : IsLocalizedModule (Submonoid.powers f) (LinearMap.id : Q →ₗ[R] Q) :=
    isLocalizedModule_id (Submonoid.powers f) Q S
  let hunit := IsLocalizedModule.map_units (S := Submonoid.powers f)
    (LinearMap.id : Q →ₗ[R] Q)
  let j' : LocalizedModule.Away f N →ₗ[S] Q :=
    (LocalizedModule.lift (Submonoid.powers f) j hunit).extendScalarsOfIsLocalization
      (Submonoid.powers f) S
  have hj' (n : N) : j' (LocalizedModule.mkLinearMap (Submonoid.powers f) N n) = j n := by
    exact LocalizedModule.lift_mk_one (Submonoid.powers f) j hunit n
  let a := e.symm (LocalizedModule.mkLinearMap (Submonoid.powers f) N s)
  let b := j' (e 1)
  have hab : algebraMap S Q a * b = 1 := by
    rw [← Algebra.smul_def, ← map_smul, ← e.map_smul, smul_eq_mul, mul_one,
      e.apply_symm_apply, hj', hj]
  have hau : IsUnit (algebraMap S Q a) := (isUnit_iff_exists_inv).mpr ⟨b, hab⟩
  let T := Localization.Away a
  let ψ : T →+* Q := IsLocalization.Away.lift a hau
  let dS : N →ₗ[R] S := e.symm.toLinearMap.restrictScalars R |>.comp
    (LocalizedModule.mkLinearMap (Submonoid.powers f) N)
  let d : N →ₗ[R] T := (IsLocalization.Away.invSelf a : T) •
    ((Algebra.linearMap S T).restrictScalars R |>.comp dS)
  have hd : d s = 1 := by
    change IsLocalization.Away.invSelf a * algebraMap S T a = 1
    rw [mul_comm]
    exact IsLocalization.Away.mul_invSelf a
  let α := SymmetricAlgebra.lift d
  have hα : I ≤ RingHom.ker α.toRingHom := by
    apply Ideal.span_le.mpr
    rintro x (rfl : x = _)
    change α (SymmetricAlgebra.ι R N s - 1) = 0
    simp [α, hd]
  let β : B →ₐ[R] T := Ideal.Quotient.liftₐ I α (fun x hx ↦ hα hx)
  have hβ : IsUnit (β (algebraMap R B f)) := by
    rw [β.commutes, IsScalarTower.algebraMap_apply R S T]
    exact (IsLocalization.Away.algebraMap_isUnit (S := S) f).map (algebraMap S T)
  let φ : Q →+* T := IsLocalization.Away.lift (g := β.toRingHom)
    (algebraMap R B f) hβ
  have hφ : φ.comp ρ = algebraMap S T := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext r
    change φ (ρ (algebraMap R S r)) = algebraMap S T (algebraMap R S r)
    rw [show ρ (algebraMap R S r) = algebraMap B Q (algebraMap R B r) from
      IsLocalization.map_eq _ r]
    rw [show φ (algebraMap B Q (algebraMap R B r)) = β (algebraMap R B r) from
      IsLocalization.Away.lift_eq _ hβ _, β.commutes]
    exact IsScalarTower.algebraMap_apply R S T r
  have hψ (x : S) : ψ (algebraMap S T x) = ρ x :=
    IsLocalization.Away.lift_eq a hau x
  have hψinv : ψ (IsLocalization.Away.invSelf a : T) = b := by
    apply hau.mul_right_inj.mp
    rw [hab]
    change ρ a * ψ (IsLocalization.Away.invSelf a : T) = 1
    rw [← hψ a, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  have hright : φ.comp ψ = RingHom.id T := by
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    ext x
    change φ (ψ (algebraMap S T x)) = algebraMap S T x
    rw [hψ]
    exact DFunLike.congr_fun hφ x
  let ψA : T →ₐ[R] Q := {
    toRingHom := ψ
    commutes' := by
      intro r
      change ψ (algebraMap R T r) = algebraMap R Q r
      rw [IsScalarTower.algebraMap_apply R S T, hψ]
      exact (IsScalarTower.algebraMap_apply R S Q r).symm }
  let γ := (IsScalarTower.toAlgHom R B Q).comp (Ideal.Quotient.mkₐ R I)
  have hgen (n : N) : j n = algebraMap S Q (dS n) * b := by
    rw [← hj' n]
    change j' (LocalizedModule.mkLinearMap (Submonoid.powers f) N n) =
      algebraMap S Q (e.symm (LocalizedModule.mkLinearMap (Submonoid.powers f) N n)) *
        j' (e 1)
    rw [← Algebra.smul_def, ← map_smul, ← e.map_smul, smul_eq_mul, mul_one,
      e.apply_symm_apply]
  have hαψ : ψA.comp α = γ := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro n
    change ψ (α (SymmetricAlgebra.ι R N n)) = j n
    rw [SymmetricAlgebra.lift_ι_apply]
    change ψ ((IsLocalization.Away.invSelf a : T) * algebraMap S T (dS n)) = j n
    rw [map_mul, hψinv, hψ]
    exact (mul_comm _ _).trans (hgen n).symm
  have hleft : ψ.comp φ = RingHom.id Q := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R B f))
    apply RingHom.ext
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change ψ (φ (algebraMap B Q (Ideal.Quotient.mk I y))) = _
    rw [show φ (algebraMap B Q (Ideal.Quotient.mk I y)) =
        β (Ideal.Quotient.mk I y) from IsLocalization.Away.lift_eq _ hβ _]
    change ψA (α y) = γ y
    exact DFunLike.congr_fun hαψ y
  let φS : Q →ₐ[S] T := {
    toRingHom := φ
    commutes' := fun x ↦ DFunLike.congr_fun hφ x }
  let ψS : T →ₐ[S] Q := { toRingHom := ψ, commutes' := hψ }
  let E := AlgEquiv.ofAlgHom φS ψS
    (by apply AlgHom.ext; intro x; exact DFunLike.congr_fun hright x)
    (by apply AlgHom.ext; intro x; exact DFunLike.congr_fun hleft x)
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers a) E.symm
-- Transport the algebra calculation to the actual restricted spectrum morphism.
private theorem affine_cap_section_trivializing_chart (R : Type u) [CommRing R]
    (N : Type v) [AddCommGroup N] [Module R N] (s : N) (f : R)
    (e : Localization.Away f ≃ₗ[Localization.Away f] LocalizedModule.Away f N) :
    IsOpenImmersion ((Spec.map (CommRingCat.ofHom
      ((algebraMap R (SymmetricAlgebra R N ⧸ Ideal.span {SymmetricAlgebra.ι R N s - 1})).comp
        (ULift.ringEquiv : ULift.{v} R ≃+* R).toRingHom))) ∣_
          PrimeSpectrum.basicOpen (ULift.up f))  := by
  let I := Ideal.span {SymmetricAlgebra.ι R N s - 1}
  let B := SymmetricAlgebra R N ⧸ I
  let S := Localization.Away f
  let Q := Localization.Away (algebraMap R B f)
  let ρ : S →+* Q := Localization.awayMap (algebraMap R B) f
  let : Algebra S Q := ρ.toAlgebra
  let a := e.symm (LocalizedModule.mkLinearMap (Submonoid.powers f) N s)
  have : IsLocalization.Away a Q := section_quotient_localization R N s f e
  let R' := ULift.{v} R
  let r : R' := ULift.up f
  let S' := Localization.Away r
  let g : R' →+* B := (algebraMap R B).comp ULift.ringEquiv.toRingHom
  let l : S' →+* Q := Localization.awayMap g r
  let : Algebra S' Q := l.toAlgebra
  let δ : S' ≃+* S := IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers r)
    (T := Submonoid.powers f) S' S
    (ULift.ringEquiv : R' ≃+* R) (by rw [Submonoid.map_powers]; rfl)
  have : IsLocalization.Away (g r) Q := by
    change IsLocalization.Away (algebraMap R B f) Q
    infer_instance
  have hδ : ρ.comp δ.toRingHom = l := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    apply RingHom.ext
    intro x
    change ρ (δ (algebraMap R' S' x)) = l (algebraMap R' S' x)
    rw [show δ (algebraMap R' S' x) = algebraMap R S x.down from
      IsLocalization.ringEquivOfRingEquiv_eq _ x]
    rw [show ρ (algebraMap R S x.down) = algebraMap B Q (algebraMap R B x.down) from
      IsLocalization.map_eq _ x.down]
    rw [show l (algebraMap R' S' x) = algebraMap B Q (g x) from
      IsLocalization.map_eq _ x]
    rfl
  have : IsLocalization.Away (δ.symm a) Q :=
    IsLocalization.of_ringEquiv_left (M₁ := Submonoid.powers a)
      (M₂ := Submonoid.powers (δ.symm a)) δ
      (by simp [Submonoid.map_powers]) (fun x ↦ (DFunLike.congr_fun hδ x).symm)
  have hlocal : IsOpenImmersion (Spec.map (CommRingCat.ofHom l)) :=
    IsOpenImmersion.of_isLocalization (δ.symm a)
  exact (CategoryTheory.MorphismProperty.arrow_mk_iso_iff (@IsOpenImmersion)
    (SpecMapRestrictBasicOpenIso (CommRingCat.ofHom g) r)).mpr hlocal


-- The quotient relation excludes primes at which the section vanishes.
private theorem section_not_mem_comap_smul (R : Type u) [CommRing R]
    (N : Type v) [AddCommGroup N] [Module R N] (s : N)
    (q : PrimeSpectrum (SymmetricAlgebra R N ⧸
      Ideal.span {SymmetricAlgebra.ι R N s - 1})) :
    s ∉ (q.asIdeal.comap (algebraMap R _)) • (⊤ : Submodule R N) := by
  let I := Ideal.span {SymmetricAlgebra.ι R N s - 1}
  let B := SymmetricAlgebra R N ⧸ I
  let j : N →ₗ[R] B := (Ideal.Quotient.mkₐ R I).toLinearMap.comp
    (SymmetricAlgebra.ι R N)
  have hj : j s = 1 := by
    change Ideal.Quotient.mk I (SymmetricAlgebra.ι R N s) = 1
    rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hle : (q.asIdeal.comap (algebraMap R B)) • (⊤ : Submodule R N) ≤
      (q.asIdeal.restrictScalars R).comap j := by
    apply Submodule.smul_le.mpr
    intro r hr n _
    change j (r • n) ∈ q.asIdeal
    rw [map_smul, Algebra.smul_def]
    exact q.asIdeal.mul_mem_right _ hr
  intro hs
  have h := hle hs
  change j s ∈ q.asIdeal at h
  rw [hj] at h
  exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem q.asIdeal h isUnit_one)

-- A projective splitting detects nonvanishing by a coordinate functional.
private theorem exists_dual_not_mem (R : Type u) [CommRing R]
    (N : Type v) [AddCommGroup N] [Module R N] [Module.Projective R N]
    (s : N) (p : Ideal R) (hs : s ∉ p • (⊤ : Submodule R N)) :
    ∃ l : N →ₗ[R] R, l s ∉ p := by
  classical
  obtain ⟨t, ht⟩ := Module.Projective.out (R := R) (P := N)
  by_contra h
  push Not at h
  apply hs
  rw [← ht s, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro n _
  exact Submodule.smul_mem_smul (h ((Finsupp.lapply n).comp t)) (Submodule.mem_top)

-- Normalize that functional in the residue field and take the evaluation kernel.
private theorem section_mem_range (R : Type u) [CommRing R]
    (N : Type v) [AddCommGroup N] [Module R N] [Module.Projective R N]
    (s : N) (p : PrimeSpectrum R) (hs : s ∉ p.asIdeal • (⊤ : Submodule R N)) :
    p ∈ Set.range (PrimeSpectrum.comap
      (algebraMap R (SymmetricAlgebra R N ⧸ Ideal.span {SymmetricAlgebra.ι R N s - 1}))) := by
  obtain ⟨l, hl⟩ := exists_dual_not_mem R N s p.asIdeal hs
  let k := p.asIdeal.ResidueField
  let c := algebraMap R k (l s)
  have hc : c ≠ 0 := by simpa [c, k] using hl
  let d : N →ₗ[R] k := c⁻¹ • ((Algebra.linearMap R k).comp l)
  have hd : d s = 1 := by
    change c⁻¹ * c = 1
    exact inv_mul_cancel₀ hc
  let a : SymmetricAlgebra R N →ₐ[R] k := SymmetricAlgebra.lift d
  let I := Ideal.span {SymmetricAlgebra.ι R N s - 1}
  have ha : I ≤ RingHom.ker a.toRingHom := by
    apply Ideal.span_le.mpr
    rintro x (rfl : x = _)
    change a (SymmetricAlgebra.ι R N s - 1) = 0
    simp [a, hd]
  let b : (SymmetricAlgebra R N ⧸ I) →ₐ[R] k :=
    Ideal.Quotient.liftₐ I a (fun x hx ↦ ha hx)
  let q : PrimeSpectrum (SymmetricAlgebra R N ⧸ I) := ⟨RingHom.ker b.toRingHom,
    RingHom.ker_isPrime b.toRingHom⟩
  refine ⟨q, ?_⟩
  apply PrimeSpectrum.ext
  ext r
  change b (algebraMap R _ r) = 0 ↔ r ∈ p.asIdeal
  rw [b.commutes]
  exact Ideal.algebraMap_residueField_eq_zero

/-- Source: Stacks Project, Lemma 01PV, algebra argument in the proof
(blueprint: lem-sc-affine-cap-section-open-algebra).
For an invertible module `N`, the spectrum of `Sym_R(N)/(ι(s)-1)` identifies with the open
locus of primes `p` where `s ∉ pN`. The base ring is lifted to the common universe
by `ULift`; primes are transported along its canonical ring equivalence.

Proof: (1) Finite projectivity gives finite presentation and freeness at each prime.
Spread this freeness to a principal neighbourhood, preserving rank one, and choose a
linear equivalence `R_f ≃ N_f` there.
(2) Write `a` for the coefficient of `s/1`. The linear map from `N` to `B_f` sends `s`
to one, so its value `b` on the basis vector satisfies `a * b = 1`. This constructs
`(R_f)_a → B_f`. Conversely the functional `n ↦ a⁻¹ * e⁻¹(n/1)` gives a map
`B_f → (R_f)_a` by the symmetric-algebra, quotient, and localization universal properties.
Those same universal properties show that the maps are inverse.
(3) Transport this principal-localization description to the restriction of the spectrum
map using `SpecMapRestrictBasicOpenIso`. The Zariski-local criterion for open immersions
then proves the assertion globally.
(4) The quotient relation excludes primes where `s ∈ pN`. Conversely, a projective
splitting gives a coordinate functional nonzero on `s` modulo any prime with `s ∉ pN`.
Normalize it in the residue field to send `s` to one. The induced map from `B` to that
field has prime kernel contracting to `p`, proving the reverse image inclusion. -/
theorem affine_cap_section_open_algebra (R : Type u) [CommRing R]
    (N : Type v) [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    (_hN : ∀ p : PrimeSpectrum R, Module.rankAtStalk N p = 1) (s : N) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      ((algebraMap R (SymmetricAlgebra R N ⧸ Ideal.span {SymmetricAlgebra.ι R N s - 1})).comp
        (ULift.ringEquiv : ULift.{v} R ≃+* R).toRingHom))) ∧
    Set.range (Spec.map (CommRingCat.ofHom
      ((algebraMap R (SymmetricAlgebra R N ⧸ Ideal.span {SymmetricAlgebra.ι R N s - 1})).comp
        (ULift.ringEquiv : ULift.{v} R ≃+* R).toRingHom))) =
      {p : PrimeSpectrum (ULift.{v} R) |
        s ∉ (p.asIdeal.comap ULift.ringEquiv.symm.toRingHom) • (⊤ : Submodule R N)} := by
  let B := SymmetricAlgebra R N ⧸ Ideal.span {SymmetricAlgebra.ι R N s - 1}
  let φ := Spec.map (CommRingCat.ofHom
    ((algebraMap R B).comp (ULift.ringEquiv : ULift.{v} R ≃+* R).toRingHom))
  have hcharts (p : PrimeSpectrum (ULift.{v} R)) :
      ∃ f : R, f ∉ p.asIdeal.comap ULift.ringEquiv.symm.toRingHom ∧
        Nonempty (Localization.Away f ≃ₗ[Localization.Away f]
          LocalizedModule.Away f N) := by
    let q := p.comap ULift.ringEquiv.symm.toRingHom
    have : Module.FinitePresentation R N := Module.finitePresentation_of_projective R N
    have : Module.Free (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl N) := Module.free_of_flat_of_isLocalRing
    obtain ⟨f, hf, hfree, hrank⟩ :=
      Module.FinitePresentation.exists_free_localizedModule_powers q.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap q.asIdeal.primeCompl N)
        (Localization.AtPrime q.asIdeal)
    have : Module.Free (Localization.Away f) (LocalizedModule.Away f N) := hfree
    have : Nontrivial (Localization.Away f) :=
      (IsLocalization.map (M := Submonoid.powers f) (T := q.asIdeal.primeCompl)
        (Localization.AtPrime q.asIdeal) (RingHom.id R)
        (Submonoid.powers_le.mpr hf)).domain_nontrivial
    refine ⟨f, hf, Module.nonempty_linearEquiv_of_finrank_eq_one ?_⟩
    exact hrank.trans (_hN q)
  have hlocal (p : PrimeSpectrum (ULift.{v} R)) :
      ∃ U : (Spec (.of (ULift.{v} R))).Opens, p ∈ U ∧ IsOpenImmersion (φ ∣_ U) := by
    obtain ⟨f, hf, ⟨e⟩⟩ := hcharts p
    exact ⟨PrimeSpectrum.basicOpen (ULift.up f), hf,
      affine_cap_section_trivializing_chart R N s f e⟩
  refine ⟨?_, ?_⟩
  · exact IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
      (P := @IsOpenImmersion) hlocal
  · change Set.range φ = _
    let g := (algebraMap R B).comp (ULift.ringEquiv : ULift.{v} R ≃+* R).toRingHom
    have hg : g.comp ULift.ringEquiv.symm.toRingHom = algebraMap R B := by
      ext r
      rfl
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      change s ∉ ((q.asIdeal.comap g).comap ULift.ringEquiv.symm.toRingHom) •
        (⊤ : Submodule R N)
      rw [Ideal.comap_comap, hg]
      exact section_not_mem_comap_smul R N s q
    · intro hp
      obtain ⟨q, hq⟩ := section_mem_range R N s
        (p.comap (ULift.ringEquiv : ULift.{v} R ≃+* R).symm.toRingHom) hp
      refine ⟨q, ?_⟩
      apply (PrimeSpectrum.comapEquiv (ULift.ringEquiv : ULift.{v} R ≃+* R)).injective
      change (q.comap g).comap ULift.ringEquiv.symm.toRingHom =
        p.comap ULift.ringEquiv.symm.toRingHom
      rw [← PrimeSpectrum.comap_comp_apply, hg]
      exact hq

end AlgebraicGeometry
