import Mathlib.RingTheory.Smooth.Local
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-! # Smoothness from lifting along elementary Artinian surjections -/

universe u

open IsLocalRing TensorProduct

noncomputable section

namespace Langlands.RingTheory.ArtinianLifting

/-- A proper quotient of a local ring is local. -/
lemma quotient_isLocalRing {R : Type u} [CommRing R] [IsLocalRing R] {J : Ideal R}
    (hJ : J ≠ ⊤) : IsLocalRing (R ⧸ J) := by
  have : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective

/-- A proper quotient of a noetherian local ring by an ideal containing a power of
the maximal ideal is Artinian. -/
lemma quotient_isArtinianRing {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {J : Ideal R} (hJ : J ≠ ⊤) {N : ℕ} (hN : maximalIdeal R ^ N ≤ J) :
    IsArtinianRing (R ⧸ J) := by
  have := quotient_isLocalRing hJ
  have : IsNoetherianRing (R ⧸ J) :=
    isNoetherianRing_of_surjective R _ (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  apply (isArtinianRing_iff_isNilpotent_maximalIdeal _).mpr
  refine ⟨N, ?_⟩
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective, ← Ideal.map_pow]
  exact Ideal.map_mk_eq_bot_of_le hN

section Core

variable {C P T : Type u} [CommRing C] [CommRing P] [CommRing T] [Algebra C P] [Algebra C T]
  [Algebra P T] [IsScalarTower C P T] [IsLocalRing P] [IsLocalRing T]

/-- The kernel of a map to a local ring lies in the maximal ideal. -/
lemma ker_le_maximalIdeal : RingHom.ker (algebraMap P T) ≤ maximalIdeal P :=
  le_maximalIdeal (RingHom.ker_ne_top _)

variable (hρ : Function.Surjective (algebraMap P T))
include hρ

/-- A surjection of local rings kills the maximal ideal in the residue field. -/
lemma algebraMap_residueField_eq_zero {a : P} (ha : a ∈ maximalIdeal P) :
    algebraMap P (ResidueField T) a = 0 := by
  have : IsLocalHom (algebraMap P T) := IsLocalHom.of_surjective _ hρ
  rw [IsScalarTower.algebraMap_apply P T (ResidueField T), ResidueField.algebraMap_eq,
    residue_eq_zero_iff]
  exact map_nonunit (algebraMap P T) a ha

/-- Elements of `m * I` vanish after tensoring with the residue field. -/
lemma tmul_eq_zero_of_mem_mul {x : P}
    (hx : x ∈ maximalIdeal P * RingHom.ker (algebraMap P T)) :
    ∃ h : x ∈ RingHom.ker (algebraMap P T),
      (1 : ResidueField T) ⊗ₜ[P] (⟨x, h⟩ : RingHom.ker (algebraMap P T)) = 0 := by
  refine Submodule.mul_induction_on hx (fun a ha b hb ↦ ?_) (fun x y hx hy ↦ ?_)
  · refine ⟨Ideal.mul_mem_left _ a hb, ?_⟩
    have : (⟨a * b, Ideal.mul_mem_left _ a hb⟩ : RingHom.ker (algebraMap P T)) =
        a • ⟨b, hb⟩ := rfl
    rw [this, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
      algebraMap_residueField_eq_zero hρ ha, TensorProduct.zero_tmul]
  · obtain ⟨hx, ex⟩ := hx
    obtain ⟨hy, ey⟩ := hy
    refine ⟨add_mem hx hy, ?_⟩
    have : (⟨x + y, add_mem hx hy⟩ : RingHom.ker (algebraMap P T)) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [this, TensorProduct.tmul_add, ex, ey, add_zero]

end Core


section Derivation

variable {C P T : Type u} [CommRing C] [CommRing P] [CommRing T] [Algebra C P] [Algebra C T]
  [Algebra P T] [IsScalarTower C P T] [IsLocalRing P] [IsLocalRing T]
  (hρ : Function.Surjective (algebraMap P T)) {N : ℕ}
  (hN : maximalIdeal P ^ N ⊓ RingHom.ker (algebraMap P T) ≤
    maximalIdeal P * RingHom.ker (algebraMap P T))

/-- The ideal `m * I + m ^ N` defining the nonsplit test extension. -/
abbrev testIdeal (P T : Type u) [CommRing P] [CommRing T] [Algebra P T] [IsLocalRing P]
    (N : ℕ) : Ideal P :=
  maximalIdeal P * RingHom.ker (algebraMap P T) ⊔ maximalIdeal P ^ N

/-- The ideal `I + m ^ N` defining the reduced test. -/
abbrev baseIdeal (P T : Type u) [CommRing P] [CommRing T] [Algebra P T] [IsLocalRing P]
    (N : ℕ) : Ideal P :=
  RingHom.ker (algebraMap P T) ⊔ maximalIdeal P ^ N

omit [IsLocalRing T] in
lemma testIdeal_le_baseIdeal : testIdeal P T N ≤ baseIdeal P T N :=
  sup_le_sup_right Ideal.mul_le_right _

omit [IsLocalRing T] in
include hN in
lemma testIdeal_inf_le :
    testIdeal P T N ⊓ RingHom.ker (algebraMap P T) ≤
      maximalIdeal P * RingHom.ker (algebraMap P T) := by
  dsimp only [testIdeal]
  rw [sup_inf_assoc_of_le _ Ideal.mul_le_right]
  exact sup_le le_rfl hN

include hρ hN in
/-- Elements of `I` with the same image in the test ring have the same residue tensor. -/
lemma tmul_eq_of_mk_eq (j j' : RingHom.ker (algebraMap P T))
    (h : Ideal.Quotient.mk (testIdeal P T N) (j : P) =
      Ideal.Quotient.mk (testIdeal P T N) (j' : P)) :
    (1 : ResidueField T) ⊗ₜ[P] j = (1 : ResidueField T) ⊗ₜ[P] j' := by
  have hmem : (j : P) - j' ∈ testIdeal P T N ⊓ RingHom.ker (algebraMap P T) :=
    ⟨Ideal.Quotient.eq.mp h, sub_mem j.2 j'.2⟩
  obtain ⟨h', e⟩ := tmul_eq_zero_of_mem_mul hρ (testIdeal_inf_le hN hmem)
  have : (⟨(j : P) - j', h'⟩ : RingHom.ker (algebraMap P T)) = j - j' := rfl
  rw [this, TensorProduct.tmul_sub, sub_eq_zero] at e
  exact e

variable (σ : P →ₐ[C] P ⧸ testIdeal P T N)
  (hσ : ∀ p, Ideal.Quotient.factor (testIdeal_le_baseIdeal (P := P) (T := T) (N := N)) (σ p) =
    Ideal.Quotient.mk (baseIdeal P T N) p)

omit [Algebra C T] [IsScalarTower C P T] [IsLocalRing T] in
include hσ in
/-- The difference of the two maps to the test ring comes from `I`. -/
lemma exists_rep (p : P) :
    ∃ j : RingHom.ker (algebraMap P T),
      Ideal.Quotient.mk (testIdeal P T N) (j : P) = σ p - Ideal.Quotient.mk _ p := by
  have hker : σ p - Ideal.Quotient.mk _ p ∈
      RingHom.ker (Ideal.Quotient.factor (testIdeal_le_baseIdeal (P := P) (T := T) (N := N))) := by
    rw [RingHom.mem_ker, map_sub, hσ, Ideal.Quotient.factor_mk, sub_self]
  rw [Ideal.Quotient.factor_ker, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
    at hker
  obtain ⟨y, hy, hyp⟩ := hker
  obtain ⟨j, hj, t, ht, rfl⟩ := Submodule.mem_sup.mp hy
  refine ⟨⟨j, hj⟩, ?_⟩
  rw [← hyp, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr (le_sup_right (a := maximalIdeal P *
    RingHom.ker (algebraMap P T)) ht), add_zero]

/-- A chosen representative in `I` of the difference at `p`. -/
def rep (p : P) : RingHom.ker (algebraMap P T) :=
  (exists_rep σ hσ p).choose

omit [Algebra C T] [IsScalarTower C P T] [IsLocalRing T] in
lemma mk_rep (p : P) :
    Ideal.Quotient.mk (testIdeal P T N) (rep σ hσ p : P) = σ p - Ideal.Quotient.mk _ p :=
  (exists_rep σ hσ p).choose_spec

variable (hσI : ∀ j ∈ RingHom.ker (algebraMap P T), σ j = 0)

/-- The derivation `σ - mk`, with values in `I ⊗ κ`. -/
def delta : Derivation C P (ResidueField T ⊗[P] RingHom.ker (algebraMap P T)) where
  toFun p := (1 : ResidueField T) ⊗ₜ[P] rep σ hσ p
  map_add' p p' := by
    rw [← TensorProduct.tmul_add]
    refine tmul_eq_of_mk_eq hρ hN _ _ ?_
    rw [Submodule.coe_add, map_add, mk_rep, mk_rep, mk_rep, map_add, map_add]
    ring
  map_smul' c p := by
    rw [RingHom.id_apply, ← TensorProduct.tmul_smul]
    refine tmul_eq_of_mk_eq hρ hN _ _ ?_
    have hmk : ∀ x : P, Ideal.Quotient.mk (testIdeal P T N) (c • x) =
        c • Ideal.Quotient.mk (testIdeal P T N) x := fun x ↦ by
      rw [← Ideal.Quotient.mkₐ_eq_mk C, map_smul]
    rw [Submodule.coe_smul_of_tower, hmk, mk_rep, mk_rep, map_smul, hmk, smul_sub]
  map_one_eq_zero' := by
    change (1 : ResidueField T) ⊗ₜ[P] rep σ hσ 1 = 0
    rw [← TensorProduct.tmul_zero (R := P) (RingHom.ker (algebraMap P T)) (1 : ResidueField T)]
    refine tmul_eq_of_mk_eq hρ hN _ _ ?_
    rw [mk_rep, map_one, map_one, sub_self, ZeroMemClass.coe_zero, map_zero]
  leibniz' p p' := by
    change (1 : ResidueField T) ⊗ₜ[P] rep σ hσ (p * p') =
      p • ((1 : ResidueField T) ⊗ₜ[P] rep σ hσ p') + p' • ((1 : ResidueField T) ⊗ₜ[P] rep σ hσ p)
    rw [← TensorProduct.tmul_smul, ← TensorProduct.tmul_smul, ← TensorProduct.tmul_add]
    refine tmul_eq_of_mk_eq hρ hN _ _ ?_
    have h0 : Ideal.Quotient.mk (testIdeal P T N) ((rep σ hσ p : P) * rep σ hσ p') = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (le_sup_left (b := maximalIdeal P ^ N)
        (Ideal.mul_mem_mul (ker_le_maximalIdeal (rep σ hσ p).2) (rep σ hσ p').2))
    rw [map_mul] at h0
    rw [Submodule.coe_add, Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower, smul_eq_mul,
      smul_eq_mul, map_add, map_mul, map_mul, mk_rep σ hσ (p * p'), mk_rep σ hσ p,
      mk_rep σ hσ p', map_mul, map_mul]
    rw [mk_rep σ hσ p, mk_rep σ hσ p'] at h0
    linear_combination h0

include hσI in
/-- On `I` the derivation is minus the residue tensor. -/
lemma delta_apply_of_mem {j : P} (hj : j ∈ RingHom.ker (algebraMap P T)) :
    delta hρ hN σ hσ j = -((1 : ResidueField T) ⊗ₜ[P] (⟨j, hj⟩ : RingHom.ker (algebraMap P T))) := by
  change (1 : ResidueField T) ⊗ₜ[P] rep σ hσ j = _
  rw [← TensorProduct.tmul_neg]
  refine tmul_eq_of_mk_eq hρ hN _ _ ?_
  rw [mk_rep, hσI j hj, zero_sub, NegMemClass.coe_neg, map_neg]

include hρ hN hσ hσI in
/-- The base-changed cotangent complex is injective: it has a left inverse built
from the derivation. -/
theorem injective_cotangentComplexBaseChange :
    Function.Injective
      (KaehlerDifferential.cotangentComplexBaseChange C T P (ResidueField T)) := by
  let G := ((delta hρ hN σ hσ).liftKaehlerDifferential).liftBaseChange (ResidueField T)
  have hG : ∀ z, G (KaehlerDifferential.cotangentComplexBaseChange C T P (ResidueField T) z) =
      -z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      rw [KaehlerDifferential.cotangentComplexBaseChange_tmul, map_smul,
        KaehlerDifferential.kerToTensor_apply, LinearMap.liftBaseChange_tmul, one_smul,
        Derivation.liftKaehlerDifferential_comp_D, delta_apply_of_mem hρ hN σ hσ hσI b.2,
        smul_neg, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add x y hx hy => rw [map_add, map_add, hx, hy, neg_add]
  intro z w h
  have := congrArg G h
  rwa [hG, hG, neg_inj] at this

end Derivation

section Main

variable (C S : Type u) [CommRing C] [CommRing S] [Algebra C S]

/-- Lifting along elementary surjections of local Artinian `C`-algebras, for maps
whose composite to the residue field is surjective. Elementary means that the
kernel is annihilated by the maximal ideal of the source. -/
def HasArtinianLifting : Prop :=
  ∀ (B' B : Type u) [CommRing B'] [CommRing B] [IsLocalRing B'] [IsLocalRing B]
    [IsArtinianRing B'] [IsArtinianRing B] [Algebra C B'] [Algebra C B]
    (φ : B' →ₐ[C] B), Function.Surjective φ →
      maximalIdeal B' * RingHom.ker φ = ⊥ →
      ∀ ψ : S →ₐ[C] B, Function.Surjective ((residue B).comp ψ.toRingHom) →
        ∃ ψ' : S →ₐ[C] B', φ.comp ψ' = ψ

variable {C S} [IsNoetherianRing C] [Algebra.FiniteType C S]

/-- Artinian lifting makes the localization at every maximal ideal formally smooth. -/
theorem formallySmooth_localization (h : HasArtinianLifting C S) (q : Ideal S) [q.IsMaximal] :
    Algebra.FormallySmooth C (Localization.AtPrime q) := by
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    ‹Algebra.FiniteType C S›
  let Q : Ideal (MvPolynomial (Fin n) C) := q.comap π.toRingHom
  have : Q.IsMaximal := Ideal.comap_isMaximal_of_surjective π.toRingHom hπ
  let Pm := Localization.AtPrime Q
  let Sq := Localization.AtPrime q
  let ρ : Pm →+* Sq := Localization.localRingHom Q q π.toRingHom rfl
  let : Algebra Pm Sq := ρ.toAlgebra
  have hρmap : ∀ x, algebraMap Pm Sq (algebraMap (MvPolynomial (Fin n) C) Pm x) =
      algebraMap S Sq (π x) := fun x ↦ Localization.localRingHom_to_map _ _ _ _ x
  have : IsScalarTower C Pm Sq := IsScalarTower.of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply C (MvPolynomial (Fin n) C) Pm, hρmap, π.commutes,
      ← IsScalarTower.algebraMap_apply]
  have hρ : Function.Surjective (algebraMap Pm Sq) := by
    intro y
    obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl y
    obtain ⟨a, rfl⟩ := hπ s
    obtain ⟨b, hb⟩ := hπ t.1
    have hbQ : b ∈ Q.primeCompl := fun hb' ↦ t.2 (hb ▸ hb')
    refine ⟨IsLocalization.mk' Pm a ⟨b, hbQ⟩, ?_⟩
    change Localization.localRingHom Q q π.toRingHom rfl _ = _
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hb
  let bP := (KaehlerDifferential.mvPolynomialBasis C (Fin n)).ofIsLocalizedModule Pm
    Q.primeCompl (KaehlerDifferential.map C C (MvPolynomial (Fin n) C) Pm)
  have : Module.Free Pm Ω[Pm⁄C] := Module.Free.of_basis bP
  have : Module.Finite Pm Ω[Pm⁄C] := Module.Finite.of_basis bP
  have : Algebra.FormallySmooth C Pm := by
    have : Algebra.FormallySmooth (MvPolynomial (Fin n) C) Pm :=
      Algebra.FormallySmooth.of_isLocalization Q.primeCompl
    exact Algebra.FormallySmooth.comp C (MvPolynomial (Fin n) C) Pm
  rw [Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField Pm hρ
    (IsNoetherian.noetherian _)]
  -- Artin–Rees bound
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (maximalIdeal Pm)
    (RingHom.ker (algebraMap Pm Sq))
  have hN : maximalIdeal Pm ^ (k + 1) ⊓ RingHom.ker (algebraMap Pm Sq) ≤
      maximalIdeal Pm * RingHom.ker (algebraMap Pm Sq) := by
    calc maximalIdeal Pm ^ (k + 1) ⊓ RingHom.ker (algebraMap Pm Sq)
        = maximalIdeal Pm ^ (k + 1) • ⊤ ⊓ RingHom.ker (algebraMap Pm Sq) := by
          rw [Ideal.smul_eq_mul, Ideal.mul_top]
      _ = maximalIdeal Pm ^ (k + 1 - k) •
          (maximalIdeal Pm ^ k • ⊤ ⊓ RingHom.ker (algebraMap Pm Sq)) := hk (k + 1) (by omega)
      _ ≤ maximalIdeal Pm ^ (k + 1 - k) • RingHom.ker (algebraMap Pm Sq) :=
          smul_mono_right _ inf_le_right
      _ = maximalIdeal Pm * RingHom.ker (algebraMap Pm Sq) := by
          rw [show k + 1 - k = 1 by omega, pow_one, Ideal.smul_eq_mul]
  -- the two test rings
  have hpow : maximalIdeal Pm ^ (k + 1) ≤ maximalIdeal Pm := Ideal.pow_le_self (by omega)
  have hA : testIdeal Pm Sq (k + 1) ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal Pm).ne_top (sup_le Ideal.mul_le_left hpow)
  have hB : baseIdeal Pm Sq (k + 1) ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal Pm).ne_top (sup_le ker_le_maximalIdeal hpow)
  have := quotient_isLocalRing hA
  have := quotient_isLocalRing hB
  have := quotient_isArtinianRing hA (le_sup_right (a := maximalIdeal Pm *
    RingHom.ker (algebraMap Pm Sq)))
  have := quotient_isArtinianRing hB (le_sup_right (a := RingHom.ker (algebraMap Pm Sq)))
  let φ : Pm ⧸ testIdeal Pm Sq (k + 1) →ₐ[C] Pm ⧸ baseIdeal Pm Sq (k + 1) :=
    Ideal.Quotient.factorₐ C testIdeal_le_baseIdeal
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ p, rfl⟩
  have hφel : maximalIdeal (Pm ⧸ testIdeal Pm Sq (k + 1)) * RingHom.ker φ = ⊥ := by
    have hker : RingHom.ker φ =
        (baseIdeal Pm Sq (k + 1)).map (Ideal.Quotient.mk (testIdeal Pm Sq (k + 1))) :=
      Ideal.Quotient.factor_ker testIdeal_le_baseIdeal
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk _)
      Ideal.Quotient.mk_surjective, hker, ← Ideal.map_mul, Ideal.map_eq_bot_iff_le_ker,
      Ideal.mk_ker]
    dsimp only [baseIdeal, testIdeal]
    rw [Ideal.mul_sup]
    exact sup_le_sup_left Ideal.mul_le_right _
  -- the reduced test map
  let ρₐ : Pm →ₐ[C] Sq := IsScalarTower.toAlgHom C Pm Sq
  have hρₐ : Function.Surjective ρₐ := hρ
  let e := Ideal.quotientKerAlgEquivOfSurjective hρₐ
  have hle : RingHom.ker ρₐ ≤ baseIdeal Pm Sq (k + 1) := le_sup_left
  let χ : Sq →ₐ[C] Pm ⧸ baseIdeal Pm Sq (k + 1) :=
    (Ideal.Quotient.factorₐ C hle).comp e.symm.toAlgHom
  have hχ : ∀ p, χ (algebraMap Pm Sq p) = Ideal.Quotient.mk _ p := fun p ↦ by
    change Ideal.Quotient.factorₐ C hle (e.symm (ρₐ p)) = _
    rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
    rfl
  let ψ : S →ₐ[C] Pm ⧸ baseIdeal Pm Sq (k + 1) := χ.comp (IsScalarTower.toAlgHom C S Sq)
  have hψπ : ∀ x, ψ (π x) =
      Ideal.Quotient.mk _ (algebraMap (MvPolynomial (Fin n) C) Pm x) := fun x ↦ by
    change χ (algebraMap S Sq (π x)) = _
    rw [← hρmap, hχ]
  have hψres : Function.Surjective ((residue _).comp ψ.toRingHom) := by
    intro y
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl p
    obtain ⟨t', i, hi, hti⟩ := Ideal.IsMaximal.exists_inv ‹Q.IsMaximal› t.2
    refine ⟨π (a * t'), ?_⟩
    let r : Pm →+* ResidueField (Pm ⧸ baseIdeal Pm Sq (k + 1)) :=
      (residue _).comp (Ideal.Quotient.mk _)
    have hmk : IsLocalHom (Ideal.Quotient.mk (baseIdeal Pm Sq (k + 1))) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have hri : r (algebraMap (MvPolynomial (Fin n) C) Pm i) = 0 := by
      change residue _ (Ideal.Quotient.mk _ _) = 0
      rw [residue_eq_zero_iff]
      exact map_nonunit _ _ ((IsLocalization.AtPrime.to_map_mem_maximal_iff Pm Q i).mpr hi)
    have hs : r (IsLocalization.mk' Pm a t) * r (algebraMap (MvPolynomial (Fin n) C) Pm t) =
        r (algebraMap _ Pm a) := by
      rw [← map_mul, IsLocalization.mk'_spec]
    have hts : r (algebraMap _ Pm t') * r (algebraMap (MvPolynomial (Fin n) C) Pm t) = 1 := by
      rw [← map_mul, ← map_mul, eq_sub_of_add_eq hti, map_sub, map_one, map_sub, map_one, hri,
        sub_zero]
    change residue _ (ψ (π (a * t'))) = r (IsLocalization.mk' Pm a t)
    rw [hψπ]
    change r (algebraMap _ Pm (a * t')) = r (IsLocalization.mk' Pm a t)
    rw [map_mul, map_mul]
    linear_combination (-r (algebraMap _ Pm t')) * hs + r (IsLocalization.mk' Pm a t) * hts
  -- the lift and its extension to the localization
  obtain ⟨ψ', hψ'⟩ := h (Pm ⧸ testIdeal Pm Sq (k + 1)) (Pm ⧸ baseIdeal Pm Sq (k + 1)) φ hφ hφel
    ψ hψres
  have hunit : ∀ t : q.primeCompl, IsUnit (ψ' t) := by
    intro t
    have : IsLocalHom φ.toRingHom := IsLocalHom.of_surjective _ hφ
    apply isUnit_of_map_unit φ.toRingHom
    change IsUnit (φ (ψ' t))
    rw [← AlgHom.comp_apply, hψ']
    exact (IsLocalization.map_units Sq t).map χ
  let ψext : Sq →ₐ[C] Pm ⧸ testIdeal Pm Sq (k + 1) :=
    IsLocalization.liftAlgHom (M := q.primeCompl) (S := Sq) hunit
  have hψext : ∀ s, ψext (algebraMap S Sq s) = ψ' s := fun s ↦ IsLocalization.lift_eq _ _
  let σ : Pm →ₐ[C] Pm ⧸ testIdeal Pm Sq (k + 1) := ψext.comp ρₐ
  have hσI : ∀ j ∈ RingHom.ker (algebraMap Pm Sq), σ j = 0 := fun j hj ↦ by
    change ψext (algebraMap Pm Sq j) = 0
    rw [RingHom.mem_ker.mp hj, map_zero]
  have hφψ : φ.comp ψext = χ := by
    apply IsLocalization.algHom_ext q.primeCompl
    ext s
    change φ (ψext (algebraMap S Sq s)) = χ (algebraMap S Sq s)
    rw [hψext]
    change (φ.comp ψ') s = ψ s
    rw [hψ']
  have hσ : ∀ p, Ideal.Quotient.factor (testIdeal_le_baseIdeal (P := Pm) (T := Sq) (N := k + 1))
      (σ p) = Ideal.Quotient.mk (baseIdeal Pm Sq (k + 1)) p := fun p ↦ by
    change φ (ψext (algebraMap Pm Sq p)) = _
    rw [← AlgHom.comp_apply, hφψ, hχ]
  exact injective_cotangentComplexBaseChange hρ hN σ hσ hσI

/-- Artin lifting gives smoothness of a finite-type algebra over a noetherian ring. -/
theorem smooth (h : HasArtinianLifting C S) : Algebra.Smooth C S := by
  have : Algebra.FinitePresentation C S :=
    Algebra.FinitePresentation.of_finiteType.mp ‹Algebra.FiniteType C S›
  have hU : Algebra.smoothLocus C S = Set.univ := by
    by_contra hne
    obtain ⟨x, hx, hxc⟩ := Algebra.isOpen_smoothLocus.isClosed_compl.exists_closed_singleton
      (Set.nonempty_compl.mpr hne)
    have := (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp hxc
    exact hx (formallySmooth_localization h x.asIdeal)
  exact ⟨Algebra.smoothLocus_eq_univ_iff.mp hU, inferInstance⟩

end Main

end Langlands.RingTheory.ArtinianLifting
