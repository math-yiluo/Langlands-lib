import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Langlands.Geometry.Analytic.FlatTargetDescent

/-! # Flatness at a maximal ideal from bijective truncated comparison maps -/

noncomputable section

universe u v

namespace Langlands.Analytic.TruncatedComparison

open AdicCompletion

section Quotient

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Bijectivity of the comparison map `R ⧸ J → S ⧸ J S` passes to every larger
ideal `𝔟 ⊇ J`. -/
theorem quotientMap_bijective_of_le {J 𝔟 : Ideal R} (hJ : J ≤ 𝔟)
    (h : Function.Bijective
      (Ideal.quotientMap (J.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map)) :
    Function.Bijective
      (Ideal.quotientMap (𝔟.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map) := by
  let e := RingEquiv.ofBijective _ h
  let ψ : S →+* R ⧸ J := e.symm.toRingHom.comp (Ideal.Quotient.mk _)
  have hψ : ∀ r, ψ (algebraMap R S r) = Ideal.Quotient.mk J r := by
    intro r
    apply e.injective
    change e (e.symm (Ideal.Quotient.mk _ (algebraMap R S r))) = _
    rw [RingEquiv.apply_symm_apply]
    rfl
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have hle : 𝔟.map (algebraMap R S) ≤ (𝔟.map (Ideal.Quotient.mk J)).comap ψ := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap, Ideal.mem_comap, hψ]
      exact Ideal.mem_map_of_mem _ hb
    have hr := hle hx
    rwa [Ideal.mem_comap, hψ, Ideal.mem_quotient_iff_mem hJ] at hr
  · intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, hx⟩ := h.2 (Ideal.Quotient.mk _ s)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    rw [Ideal.quotientMap_mk] at hx ⊢
    rw [Ideal.Quotient.eq] at hx ⊢
    exact Ideal.map_mono hJ hx

end Quotient

section Evaluation

variable {A : Type*} [CommRing A]

/-- Truncating an evaluation of the adic completion gives the lower evaluation. -/
theorem factor_evalₐ (I : Ideal A) {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I A) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) (evalₐ I n x) = evalₐ I m x := by
  obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective I A x
  rw [evalₐ_mk, evalₐ_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
  have h := (Submodule.Quotient.eq _).mp (AdicCauchySequence.mk_eq_mk hmn c)
  simpa only [smul_eq_mul, Ideal.mul_top] using h

end Evaluation

section Core

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Powers of a contracted ideal map into the corresponding powers. -/
theorem pow_le_comap_pow {𝔪 : Ideal S} {𝔫 : Ideal R}
    (h𝔫 : 𝔫 ≤ 𝔪.comap (algebraMap R S)) (k : ℕ) :
    𝔫 ^ k ≤ (𝔪 ^ k).comap (algebraMap R S) :=
  (Ideal.pow_right_mono h𝔫 k).trans (Ideal.le_comap_pow _ k)

variable {𝔪 : Ideal S} {𝔫 : Ideal R} (h𝔫 : 𝔫 ≤ 𝔪.comap (algebraMap R S))
  (hbij : ∀ k : ℕ, Function.Bijective
    (Ideal.quotientMap (𝔪 ^ k) (algebraMap R S) (pow_le_comap_pow h𝔫 k)))

/-- The truncated comparison isomorphisms `R ⧸ 𝔫 ^ k ≃ S ⧸ 𝔪 ^ k`. -/
def truncEquiv (k : ℕ) : (R ⧸ 𝔫 ^ k) ≃ₐ[R] (S ⧸ 𝔪 ^ k) :=
  AlgEquiv.ofBijective
    (Ideal.quotientMapₐ (𝔪 ^ k) (Algebra.ofId R S) (pow_le_comap_pow h𝔫 k)) (hbij k)

theorem truncEquiv_mk (k : ℕ) (r : R) :
    truncEquiv h𝔫 hbij k (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (algebraMap R S r) := rfl

theorem factor_truncEquiv {m n : ℕ} (hmn : m ≤ n) (x : R ⧸ 𝔫 ^ n) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) (truncEquiv h𝔫 hbij n x) =
      truncEquiv h𝔫 hbij m (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) x) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [truncEquiv_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, truncEquiv_mk]

theorem factor_truncEquiv_symm {m n : ℕ} (hmn : m ≤ n) (y : S ⧸ 𝔪 ^ n) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) ((truncEquiv h𝔫 hbij n).symm y) =
      (truncEquiv h𝔫 hbij m).symm (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) y) := by
  apply (truncEquiv h𝔫 hbij m).injective
  rw [AlgEquiv.apply_symm_apply, ← factor_truncEquiv h𝔫 hbij hmn, AlgEquiv.apply_symm_apply]

instance isScalarTower_adicCompletion (I : Ideal S) :
    IsScalarTower R S (AdicCompletion I S) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The components `AdicCompletion 𝔫 R → S ⧸ 𝔪 ^ k` of the comparison map. -/
def homComponent (k : ℕ) : AdicCompletion 𝔫 R →ₐ[R] S ⧸ 𝔪 ^ k :=
  (truncEquiv h𝔫 hbij k : (R ⧸ 𝔫 ^ k) →ₐ[R] S ⧸ 𝔪 ^ k).comp (evalₐ 𝔫 k)

theorem homComponent_apply (k : ℕ) (x : AdicCompletion 𝔫 R) :
    homComponent h𝔫 hbij k x = truncEquiv h𝔫 hbij k (evalₐ 𝔫 k x) := rfl

/-- The components `AdicCompletion 𝔪 S → R ⧸ 𝔫 ^ k` of the inverse comparison map. -/
def invComponent (k : ℕ) : AdicCompletion 𝔪 S →ₐ[R] R ⧸ 𝔫 ^ k :=
  ((truncEquiv h𝔫 hbij k).symm : (S ⧸ 𝔪 ^ k) →ₐ[R] R ⧸ 𝔫 ^ k).comp
    ((evalₐ 𝔪 k).restrictScalars R)

theorem invComponent_apply (k : ℕ) (x : AdicCompletion 𝔪 S) :
    invComponent h𝔫 hbij k x = (truncEquiv h𝔫 hbij k).symm (evalₐ 𝔪 k x) := rfl

theorem homComponent_compat {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (homComponent h𝔫 hbij n) =
      homComponent h𝔫 hbij m := by
  ext x
  rw [AlgHom.comp_apply, homComponent_apply, homComponent_apply,
    Ideal.Quotient.factorₐ_apply, factor_truncEquiv h𝔫 hbij hmn, factor_evalₐ _ hmn]

theorem invComponent_compat {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (invComponent h𝔫 hbij n) =
      invComponent h𝔫 hbij m := by
  ext x
  rw [AlgHom.comp_apply, invComponent_apply, invComponent_apply,
    Ideal.Quotient.factorₐ_apply, factor_truncEquiv_symm h𝔫 hbij hmn, factor_evalₐ _ hmn]

/-- The comparison of the two adic completions, from the completion of `R`. -/
def completionHom : AdicCompletion 𝔫 R →ₐ[R] AdicCompletion 𝔪 S :=
  liftAlgHom 𝔪 (homComponent h𝔫 hbij) (homComponent_compat h𝔫 hbij)

/-- The comparison of the two adic completions, to the completion of `R`. -/
def completionInv : AdicCompletion 𝔪 S →ₐ[R] AdicCompletion 𝔫 R :=
  liftAlgHom 𝔫 (invComponent h𝔫 hbij) (invComponent_compat h𝔫 hbij)

theorem evalₐ_completionHom (k : ℕ) (x : AdicCompletion 𝔫 R) :
    evalₐ 𝔪 k (completionHom h𝔫 hbij x) = truncEquiv h𝔫 hbij k (evalₐ 𝔫 k x) :=
  evalₐ_liftAlgHom 𝔪 _ (homComponent_compat h𝔫 hbij) k x

theorem evalₐ_completionInv (k : ℕ) (x : AdicCompletion 𝔪 S) :
    evalₐ 𝔫 k (completionInv h𝔫 hbij x) = (truncEquiv h𝔫 hbij k).symm (evalₐ 𝔪 k x) :=
  evalₐ_liftAlgHom 𝔫 _ (invComponent_compat h𝔫 hbij) k x

/-- The two adic completions are isomorphic as `R`-algebras. -/
def completionEquiv : AdicCompletion 𝔪 S ≃ₐ[R] AdicCompletion 𝔫 R :=
  AlgEquiv.ofAlgHom (completionInv h𝔫 hbij) (completionHom h𝔫 hbij)
    (by
      apply AlgHom.ext
      intro x
      apply ext_evalₐ
      intro k
      rw [AlgHom.comp_apply, evalₐ_completionInv, evalₐ_completionHom,
        AlgEquiv.symm_apply_apply, AlgHom.id_apply])
    (by
      apply AlgHom.ext
      intro x
      apply ext_evalₐ
      intro k
      rw [AlgHom.comp_apply, evalₐ_completionHom, evalₐ_completionInv,
        AlgEquiv.apply_symm_apply, AlgHom.id_apply])

variable [IsNoetherianRing R] [IsNoetherianRing S] [𝔪.IsMaximal]

include h𝔫 hbij in
/-- If all truncated comparison maps at a maximal ideal are bijective, the
localization of `S` at that maximal ideal is flat over `R`. -/
theorem flat_localization : Module.Flat R (Localization.AtPrime 𝔪) := by
  let T := AdicCompletion 𝔪 S
  have hTflat : Module.Flat R T :=
    Module.Flat.of_linearEquiv (completionEquiv h𝔫 hbij).toLinearEquiv
  have hfg : 𝔪.FG := (IsNoetherian.noetherian 𝔪)
  have hcomplete : IsAdicComplete (𝔪.map (algebraMap S T)) T :=
    AdicCompletion.isAdicComplete_self 𝔪 hfg
  have hmax : (𝔪.map (algebraMap S T)).IsMaximal :=
    AdicCompletion.isMaximal_map_of_le 𝔪 𝔪 le_rfl hfg
  have : IsLocalRing T := isLocalRing_of_isAdicComplete_maximal (𝔪.map (algebraMap S T))
  have hunit : ∀ s : 𝔪.primeCompl, IsUnit (algebraMap S T s) := by
    rintro ⟨s, hs⟩
    obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv ‹𝔪.IsMaximal› hs
    have hj : algebraMap S T i ∈ (⊥ : Ideal T).jacobson :=
      IsAdicComplete.le_jacobson_bot _ (Ideal.mem_map_of_mem _ hi)
    rw [Ideal.mem_jacobson_bot] at hj
    have hu := hj (-1)
    have heq : algebraMap S T i * -1 + 1 = algebraMap S T y * algebraMap S T s := by
      rw [← map_mul, show y * s = 1 - i by rw [← hyi]; ring, map_sub, map_one]
      ring
    rw [heq] at hu
    exact isUnit_of_mul_isUnit_right hu
  let f : Localization.AtPrime 𝔪 →+* T := IsLocalization.lift (M := 𝔪.primeCompl) hunit
  let _ : Algebra (Localization.AtPrime 𝔪) T := f.toAlgebra
  have : IsScalarTower S (Localization.AtPrime 𝔪) T :=
    IsScalarTower.of_algebraMap_eq fun s => (IsLocalization.lift_eq hunit s).symm
  have : IsScalarTower R (Localization.AtPrime 𝔪) T :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime 𝔪),
        IsScalarTower.algebraMap_apply R S T]
      exact (IsLocalization.lift_eq hunit _).symm
  have : Module.Flat S T := AdicCompletion.flat_of_isNoetherian 𝔪
  have : Module.Flat (Localization.AtPrime 𝔪) T :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime 𝔪) 𝔪.primeCompl T).mpr
      inferInstance
  have : IsLocalHom (algebraMap (Localization.AtPrime 𝔪) T) := by
    apply ((IsLocalRing.local_hom_TFAE (algebraMap (Localization.AtPrime 𝔪) T)).out 1 3).mpr
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq, ← IsLocalRing.eq_maximalIdeal hmax]
  have : Module.FaithfullyFlat (Localization.AtPrime 𝔪) T :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact flat_of_faithfullyFlat_target R (Localization.AtPrime 𝔪) T

end Core

section Global

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Flatness of `S` over `R` follows from flatness of all localizations of `S`
at maximal ideals. -/
theorem flat_of_forall_maximal
    (H : ∀ (𝔪 : Ideal S) [𝔪.IsMaximal], Module.Flat R (Localization.AtPrime 𝔪)) :
    Module.Flat R S :=
  Module.flat_of_isLocalized_maximal S S (fun P _ => Localization.AtPrime P)
    (fun P _ => Algebra.linearMap S (Localization.AtPrime P)) H

end Global

end Langlands.Analytic.TruncatedComparison
