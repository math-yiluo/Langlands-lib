import Langlands.ClassFieldTheory.Global.PositiveQuadraticNormProfile
import Langlands.Shimura.Unitary.NonsplitCompletionChart

/-! # Descent of a finite quadratic norm profile through a number field norm -/

noncomputable section

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra IsDedekindDomain
open Langlands.Global (FiniteCompletion)
open Langlands.Global.AdelicFunctoriality Langlands.LocalClassField
open Langlands.ClassFieldTheory.Global
open scoped FiniteExtension NumberField

universe u v s t

section NormTower

variable {R : Type u} {S : Type v} {T : Type s} {U : Type t}
  [Field R] [Field S] [Field T] [Field U]
  [Algebra R S] [Algebra R T] [Algebra R U] [Algebra S U] [Algebra T U]
  [IsScalarTower R S U] [IsScalarTower R T U]
  [FiniteDimensional R S] [FiniteDimensional R T] [FiniteDimensional S U] [FiniteDimensional T U]

private theorem normUnits_tower (y : Uˣ) :
    normUnits R S (normUnits S U y) = normUnits R T (normUnits T U y) := by
  apply Units.ext
  change Algebra.norm R (Algebra.norm S (y : U)) = Algebra.norm R (Algebra.norm T (y : U))
  rw [Algebra.norm_norm, Algebra.norm_norm]

private theorem normUnits_mem_of_mem (x : Sˣ) (hx : x ∈ normSubgroup S U) :
    normUnits R S x ∈ normSubgroup R T := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨normUnits T U y, (normUnits_tower y).symm⟩

private theorem normUnits_mem_iff_of_degree_one (hs : Module.finrank R S = 1)
    (ht : Module.finrank T U = 1) (x : Sˣ) :
    normUnits R S x ∈ normSubgroup R T ↔ x ∈ normSubgroup S U := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hx
    have hnorm : Function.Injective (normUnits R S) := by
      intro a b hab
      apply Units.ext
      obtain ⟨a', ha'⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hs).2 (a : S)
      obtain ⟨b', hb'⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hs).2 (b : S)
      have h := congrArg Units.val hab
      change Algebra.norm R (a : S) = Algebra.norm R (b : S) at h
      rw [← ha', ← hb', Algebra.norm_algebraMap, Algebra.norm_algebraMap, hs, pow_one, pow_one] at h
      rw [← ha', ← hb', h]
    let z := Units.map (algebraMap T U).toMonoidHom y
    have hz : normUnits T U z = y := by
      apply Units.ext
      change Algebra.norm T (algebraMap T U (y : T)) = (y : T)
      rw [Algebra.norm_algebraMap, ht, pow_one]
    exact ⟨z, hnorm ((normUnits_tower z).trans (hz ▸ hy))⟩
  · exact normUnits_mem_of_mem x

end NormTower

section Completions

variable {E : Type u} {K F M : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K]
  [Field F] [NumberField F] [Algebra E F] [Field M] [NumberField M]
  [Algebra F M] [IsQuadraticExtension F M] [Algebra K M] [Algebra E M]
  [IsScalarTower E F M] [IsScalarTower E K M]

attribute [local instance] FiniteExtension.local_finite CompletionTower.isScalarTower_completion

private def chosenUpperPlace (E : Type u) (F : Type v) [Field E] [NumberField E]
    [Field F] [NumberField F] [Algebra E F] :
    Langlands.Global.FinitePlace E ↪ Langlands.Global.FinitePlace F where
  toFun p := (placeAbove F p).val
  inj' := fun {p q} h => (finitePlacesAbove_under p (placeAbove F p)).symm.trans
    ((congrArg (fun x : Langlands.Global.FinitePlace F => x.under (𝓞 E)) h).trans
      (finitePlacesAbove_under q (placeAbove F q)))

variable (p : Langlands.Global.FinitePlace E) (hp : ¬ IsSplitPlace E K p)
  (r : FinitePlacesAbove F p)

local notation "q₀" => Subtype.val (placeAbove K p)
local notation "w₀" => Subtype.val (placeAbove M (Subtype.val r))
local notation "R₀" => FiniteCompletion E p
local notation "S₀" => FiniteCompletion F r.val
local notation "T₀" => FiniteCompletion K q₀
local notation "U₀" => FiniteCompletion M w₀

private instance upper_liesOver_base : (w₀).asIdeal.LiesOver p.asIdeal :=
  Ideal.LiesOver.trans (w₀).asIdeal r.val.asIdeal p.asIdeal

omit [IsQuadraticExtension F M] in
include hp in
private theorem upper_liesOver_cm : (w₀).asIdeal.LiesOver (q₀).asIdeal := by
  let q' := (w₀).under (𝓞 K)
  let : (w₀).asIdeal.LiesOver q'.asIdeal := ⟨rfl⟩
  let : q'.asIdeal.LiesOver p.asIdeal := Ideal.LiesOver.tower_bot (w₀).asIdeal q'.asIdeal p.asIdeal
  have heq := congrArg Subtype.val (eq_placeAbove_of_nonsplit p hp
    (⟨q', inferInstance⟩ : FinitePlacesAbove K p))
  exact heq ▸ (inferInstance : (w₀).asIdeal.LiesOver q'.asIdeal)

include hp in
private theorem localDegrees_of_base_degree_one (hd : Module.finrank R₀ S₀ = 1) :
    letI := upper_liesOver_cm (M := M) p hp r
    Module.finrank S₀ U₀ = 2 ∧ Module.finrank T₀ U₀ = 1 := by
  let : (w₀).asIdeal.LiesOver (q₀).asIdeal := upper_liesOver_cm (M := M) p hp r
  have hS := Module.finrank_mul_finrank R₀ S₀ U₀
  have hT := Module.finrank_mul_finrank R₀ T₀ U₀
  rw [hd, one_mul] at hS
  rw [nonsplitCompletion_finrank p hp, ← hS] at hT
  change 2 * Module.finrank T₀ U₀ = Module.finrank S₀ U₀ at hT
  have hw := localDegree_dvd r.val w₀
  rw [IsQuadraticExtension.finrank_eq_two F M] at hw
  rcases (Nat.dvd_prime Nat.prime_two).mp hw with he | he
  · rw [he] at hT
    omega
  · refine ⟨he, ?_⟩
    rw [he] at hT
    omega

omit [IsQuadraticExtension F M] in
include hp in
private theorem localNormFactor_mem (x : S₀ˣ) (hx : x ∈ normSubgroup S₀ U₀) :
    normUnits R₀ S₀ x ∈ normSubgroup R₀ T₀ := by
  let : (w₀).asIdeal.LiesOver (q₀).asIdeal := upper_liesOver_cm (M := M) p hp r
  exact normUnits_mem_of_mem x hx

include hp in
private theorem localNormFactor_mem_iff (hd : Module.finrank R₀ S₀ = 1) (x : S₀ˣ) :
    normUnits R₀ S₀ x ∈ normSubgroup R₀ T₀ ↔ x ∈ normSubgroup S₀ U₀ := by
  let : (w₀).asIdeal.LiesOver (q₀).asIdeal := upper_liesOver_cm (M := M) p hp r
  exact normUnits_mem_iff_of_degree_one hd (localDegrees_of_base_degree_one (M := M) p hp r hd).2 x

omit [IsTotallyReal E] [IsTotallyComplex K] [IsQuadraticExtension E K] [Field K]
  [NumberField K] [Algebra E K] [Field M] [NumberField M] [Algebra F M]
  [IsQuadraticExtension F M] [Algebra K M] [Algebra E M] [IsScalarTower E F M]
  [IsScalarTower E K M] in
private theorem normUnits_eq_prod (t : Fˣ) :
    Units.map (algebraMap E R₀).toMonoidHom (normUnits E F t) =
      ∏ r : FinitePlacesAbove F p,
        normUnits R₀ (FiniteCompletion F r.val)
          (Units.map (algebraMap F (FiniteCompletion F r.val)).toMonoidHom t) := by
  apply Units.ext
  change algebraMap E R₀ (Algebra.norm E (t : F)) = Units.coeHom R₀ _
  rw [map_prod]
  exact (finiteNorm_principal_of_bijective p ((completedTensorComparison E F).1 p) (t : F)).symm

variable [IsTotallyComplex M] (S : Finset (Langlands.Global.FinitePlace E))
  (hS : ∀ p ∈ S, ¬ IsSplitPlace E K p) (heven : Even S.card)
  (hd : ∀ p ∈ S, Module.finrank (FiniteCompletion E p)
    (FiniteCompletion F (placeAbove F p).val) = 1)

set_option maxRecDepth 4096 in
/-- An even set of nonsplit places with a degree-one completion in the lower
extension is the nonnorm profile of the norm of a totally positive unit. -/
def positiveQuadraticNormProfileDescend :
    {t : Fˣ // (∀ v : InfinitePlace F, v.IsReal → 0 < (v.embedding (t : F)).re) ∧
      ∀ (p : Langlands.Global.FinitePlace E), ¬ IsSplitPlace E K p →
        (Units.map (algebraMap E (FiniteCompletion E p)).toMonoidHom (normUnits E F t) ∈
          normSubgroup (FiniteCompletion E p) (FiniteCompletion K (placeAbove K p).val) ↔
        p ∉ S)} := by
  classical
  let ι := chosenUpperPlace E F
  let P := S.map ι
  have hPdeg (r : Langlands.Global.FinitePlace F) (hr : r ∈ P) :
      Module.finrank (FiniteCompletion F r) (FiniteCompletion M (placeAbove M r).val) = 2 := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hr
    exact (localDegrees_of_base_degree_one (M := M) p (hS p hp) (placeAbove F p) (hd p hp)).1
  let t := positiveQuadraticNormProfile (F := F) (L := M) P
    ((Finset.card_map ι).symm ▸ heven) hPdeg
  refine ⟨t.unit, t.positive, ?_⟩
  intro p hp
  let r₀ := placeAbove F p
  let N := normSubgroup (FiniteCompletion E p) (FiniteCompletion K (placeAbove K p).val)
  let y (r : FinitePlacesAbove F p) :=
    Units.map (algebraMap F (FiniteCompletion F r.val)).toMonoidHom t.unit
  let z (r : FinitePlacesAbove F p) :=
    normUnits (FiniteCompletion E p) (FiniteCompletion F r.val) (y r)
  rw [normUnits_eq_prod p t.unit]
  change (∏ r, z r) ∈ N ↔ p ∉ S
  have hP (r : FinitePlacesAbove F p) : r.val ∈ P ↔ p ∈ S ∧ r = r₀ := by
    constructor
    · intro hr
      obtain ⟨p', hp', hr'⟩ := Finset.mem_map.mp hr
      have he := congrArg (fun v : Langlands.Global.FinitePlace F => v.under (𝓞 E)) hr'
      change (placeAbove F p').val.under (𝓞 E) = r.val.under (𝓞 E) at he
      rw [finitePlacesAbove_under, finitePlacesAbove_under] at he
      subst p'
      exact ⟨hp', Subtype.ext hr'.symm⟩
    · rintro ⟨h, rfl⟩
      exact Finset.mem_map.mpr ⟨p, h, rfl⟩
  have hZ (r : FinitePlacesAbove F p) (hr : r.val ∉ P) : z r ∈ N :=
    localNormFactor_mem (M := M) p hp r (y r) ((t.finiteNorm r.val).mpr hr)
  by_cases h : p ∈ S
  · have hprod : (∏ r ∈ Finset.univ.erase r₀, z r) ∈ N :=
      N.prod_mem fun r hr => hZ r (fun hr' => (Finset.mem_erase.mp hr).1 ((hP r).mp hr').2)
    have hz₀ : z r₀ ∈ N ↔ r₀.val ∉ P :=
      (localNormFactor_mem_iff (M := M) p hp r₀ (hd p h) (y r₀)).trans (t.finiteNorm r₀.val)
    rw [← Finset.prod_erase_mul Finset.univ z (Finset.mem_univ r₀), N.mul_mem_cancel_left hprod,
      hz₀, hP]
    simp
  · exact ⟨fun _ => h, fun _ => N.prod_mem fun r _ => hZ r (fun hr => h ((hP r).mp hr).1)⟩

end Completions

end Langlands.Shimura.FiniteUnitary
