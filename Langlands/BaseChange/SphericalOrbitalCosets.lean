import Langlands.BaseChange.SphericalNormLift
import Langlands.BaseChange.NormCentralizer
import Langlands.TraceFormula.CompactOpenOrbitalIntegral

/-! Double-coset comparison for the unit fundamental lemma. -/

noncomputable section

namespace Langlands.BaseChange

open Correspondence Langlands.JacquetLanglands Langlands.Unramified Langlands.TraceFormula

universe u v w

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]

local instance fieldTopology (L : PadicField.{w} p) : TopologicalSpace L.Carrier :=
  L.canonicalTopologicalData.topology
local instance fieldValuativeRel (L : PadicField.{w} p) : ValuativeRel L.Carrier :=
  L.canonicalTopologicalData.valuativeRel
local instance fieldLocalField (L : PadicField.{w} p) : IsNonarchimedeanLocalField L.Carrier :=
  L.canonicalTopologicalData.localField
local instance fieldModuleTopology (L : PadicField.{w} p) : IsModuleTopology (Padic p) L.Carrier :=
  L.canonicalTopologicalData.moduleTopology

/-- The canonical topology of a p-adic field extension is its module topology
over the intermediate p-adic field as well. -/
theorem canonicalRelativeModuleTopology : IsModuleTopology F.Carrier E.Carrier := by
  have hF : Continuous (algebraMap (Padic p) F.Carrier) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (Padic p) F.Carrier)
  have hE : Continuous (algebraMap F.Carrier E.Carrier) :=
    IsModuleTopology.continuous_of_linearMap (IsScalarTower.toAlgHom (Padic p) F.Carrier E.Carrier).toLinearMap
  have hle : moduleTopology (Padic p) E.Carrier ≤ moduleTopology F.Carrier E.Carrier := by
    let : TopologicalSpace E.Carrier := moduleTopology F.Carrier E.Carrier
    let : ContinuousAdd E.Carrier := ModuleTopology.continuousAdd F.Carrier E.Carrier
    let : ContinuousSMul F.Carrier E.Carrier := ModuleTopology.continuousSMul F.Carrier E.Carrier
    let : ContinuousSMul (Padic p) E.Carrier := ⟨by
      have h := (continuous_smul (M := F.Carrier) (X := E.Carrier)).comp
        ((hF.comp continuous_fst).prodMk continuous_snd)
      change Continuous (fun t : Padic p × E.Carrier => algebraMap (Padic p) F.Carrier t.1 • t.2) at h
      simpa only [algebraMap_smul] using h⟩
    exact moduleTopology_le (Padic p) E.Carrier
  let : ContinuousSMul F.Carrier E.Carrier := ⟨by
    have h := (hE.comp continuous_fst).mul (continuous_snd (X := F.Carrier))
    change Continuous (fun t : F.Carrier × E.Carrier => algebraMap F.Carrier E.Carrier t.1 * t.2) at h
    simpa only [Algebra.smul_def] using h⟩
  exact ⟨le_antisymm ((eq_moduleTopology (Padic p) E.Carrier).le.trans hle)
    (moduleTopology_le F.Carrier E.Carrier)⟩

variable {σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier} {l r : ℕ}

local notation "GF" => GeneralLinear (r + 1) F.Carrier
local notation "GE" => GeneralLinear (r + 1) E.Carrier
local notation "B" => baseChange F.Carrier E.Carrier (r + 1)
local notation "θ" => entrywiseAut σ (r + 1)
local notation "KF" => sphericalSubgroup F r
local notation "KE" => sphericalSubgroup E r

variable {δ : GeneralLinear (r + 1) E.Carrier} {γ : GeneralLinear (r + 1) F.Carrier}

private theorem sphericalDoubleCoset_mk_eq_iff (hσ : IsCyclicAlgebra σ l)
    (hγ : IsRegularSemisimple γ) (s : GE) (hs : s⁻¹ * cyclicNorm σ l δ * s = B γ)
    (y z : GF) :
    DoubleCoset.mk (sigmaCentralizer σ (r + 1) δ) KE (s * B y) =
        DoubleCoset.mk (sigmaCentralizer σ (r + 1) δ) KE (s * B z) ↔
      DoubleCoset.mk (glCentralizer γ) KF y = DoubleCoset.mk (glCentralizer γ) KF z := by
  let := canonicalRelativeModuleTopology F E
  let e := normCentralizerEquiv hσ hγ s hs
  rw [DoubleCoset.eq, DoubleCoset.eq]
  constructor
  · rintro ⟨c, hc, k, hk, heq⟩
    obtain ⟨t, ht⟩ := e.surjective ⟨c, hc⟩
    have htc : s * B t.val * s⁻¹ = c := by
      rw [← normCentralizerEquiv_apply_val hσ hγ s hs t, ht]
    have htz : B z = B t.val * B y * k := by
      apply mul_left_cancel (a := s)
      rw [heq, ← htc]
      group
    have hbk : B (y⁻¹ * t.val⁻¹ * z) = k := by
      rw [map_mul, map_mul, map_inv, map_inv, htz]
      group
    have hk' := (baseChange_mem_sphericalSubgroup_iff F E (y⁻¹ * t.val⁻¹ * z)).mp (hbk.symm ▸ hk)
    exact ⟨t.val, t.property, _, hk', by group⟩
  · rintro ⟨t, ht, k, hk, rfl⟩
    refine ⟨(e ⟨t, ht⟩).val, (e ⟨t, ht⟩).property, B k,
      (baseChange_mem_sphericalSubgroup_iff F E k).mpr hk, ?_⟩
    change s * B (t * y * k) = (normCentralizerEquiv hσ hγ s hs ⟨t, ht⟩).val * (s * B y) * B k
    rw [normCentralizerEquiv_apply_val, map_mul, map_mul]
    group

/-- Left multiplication by a norm conjugator after base change gives a map
on the actual double cosets of the two centralizers and spherical subgroups. -/
def sphericalDoubleCosetMap (hσ : IsCyclicAlgebra σ l) (hγ : IsRegularSemisimple γ) (s : GE)
    (hs : s⁻¹ * cyclicNorm σ l δ * s = B γ) :
    DoubleCoset.Quotient (glCentralizer γ : Set GF) KF →
      DoubleCoset.Quotient (sigmaCentralizer σ (r + 1) δ : Set GE) KE :=
  Quotient.map' (fun y => s * B y) fun y z h => DoubleCoset.eq''.mp
    ((sphericalDoubleCoset_mk_eq_iff F E hσ hγ s hs y z).mpr (DoubleCoset.eq''.mpr h))

@[simp] theorem sphericalDoubleCosetMap_mk (hσ : IsCyclicAlgebra σ l) (hγ : IsRegularSemisimple γ)
    (s : GE) (hs : s⁻¹ * cyclicNorm σ l δ * s = B γ) (y : GF) :
    sphericalDoubleCosetMap F E hσ hγ s hs (DoubleCoset.mk (glCentralizer γ) KF y) =
      DoubleCoset.mk (sigmaCentralizer σ (r + 1) δ) KE (s * B y) := rfl

private theorem sphericalDoubleCosetMap_injective (hσ : IsCyclicAlgebra σ l)
    (hγ : IsRegularSemisimple γ) (s : GE) (hs : s⁻¹ * cyclicNorm σ l δ * s = B γ) :
    Function.Injective (sphericalDoubleCosetMap F E hσ hγ s hs) := by
  intro a b hab
  rw [← DoubleCoset.out_eq' a, ← DoubleCoset.out_eq' b] at hab ⊢
  exact (sphericalDoubleCoset_mk_eq_iff F E hσ hγ s hs a.out b.out).mp hab

local notation "KFo" => sphericalOpenSubgroup F r
local notation "KEo" => sphericalOpenSubgroup E r
local notation "OF" => compactOpenTwistedDoubleCosets (MonoidHom.id GF) γ KFo
local notation "OE" => compactOpenTwistedDoubleCosets θ δ KEo

omit [IsScalarTower (Padic p) F.Carrier E.Carrier] in
private theorem twistedConj_mul_normLift (s u : GE)
    (hs : s⁻¹ * δ * θ s = u) (z : GE) :
    twistedConj θ (s * z) δ = z⁻¹ * u * θ z := by
  rw [← twistedConj_mul]
  change z⁻¹ * (s⁻¹ * δ * θ s) * θ z = _
  rw [hs]

private theorem sphericalDoubleCosetMap_mem (hσ : IsCyclicAlgebra σ l) (hγ : IsRegularSemisimple γ)
    (s u : GE) (hs : s⁻¹ * δ * θ s = u) (hsN : s⁻¹ * cyclicNorm σ l δ * s = B γ)
    (huInt : ∀ z : GE, z⁻¹ * B γ * z ∈ KE → z⁻¹ * u * z ∈ KE) (d : OF) :
    twistedConj θ (sphericalDoubleCosetMap F E hσ hγ s hsN d.val).out δ ∈ KEo := by
  have hd : DoubleCoset.mk (glCentralizer γ) KF d.val.out = d.val := DoubleCoset.out_eq' _
  rw [← hd, sphericalDoubleCosetMap_mk F E hσ hγ s hsN d.val.out]
  apply (compactOpenTwistedDoubleCosets_mk_iff θ δ KEo
    (fun _ h => entrywiseAut_mem_sphericalSubgroup F E σ h) _).mpr
  rw [twistedConj_mul_normLift F E s u hs, entrywiseAut_baseChange]
  apply huInt
  rw [← map_inv, ← map_mul, ← map_mul, baseChange_mem_sphericalSubgroup_iff F E]
  exact d.property

/-- A lift integral on all spherical conjugates of its norm identifies the
contributing ordinary and twisted double cosets. -/
def sphericalOrbitalCosetsEquiv (hσ : IsCyclicAlgebra σ l)
    (he : E.canonicalTopologicalData.ramificationIndex = F.canonicalTopologicalData.ramificationIndex)
    (hγ : IsRegularSemisimple γ) (s u : GE) (hs : s⁻¹ * δ * θ s = u)
    (hsN : s⁻¹ * cyclicNorm σ l δ * s = B γ) (hu : cyclicNorm σ l u = B γ)
    (huInt : ∀ z : GE, z⁻¹ * B γ * z ∈ KE → z⁻¹ * u * z ∈ KE) : OF ≃ OE := by
  let f (d : OF) : OE := ⟨sphericalDoubleCosetMap F E hσ hγ s hsN d.val,
    sphericalDoubleCosetMap_mem F E hσ hγ s u hs hsN huInt d⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro d e h
    exact Subtype.ext (sphericalDoubleCosetMap_injective F E hσ hγ s hsN (congrArg Subtype.val h))
  · intro d
    let z := s⁻¹ * d.val.out
    have hz : s * z = d.val.out := by simp [z]
    have hδz : z⁻¹ * u * θ z ∈ KE := by
      rw [← twistedConj_mul_normLift F E s u hs z, hz]
      exact d.property
    have hzΓ := cyclicNorm_mem_sphericalSubgroup F E σ l hδz
    rw [cyclicNorm_twistedConj, hσ.pow_eq_one, entrywiseAut_one_apply, hu] at hzΓ
    have hfix : z⁻¹ * θ z ∈ KE := by
      rw [show z⁻¹ * θ z = (z⁻¹ * u * z)⁻¹ * (z⁻¹ * u * θ z) by group]
      exact (KE).mul_mem ((KE).inv_mem (huInt z hzΓ)) hδz
    obtain ⟨y, k, hk, hy⟩ := exists_baseChange_mul_spherical_of_fixed F E σ hσ he z hfix
    have hyΓ : y⁻¹ * γ * y ∈ KF := by
      apply (baseChange_mem_sphericalSubgroup_iff F E _).mp
      rw [map_mul, map_mul, map_inv, hy]
      rw [show (z * k)⁻¹ * B γ * (z * k) = k⁻¹ * (z⁻¹ * B γ * z) * k by group]
      exact (KE).mul_mem ((KE).mul_mem ((KE).inv_mem hk) hzΓ) hk
    let a : OF := ⟨DoubleCoset.mk (glCentralizer γ) KF y,
      (compactOpenTwistedDoubleCosets_mk_iff (MonoidHom.id GF) γ KFo (fun _ h => h) y).mpr hyΓ⟩
    refine ⟨a, Subtype.ext ?_⟩
    change sphericalDoubleCosetMap F E hσ hγ s hsN (DoubleCoset.mk (glCentralizer γ) KF y) = d.val
    rw [sphericalDoubleCosetMap_mk, hy, ← mul_assoc, hz]
    exact (DoubleCoset.mk_mul_mem ⟨k, hk⟩ d.val.out).trans (DoubleCoset.out_eq' d.val)

@[simp] theorem sphericalOrbitalCosetsEquiv_apply_val (hσ : IsCyclicAlgebra σ l)
    (he : E.canonicalTopologicalData.ramificationIndex = F.canonicalTopologicalData.ramificationIndex)
    (hγ : IsRegularSemisimple γ) (s u : GE) (hs : s⁻¹ * δ * θ s = u)
    (hsN : s⁻¹ * cyclicNorm σ l δ * s = B γ) (hu : cyclicNorm σ l u = B γ)
    (huInt : ∀ z : GE, z⁻¹ * B γ * z ∈ KE → z⁻¹ * u * z ∈ KE) (d : OF) :
    (sphericalOrbitalCosetsEquiv F E hσ he hγ s u hs hsN hu huInt d).val =
      DoubleCoset.mk (sigmaCentralizer σ (r + 1) δ) KE (s * B d.val.out) := by
  change sphericalDoubleCosetMap F E hσ hγ s hsN d.val = _
  have hd : DoubleCoset.mk (glCentralizer γ) KF d.val.out = d.val := DoubleCoset.out_eq' _
  exact (congrArg (sphericalDoubleCosetMap F E hσ hγ s hsN) hd.symm).trans
    (sphericalDoubleCosetMap_mk F E hσ hγ s hsN d.val.out)

end Langlands.BaseChange
