import Langlands.BaseChange.NormCentralizer
import Langlands.BaseChange.RegularCoefficientSlice
import Langlands.BaseChange.RegularOrbitalProfilesFromCharts
import Langlands.BaseChange.TwistedNearConjugator
import Langlands.BaseChange.TwistedOrbitChart
import Langlands.Galois.Local.AbsoluteDefinitions

noncomputable section

open Filter Set Topology

namespace Langlands.BaseChange

open Langlands.JacquetLanglands Langlands.QuotientIntegration Langlands.TraceFormula
open SigmaLiftCharacterIdentity (coefficients continuous_baseChange)

universe u v

private def restrictOrbitalChart {G B : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [TopologicalSpace B]
    {p : G → B} {θ : G →* G} {V : Set B} {R : Set G} {H : Subgroup G}
    (hV : IsOpen V) (hR : p ⁻¹' V ⊆ R) (s : V → G) (hp_s : ∀ b, p (s b) = b.val)
    (hH : ∀ b, twistedCentralizer θ (s b) = H)
    (e : V × LeftQuotient H ≃ₜ (p ⁻¹' V : Set G))
    (he : ∀ b g, (e (b, leftQuotientMap H g) : G) = twistedConj θ g (s b))
    (hep : ∀ z, p (e z) = z.1.val) :
    RegularOrbitalChart θ (fun r : R => p r.val) := by
  let eR : (p ⁻¹' V : Set G) ≃ₜ ((fun r : R => p r.val) ⁻¹' V : Set R) :=
    { toFun := fun x => ⟨⟨x.val, hR x.property⟩, x.property⟩
      invFun := fun x => ⟨x.val.val, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  exact
    { parameters := V
      isOpen := hV
      centralizer := H
      representative := fun b => ⟨s b, hR (show p (s b) ∈ V from (hp_s b).symm ▸ b.property)⟩
      chart := e.trans eR
      stabilizer := hH
      parameter := hep
      apply_mk := he }

section Algebra

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E]
variable {σ : E ≃ₐ[F] E} {l n : ℕ}

private theorem glCentralizer_eq_of_regular_commute {a b : GeneralLinear n F}
    (ha : IsRegularSemisimple a) (hb : IsRegularSemisimple b) (hab : Commute a b) :
    glCentralizer a = glCentralizer b := by
  have hsub {x y : GeneralLinear n F} (hx : IsRegularSemisimple x) (hxy : Commute x y) :
      glCentralizer x ≤ glCentralizer y := by
    intro g hg
    rw [glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    have hy : y ∈ glCentralizer x := by
      rw [glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      exact hxy.symm.eq
    exact congrArg Subtype.val (glCentralizer_mul_comm hx ⟨g, hg⟩ ⟨y, hy⟩)
  exact le_antisymm (hsub ha hab) (hsub hb hab.symm)

private theorem commute_norm_of_rational (hσ : σ ^ l = 1)
    {δ : GeneralLinear n E} {γ : GeneralLinear n F}
    (hnorm : cyclicNorm σ l δ = baseChange F E n γ) :
    Commute δ (baseChange F E n γ) := by
  have h := entrywiseAut_cyclicNorm σ l δ
  rw [hnorm, entrywiseAut_baseChange, hσ, entrywiseAut_one_apply] at h
  exact eq_inv_mul_iff_mul_eq.mp (by simpa only [mul_assoc] using h)

private theorem cyclicNorm_mul_rational (σ : E ≃ₐ[F] E) (l : ℕ)
    (δ : GeneralLinear n E) (t : GeneralLinear n F) (ht : Commute δ (baseChange F E n t)) :
    cyclicNorm σ l (δ * baseChange F E n t) =
      cyclicNorm σ l δ * baseChange F E n t ^ l := by
  let b := baseChange F E n t
  change cyclicNorm σ l (δ * b) = cyclicNorm σ l δ * b ^ l
  induction l with
  | zero => simp
  | succ l ih =>
    have hfixed : entrywiseAut (σ ^ l) n b = b := entrywiseAut_baseChange _ t
    have hcomm : Commute (entrywiseAut (σ ^ l) n δ) b := by
      simpa only [b, entrywiseAut_baseChange] using ht.map (entrywiseAut (σ ^ l) n)
    calc
      _ = cyclicNorm σ l δ * b ^ l * (entrywiseAut (σ ^ l) n δ * b) := by
        rw [cyclicNorm_succ, ih, map_mul, hfixed]
      _ = cyclicNorm σ l δ * entrywiseAut (σ ^ l) n δ * (b ^ l * b) :=
        (hcomm.symm.pow_left l).mul_mul_mul_comm _ _
      _ = _ := by rw [cyclicNorm_succ, pow_succ]

private theorem normCoefficients_one (γ : GeneralLinear n F) :
    normCoefficients (isCyclicAlgebra_one (F := F)) γ = coefficients γ := by
  apply normCoefficients_eq_of_associated
  have hb : baseChange F F n γ = γ := by
    ext i j
    rfl
  refine ⟨1, ?_⟩
  rw [show (1 : ℕ) = 0 + 1 by rfl, cyclicNorm_succ, cyclicNorm_zero, pow_zero,
    entrywiseAut_one_apply, inv_one, one_mul, one_mul, mul_one, hb]

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]

private theorem sigmaCentralizer_eq_map_of_norm_eq (hcyc : IsCyclicAlgebra σ l)
    {δ : GeneralLinear n E} {γ : GeneralLinear n F} (hγ : IsRegularSemisimple γ)
    (hnorm : cyclicNorm σ l δ = baseChange F E n γ) :
    sigmaCentralizer σ n δ = (glCentralizer γ).map (baseChange F E n) := by
  have h : (1 : GeneralLinear n E)⁻¹ * cyclicNorm σ l δ * 1 = baseChange F E n γ := by
    simpa only [inv_one, one_mul, mul_one] using hnorm
  let e := normCentralizerEquiv hcyc hγ 1 h
  have he (t : glCentralizer γ) : (e t).val = baseChange F E n t.val := by
    rw [normCentralizerEquiv_apply_val, one_mul, inv_one, mul_one]
  ext c
  constructor
  · intro hc
    obtain ⟨t, ht⟩ := e.surjective ⟨c, hc⟩
    exact ⟨t.val, t.property, by rw [← he t, ht]⟩
  · rintro ⟨t, ht, rfl⟩
    rw [← he ⟨t, ht⟩]
    exact (e ⟨t, ht⟩).property

end Algebra

section LocalField

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E]
  [IsTopologicalRing E] [IsModuleTopology F E]
variable {σ : E ≃ₐ[F] E} {l n : ℕ}

/-- Every twisted regular coefficient is contained in an open product chart. -/
theorem exists_twistedRegularOrbitalChart (hcyc : IsCyclicAlgebra σ l)
    (d : {δ : GeneralLinear n E | IsSigmaRegular σ l δ}) :
    ∃ c : RegularOrbitalChart (entrywiseAut σ n).toMonoidHom
        (fun δ : {δ : GeneralLinear n E | IsSigmaRegular σ l δ} => normCoefficients hcyc δ.val),
      normCoefficients hcyc d.val ∈ c.parameters := by
  let : NontriviallyNormedField F := LocalGalois.localNormedField F
  let := LocalGalois.localNormedField_complete F
  let : Module.Finite F E := hcyc.1
  let R := {δ : GeneralLinear n E | IsSigmaRegular σ l δ}
  let p := normCoefficients (n := n) hcyc
  let θ := (entrywiseAut σ n).toMonoidHom
  obtain ⟨γ, ⟨x, hx⟩, hγ⟩ := d.property
  let δ := twistedConj θ x d.val
  have hnorm : cyclicNorm σ l δ = baseChange F E n γ := by
    change cyclicNorm σ l (x⁻¹ * d.val * entrywiseAut σ n x) = _
    rw [cyclicNorm_twistedConj, hcyc.pow_eq_one, entrywiseAut_one_apply, hx]
  obtain ⟨V₀, hγV₀, t₀, hV₀, ht₀, -, hpoly₀, hcoeff₀⟩ :=
    regularCoefficientSlice F n l γ hcyc.pos hγ
  let V := V₀ ∩ {b : Fin n → F | (polynomialOfCoefficients b).Separable}
  have hV : IsOpen V := hV₀.inter (isOpen_separable_polynomialOfCoefficients n)
  have hdV : p d.val ∈ V := by
    change normCoefficients hcyc d.val ∈ V
    rw [normCoefficients_eq_of_associated hcyc (show IsNormAssociated σ l d.val γ from ⟨x, hx⟩)]
    exact ⟨hγV₀, (isRegularSemisimple_iff_separable_coefficients γ).mp hγ⟩
  let j : V → V₀ := fun b => ⟨b.val, b.property.1⟩
  let t : V → GeneralLinear n F := t₀ ∘ j
  let r : V → GeneralLinear n F := fun b => γ * t b ^ l
  let s : V → GeneralLinear n E := fun b => δ * baseChange F E n (t b)
  have hs : Continuous s := continuous_const.mul (continuous_baseChange.comp
    (ht₀.comp (continuous_subtype_val.subtype_mk _)))
  have hr (b : V) : IsRegularSemisimple (r b) :=
    (isRegularSemisimple_iff_separable_coefficients (r b)).mpr (by
      change (polynomialOfCoefficients (coefficients (γ * t₀ (j b) ^ l))).Separable
      rw [hcoeff₀]
      exact b.property.2)
  have hR : p ⁻¹' V ⊆ R := fun y hy =>
    (isSigmaRegular_iff_separable_normCoefficients hcyc y).mpr hy.2
  have hcomm (b : V) : Commute γ (t b) := by
    obtain ⟨c, hc⟩ := hpoly₀ (j b)
    apply Units.ext
    change Commute γ.val (t₀ (j b)).val
    rw [hc]
    exact (Commute.one_right _).add_right (Commute.sum_right _ _ _ fun i _ =>
      ((Commute.refl γ.val).pow_right (i : ℕ)).smul_right (c i))
  have hnorm_s (b : V) : cyclicNorm σ l (s b) = baseChange F E n (r b) := by
    have hcomm' : Commute δ (baseChange F E n (t b)) :=
      commute_of_regular_baseChange hγ (commute_norm_of_rational hcyc.pow_eq_one hnorm)
        ((hcomm b).symm.map (baseChange F E n))
    change cyclicNorm σ l (δ * baseChange F E n (t b)) = baseChange F E n (γ * t b ^ l)
    rw [cyclicNorm_mul_rational σ l δ (t b) hcomm', hnorm, map_mul, map_pow]
  have hp_s (b : V) : p (s b) = b.val := by
    have ha : IsNormAssociated σ l (s b) (r b) := ⟨1, by simpa using hnorm_s b⟩
    exact (normCoefficients_eq_of_associated hcyc ha).trans (hcoeff₀ (j b))
  let H := (glCentralizer γ).map (baseChange F E n)
  have hH (b : V) : twistedCentralizer θ (s b) = H := by
    have hc : Commute γ (r b) := Commute.mul_right (Commute.refl γ) ((hcomm b).pow_right l)
    change sigmaCentralizer σ n (s b) = (glCentralizer γ).map _
    rw [sigmaCentralizer_eq_map_of_norm_eq hcyc (hr b) (hnorm_s b),
      glCentralizer_eq_of_regular_commute hγ (hr b) hc]
  have hp : Continuous p := continuous_normCoefficients hcyc
  let D := (p ⁻¹' V : Set (GeneralLinear n E))
  let parameter : D → V := fun y => ⟨p y.val, y.property⟩
  have hparameter : Continuous parameter := (hp.comp continuous_subtype_val).subtype_mk _
  have horbit (y : D) : ∃ g : GeneralLinear n E, twistedConj θ g (s (parameter y)) = y.val :=
    exists_twistedConj_of_regular_normCoefficients_eq hcyc
      (hR (show p (s (parameter y)) ∈ V from
        (hp_s (parameter y)).symm ▸ (parameter y).property)) (hp_s (parameter y))
  have hlift (b : V) (W : Set (GeneralLinear n E)) (hW : W ∈ 𝓝 (1 : GeneralLinear n E)) :
      ∀ᶠ y : D in 𝓝 (⟨s b, show p (s b) ∈ V from (hp_s b).symm ▸ b.property⟩ : D),
        ∃ g ∈ W, twistedConj θ g (s (parameter y)) = y.val := by
    let y₀ : D := ⟨s b, show p (s b) ∈ V from (hp_s b).symm ▸ b.property⟩
    have hy₀ : parameter y₀ = b := Subtype.ext (hp_s b)
    have hsT : Tendsto (s ∘ parameter) (𝓝 y₀) (𝓝 (s b)) := by
      have h := (hs.comp hparameter).continuousAt (x := y₀).tendsto
      simpa only [Function.comp_def, hy₀] using h
    have hyT : Tendsto (Subtype.val : D → GeneralLinear n E) (𝓝 y₀) (𝓝 (s b)) :=
      continuous_subtype_val.continuousAt
    obtain ⟨v, hv⟩ := regularCyclicBasis F n (r b).val (hr b)
    have hvE : IsUnit (cyclicBasisMatrix (cyclicNorm σ l (s b)).val (algebraMap F E ∘ v)) := by
      rw [hnorm_s]
      change IsUnit (cyclicBasisMatrix ((r b).val.map (algebraMap F E)) (algebraMap F E ∘ v))
      rw [← cyclicBasisMatrix_map]
      exact hv.map (algebraMap F E).mapMatrix
    have he : ∀ᶠ y : D in 𝓝 y₀,
        (cyclicNorm σ l ((s ∘ parameter) y)).val.charpoly = (cyclicNorm σ l y.val).val.charpoly :=
      Eventually.of_forall fun y => charpoly_norm_eq_of_normCoefficients_eq hcyc (hp_s (parameter y))
    obtain ⟨g, hg, hgy⟩ :=
      exists_tendsto_twistedConjugator hcyc.pow_eq_one hcyc.pos.ne' hsT hyT hvE he
    filter_upwards [hg.eventually hW, hgy] with y hy hy'
    exact ⟨g y, hy, hy'⟩
  obtain ⟨e, he, hep⟩ := exists_twistedOrbitChart (GeneralLinear n E) (Fin n → F)
    θ (continuous_entrywiseAut σ n) p hp (normCoefficients_twistedConj hcyc)
    V H s hs hp_s hH horbit hlift
  exact ⟨restrictOrbitalChart hV hR s hp_s hH e he hep, hdV⟩

/-- Every ordinary regular coefficient is contained in an open product chart. -/
theorem exists_ordinaryRegularOrbitalChart
    (a : {γ : GeneralLinear n F | IsRegularSemisimple γ}) :
    ∃ c : RegularOrbitalChart (MonoidHom.id (GeneralLinear n F))
        (fun γ : {γ : GeneralLinear n F | IsRegularSemisimple γ} => coefficients γ.val),
      coefficients a.val ∈ c.parameters := by
  have hθ : (entrywiseAut (1 : F ≃ₐ[F] F) n).toMonoidHom = MonoidHom.id _ :=
    MonoidHom.ext entrywiseAut_one_apply
  have hreg (γ : GeneralLinear n F) : IsSigmaRegular (1 : F ≃ₐ[F] F) 1 γ ↔
      IsRegularSemisimple γ := by
    rw [isSigmaRegular_iff_separable_normCoefficients (isCyclicAlgebra_one (F := F)),
      normCoefficients_one, ← isRegularSemisimple_iff_separable_coefficients]
  have hR : {γ : GeneralLinear n F | IsSigmaRegular (1 : F ≃ₐ[F] F) 1 γ} =
      {γ : GeneralLinear n F | IsRegularSemisimple γ} := Set.ext hreg
  have hp : normCoefficients (n := n) (isCyclicAlgebra_one (F := F)) =
      coefficients := funext normCoefficients_one
  have hcharts := exists_twistedRegularOrbitalChart (n := n) (isCyclicAlgebra_one (F := F))
  rw [hθ, hp, hR] at hcharts
  exact hcharts a

end LocalField

/-- The regular coefficient maps on the ordinary and twisted groups admit the product
charts used by the orbital-profile construction. -/
def RegularTransferChartsStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] (n : ℕ),
    (∀ a : {γ : GeneralLinear n F | IsRegularSemisimple γ},
      ∃ c : RegularOrbitalChart (MonoidHom.id (GeneralLinear n F))
          (fun γ : {γ : GeneralLinear n F | IsRegularSemisimple γ} => coefficients γ.val),
        coefficients a.val ∈ c.parameters) ∧
    ∀ (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E]
      [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l : ℕ)
      (hcyc : IsCyclicAlgebra σ l) (d : {δ : GeneralLinear n E | IsSigmaRegular σ l δ}),
      ∃ c : RegularOrbitalChart (entrywiseAut σ n).toMonoidHom
          (fun δ : {δ : GeneralLinear n E | IsSigmaRegular σ l δ} => normCoefficients hcyc δ.val),
        normCoefficients hcyc d.val ∈ c.parameters

theorem regularTransferCharts : RegularTransferChartsStatement.{u, v} := by
  intro F _ _ _ _ _ n
  exact ⟨exists_ordinaryRegularOrbitalChart,
    fun _ _ _ _ _ _ _ _ hcyc => exists_twistedRegularOrbitalChart hcyc⟩

end Langlands.BaseChange
