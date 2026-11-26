import Langlands.Global.AdelicIntertwiningAdjunctionQuotient

/-! # Iwasawa integration on an unfolded quotient -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Topology Set
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.AdelicGroupPoints.ParabolicIwasawaMeasure

open Langlands.GroupScheme
open LeftCosetSpace

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
  (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P)
  [IsClosedImmersion (iU ≫ p).hom.hom.left] (l : M ⟶ P)
  [IsIso (subgroupMultiplication l iU)] (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
  {K : Subgroup (AdelicGroupPoints F G)} (hKc : IsCompact (K : Set (AdelicGroupPoints F G)))
  (μM : Measure (AdelicGroupPoints F M)) [μM.IsHaarMeasure]
  [hN : IsClosed (AdelicSubgroupPoints.adelicPoints F G
    (SubgroupFunctor.range (iU ≫ p)) : Set (AdelicGroupPoints F G))]

local notation "Gₐ" => (AdelicGroupPoints F G)
local notation "Mₐ" => (AdelicGroupPoints F M)
local notation "S" => (SubgroupFunctor.range (iU ≫ p))
local notation "N" => (AdelicSubgroupPoints.adelicPoints F G S)
local instance : LocallyCompactSpace N := hN.locallyCompactSpace
local instance : PolishSpace N := hN.polishSpace
local notation "μN" => (AdelicSubgroupPoints.normalizedHaarMeasure F G S)
local notation "μK" => (compactHaarProbability F G K hKc)
local notation "mG" => (fun m => map F P G p (map F M P l m))
local notation "Dm" => (fundamentalDomain (rationalSubgroup F M) (isDiscrete_rationalSubgroup F M))

/-- The Iwasawa integrand with the radical modulo the prescribed discrete subgroup. -/
def unfoldedIntegrand (Δ : Subgroup N) (f : Gₐ → ℂ) (z : (LeftCosetSpace Δ × Mₐ) × K) : ℂ :=
  (inverseModulus l z.1.2 : ℂ) * f ((z.1.1.out : N).val * mG z.1.2 * z.2.val)

theorem measurable_unfoldedIntegrand (Δ : Subgroup N) (hΔd : IsDiscrete (Δ : Set N))
    (f : Gₐ → ℂ) (hf : Measurable f) (hInv : ∀ u ∈ Δ, ∀ g, f (u.val * g) = f g) :
    Measurable (unfoldedIntegrand (K := K) p iU l Δ f) := by
  let u : N →* Gₐ := Subgroup.subtype N
  let k : K → Gₐ := Subtype.val
  let m : Mₐ → Gₐ := mG
  have hm : Measurable m := (map F P G p).measurable.comp (map F M P l).measurable
  have hMeas := measurable_radicalQuotient_product hΔd u m k measurable_subtype_coe hm
    measurable_subtype_coe f hf (fun d hd g => hInv d hd g)
  apply Measurable.mul _ hMeas
  exact Complex.continuous_ofReal.measurable.comp ((continuous_inverseModulus l).measurable.comp
    (measurable_snd.comp measurable_fst))

include hU in
set_option maxHeartbeats 800000 in
/-- The unfolded quotient integral and its absolute integrability in Iwasawa coordinates. -/
theorem unfoldDiscreteIwasawa (hμM : IsIwasawaCompatibleMeasure K hKc p iU l μM)
    (Γ : Subgroup Gₐ) (hΓr : Γ ≤ rationalSubgroup F G)
    (hΓp : Γ ≤ (map F P G p).toMonoidHom.range) (hLevi : ∀ m ∈ rationalSubgroup F M, mG m ∈ Γ)
    (Δ : Subgroup N) (hΔd : IsDiscrete (Δ : Set N)) (hΔ : ∀ u : N, u ∈ Δ ↔ u.val ∈ Γ)
    (f : Gₐ → ℂ) (hf : Continuous f) (hInv : ∀ d ∈ Γ, ∀ g, f (d * g) = f g) :
    let hΓ := (isDiscrete_rationalSubgroup F G).mono hΓr
    let μΓ := discreteQuotientMeasure Γ hΓ (Measure.haar : Measure Gₐ)
    let μI := (Measure.prod (discreteQuotientMeasure Δ hΔd μN) (μM.restrict Dm)).prod μK
    (Integrable (fun z : LeftCosetSpace Γ => f z.out) μΓ ↔
        Integrable (unfoldedIntegrand (K := K) p iU l Δ f) μI) ∧
      (∫ z : LeftCosetSpace Γ, f z.out ∂μΓ) = ∫ z, unfoldedIntegrand p iU l Δ f z ∂μI := by
  intro hΓ μΓ μI
  let B : LeftCosetSpace Γ → ℂ := fun z => f z.out
  have hB : Measurable B := measurable_out_of_invariant Γ hf.measurable hInv
  let Dn := fundamentalDomain Δ hΔd
  let d (m : Mₐ) := ENNReal.ofReal (inverseModulus l m)
  have hd : Measurable d := ENNReal.measurable_ofReal.comp (continuous_inverseModulus l).measurable
  let ν := ((Measure.prod (Measure.restrict μN Dn) (μM.restrict Dm)).prod μK)
  let νd := (Measure.prod (Measure.restrict μN Dn) ((μM.withDensity d).restrict Dm)).prod μK
  let : SFinite (Measure.restrict μN Dn) := inferInstanceAs (SFinite (Measure.restrict
    (AdelicSubgroupPoints.quotientMassNormalizer F G S • (Measure.haar : Measure N)) Dn))
  let : SFinite (μM.restrict Dm) := inferInstance
  let : SFinite μK := inferInstance
  have hνd : νd = ν.withDensity (fun z : (N × Mₐ) × K => d z.1.2) := by
    dsimp only [νd, ν]
    have hd2 : Measurable (fun z : N × Mₐ => d z.2) := hd.comp measurable_snd
    rw [restrict_withDensity (measurableSet_fundamentalDomain _ _),
      prod_withDensity_right hd, prod_withDensity_left hd2]
  let T : (N × Mₐ) × K → Gₐ := fun z => z.1.1.val * mG z.1.2 * z.2.val
  have hT : Continuous T := by
    dsimp only [T]
    fun_prop
  have hQ : Measure.map (mk Γ ∘ T) νd = μΓ :=
    (map_iwasawaDiscreteProduct p iU l hU μM hKc hμM Γ hΓr hΓp hLevi Δ hΔ).symm
  let ψ : (N × Mₐ) × K → (LeftCosetSpace Δ × Mₐ) × K := Prod.map (Prod.map (mk Δ) id) id
  have hψ : MeasurePreserving ψ ν μI := by
    let zmap := show MeasurePreserving (mk Δ) (Measure.restrict μN Dn) (discreteQuotientMeasure Δ hΔd μN) from
      ⟨measurable_mk Δ, rfl⟩
    exact (zmap.prod (MeasurePreserving.id _)).prod (MeasurePreserving.id _)
  have hFi (z : (N × Mₐ) × K) : unfoldedIntegrand (K := K) p iU l Δ f (ψ z) =
      (inverseModulus l z.1.2 : ℂ) * f (T z) := by
    change (inverseModulus l z.1.2 : ℂ) * f ((Quotient.out (mk Δ z.1.1) : N).val * mG z.1.2 * z.2.val) = _
    congr 1
    apply out_mk_of_invariant Δ (fun u : N => f (u.val * mG z.1.2 * z.2.val))
    intro x hx u
    change f ((x.val * u.val) * mG z.1.2 * z.2.val) = _
    simpa only [mul_assoc] using hInv x.val ((hΔ _).1 hx) (u.val * mG z.1.2 * z.2.val)
  let H := unfoldedIntegrand (K := K) p iU l Δ f
  have hFc : Measurable H := measurable_unfoldedIntegrand (K := K) p iU l Δ hΔd f
    hf.measurable (fun u hu g => hInv u.val ((hΔ u).1 hu) g)
  let wt : (N × Mₐ) × K → ℝ := fun z => inverseModulus l z.1.2
  have hwt : Measurable wt := (continuous_inverseModulus l).measurable.comp
    (measurable_snd.comp measurable_fst)
  have hΓmap : MeasurePreserving (mk Γ ∘ T) (ν.withDensity fun z => ENNReal.ofReal (wt z)) μΓ :=
    ⟨(measurable_mk Γ).comp hT.measurable, hνd ▸ hQ⟩
  exact integrable_integral_of_weighted_pushforwards ν μΓ μI _ ψ wt hwt
    (fun _ => norm_nonneg _) hΓmap hψ B H hB hFc (fun z => by
      change (inverseModulus l z.1.2 : ℂ) * (B ∘ (mk Γ ∘ T)) z = H (ψ z)
      rw [show B ∘ (mk Γ ∘ T) = f ∘ T from funext fun x =>
        out_mk_of_invariant Γ f hInv (T x)]
      exact (hFi z).symm)

end Langlands.Global.AdelicGroupPoints.ParabolicIwasawaMeasure
