import Langlands.Analysis.Local.QuotientMeasureEquiv
import Langlands.BaseChange.ConcordanceConjugation
import Langlands.BaseChange.ExactNormAssociatedMeasure
import Langlands.BaseChange.ExactNormCentralizer
import Langlands.BaseChange.SphericalHeckeFieldPullback

/-! The spherical fundamental lemma for a cyclic extension of degree one. -/

noncomputable section

namespace Langlands.BaseChange

open Langlands.JacquetLanglands Langlands.QuotientIntegration
open Langlands.TraceFormula Langlands.Unramified MeasureTheory

universe u v w

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel
attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

local instance degreeOneGlLocallyCompact {p : ℕ} [Fact p.Prime] (K : PadicField.{w} p) (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n K.Carrier) :=
  LocalFieldTopology.generalLinear_locallyCompactSpace K.Carrier n

local instance degreeOneGlSecondCountable {p : ℕ} [Fact p.Prime] (K : PadicField.{w} p) (n : ℕ) :
    SecondCountableTopology (GeneralLinear n K.Carrier) :=
  LocalFieldTopology.generalLinear_secondCountableTopology K.Carrier n

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  {σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier}

omit [IsScalarTower (Padic p) F.Carrier E.Carrier] in
private theorem cyclicNorm_degreeOne {n : ℕ} (δ : GeneralLinear n E.Carrier) :
    cyclicNorm σ 1 δ = δ := by
  rw [show (1 : ℕ) = 0 + 1 by rfl, cyclicNorm_succ, cyclicNorm_zero, pow_zero,
    entrywiseAut_one_apply, one_mul]

private theorem degreeOne_concordAt_of_exactNorm (r : ℕ)
    (hcyc : IsCyclicAlgebra σ 1) (e : F.Carrier ≃ₐ[Padic p] E.Carrier)
    (he : ∀ a, e a = algebraMap F.Carrier E.Carrier a)
    (φ : SphericalHeckeAlgebra E r)
    {δ : GeneralLinear (r + 1) E.Carrier} {γ : GeneralLinear (r + 1) F.Carrier}
    (hγ : IsRegularSemisimple γ) (hn : cyclicNorm σ 1 δ = baseChange F.Carrier E.Carrier (r + 1) γ) :
    ConcordAt σ 1 (sphericalHaar F r) (sphericalHaar E r) ⇑φ
      ⇑(sphericalHeckeFieldPullback F E e r φ) δ γ := by
  let : Module.Finite F.Carrier E.Carrier := hcyc.1
  let : IsModuleTopology F.Carrier E.Carrier := isModuleTopology_padic_extension F E
  let κ := padicMatrixFieldEquiv F E e (r + 1)
  have hκ (g : GeneralLinear (r + 1) F.Carrier) :
      κ g = baseChange F.Carrier E.Carrier (r + 1) g := by
    apply Units.ext
    apply Matrix.ext
    exact fun i j => he (g i j)
  have hδ : κ γ = δ := by
    rw [hκ, ← hn, cyclicNorm_degreeOne F E]
  have hσ : σ = 1 := by simpa only [pow_one] using hcyc.pow_eq_one
  have hθ (g : GeneralLinear (r + 1) E.Carrier) : entrywiseAut σ (r + 1) g = g := by
    rw [hσ, entrywiseAut_one_apply]
  have hH (g : GeneralLinear (r + 1) F.Carrier) :
      κ g ∈ sigmaCentralizer σ (r + 1) δ ↔ g ∈ glCentralizer γ := by
    rw [mem_sigmaCentralizer, hθ, ← hδ]
    change (κ g)⁻¹ * κ γ * κ g = κ γ ↔ g⁻¹ * γ * g = γ
    rw [← map_inv, ← map_mul, ← map_mul, κ.injective.eq_iff]
  let eQ : LeftQuotient (glCentralizer γ) ≃ₜ LeftQuotient (sigmaCentralizer σ (r + 1) δ) :=
    Homeomorph.Quotient.congr κ.toHomeomorph (by
      intro a b
      rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
      change b * a⁻¹ ∈ glCentralizer γ ↔ κ b * (κ a)⁻¹ ∈ sigmaCentralizer σ (r + 1) δ
      rw [← map_inv, ← map_mul, hH])
  let eH := exactNormCentralizerEquiv hcyc hγ hn
  have heH (x : glCentralizer γ) : (eH x).val = κ x.val := by
    rw [hκ, show (eH x).val = baseChange F.Carrier E.Carrier (r + 1) x.val from
      exactNormCentralizerEquiv_apply_val hcyc hγ hn x]
  intro μδ _ _ μγ _ _ νδ νγ hνδ hνγ hassoc
  have hμ := (isAssociatedMeasure_iff_map_exactNormCentralizerEquiv hcyc hγ hn μδ μγ).1 hassoc
  change μδ = Measure.map eH μγ at hμ
  subst μδ
  have hP := padicMatrixFieldEquiv_measurePreserving F E e r
  have hν :
      IsCompatible (sigmaCentralizer σ (r + 1) δ) (sphericalHaar E r)
        (Measure.map eH μγ) (Measure.map eQ νγ) := by
    have hmap : Measure.map κ (sphericalHaar F r) = sphericalHaar E r := hP.map_eq
    simpa only [hmap] using isCompatible_map_equiv κ _ _ eH heH eQ (fun _ => rfl)
      (sphericalHaar F r) μγ νγ hνγ
  have hcδ : IsClosed (sigmaCentralizer σ (r + 1) δ : Set (GeneralLinear (r + 1) E.Carrier)) :=
    isClosed_twistedCentralizer (entrywiseAut σ (r + 1))
      (by simpa only [hθ] using (continuous_id' : Continuous (fun x : GeneralLinear (r + 1) E.Carrier => x))) δ
  let : LocallyCompactSpace (sigmaCentralizer σ (r + 1) δ) := hcδ.locallyCompactSpace
  let : SecondCountableTopology (sigmaCentralizer σ (r + 1) δ) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have hνeq : νδ = Measure.map eQ νγ := by
    have h := hνδ.eq_smul_of_subgroup_smul hcδ hν (c := 1) (one_smul ..).symm
    simpa only [one_smul] using h
  let fδ := twistedOrbitFunction (entrywiseAut σ (r + 1)) δ (fun x => φ x)
  let fγ := twistedOrbitFunction (MonoidHom.id (GeneralLinear (r + 1) F.Carrier)) γ
    (fun x => sphericalHeckeFieldPullback F E e r φ x)
  change (∫ q, fδ q ∂νδ) = ∫ q, fγ q ∂νγ
  rw [hνeq]
  calc
    _ = ∫ q, fδ (eQ q) ∂νγ := integral_map_equiv eQ.toMeasurableEquiv fδ
    _ = _ := by
      congr 1
      funext q
      induction q using Quotient.inductionOn with
      | h g =>
        change φ ((κ g)⁻¹ * δ * entrywiseAut σ (r + 1) (κ g)) =
          sphericalHeckeFieldPullback F E e r φ (g⁻¹ * γ * g)
        rw [hθ, ← hδ, sphericalHeckeFieldPullback_apply, map_mul, map_mul, map_inv]

/-- The degree-one restriction of the spherical fundamental lemma, on the two
original p-adic carriers and for every positive matrix rank. -/
def DegreeOneFundamentalLemmaStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) (r : ℕ),
    IsCyclicAlgebra σ 1 →
    ∀ b : SphericalHeckeAlgebra E r →ₐ[ℂ] SphericalHeckeAlgebra F r,
      IsUnramifiedBaseChangeHom F E 1 r b →
      ∀ φ : SphericalHeckeAlgebra E r,
        AreConcordant σ 1 (sphericalHaar F r) (sphericalHaar E r) ⇑φ ⇑(b φ)

theorem degreeOneFundamentalLemma : DegreeOneFundamentalLemmaStatement.{u, v} := by
  intro p _ F E _ _ σ r hcyc b hb φ
  have hσ : σ = 1 := by simpa only [pow_one] using hcyc.pow_eq_one
  let e : F.Carrier ≃ₐ[Padic p] E.Carrier :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom (Padic p) F.Carrier E.Carrier)
      ⟨(algebraMap F.Carrier E.Carrier).injective, fun x => hcyc.2.2.2.2 x (by rw [hσ]; rfl)⟩
  have he (x : F.Carrier) : e x = algebraMap F.Carrier E.Carrier x := rfl
  rw [(isUnramifiedBaseChangeHom_one_iff F E e r).1 hb]
  constructor
  · intro γ _ hnot
    exfalso
    apply hnot
    refine ⟨baseChange F.Carrier E.Carrier (r + 1) γ, 1, ?_⟩
    rw [inv_one, one_mul, mul_one, cyclicNorm_degreeOne F E]
  · intro δ γ _ hγ
    refine concordAt_of_conj_of_cyclicNorm_eq hcyc.pow_eq_one
      (continuous_baseChange_padic F E (r + 1)).measurable δ γ 1 ?_
    intro δ' hδ'
    simp only [inv_one, one_mul, mul_one] at hδ' ⊢
    exact degreeOne_concordAt_of_exactNorm F E r hcyc e he φ hγ hδ'

end Langlands.BaseChange
