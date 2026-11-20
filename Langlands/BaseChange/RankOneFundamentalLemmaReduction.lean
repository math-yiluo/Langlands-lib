import Langlands.BaseChange.CyclicNormDeterminant
import Langlands.BaseChange.RankOneHecke
import Langlands.BaseChange.UnitFundamentalLemmaStatement
import Langlands.LocalFactor.DeligneHenniartTopLayerOrders

/-! # The rank-one fundamental lemma from the unit and Satake statements -/

noncomputable section

namespace Langlands.BaseChange

open Correspondence Langlands.Unramified Langlands.TraceFormula
open Langlands.QuotientIntegration MeasureTheory

universe u v

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel
attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} {E : PadicField.{v} p}
variable [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
variable {σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier} {l : ℕ}

/-- For rank one the scalar norm criterion is the matrix norm criterion. -/
theorem isNorm_rankOne_iff_dvd (hcyc : IsCyclicAlgebra σ l)
    (he : E.canonicalTopologicalData.ramificationIndex =
      F.canonicalTopologicalData.ramificationIndex) (γ : GeneralLinear 1 F.Carrier) :
    IsNorm σ l γ ↔ (l : ℤ) ∣ rankOneOrder F γ := by
  constructor
  · rintro ⟨δ, hδγ⟩
    exact ⟨rankOneOrder E δ, hδγ.ord_determinant_eq hcyc he⟩
  · intro hd
    let : FiniteDimensional F.Carrier E.Carrier := hcyc.1
    have hmem := LocalClassField.unramifiedNormMembership p F E F.canonicalTopologicalData
      E.canonicalTopologicalData he.symm (GeneralLinear.determinant γ)
    obtain ⟨a, ha⟩ := hmem.2 (by rwa [hcyc.2.1])
    let δ : GeneralLinear 1 E.Carrier := GeneralLinear.scalar a
    refine ⟨δ, 1, ?_⟩
    rw [inv_one, one_mul, mul_one]
    apply rankOne_determinant_injective
    apply Units.ext
    rw [hcyc.determinant_cyclicNorm]
    have hδ : GeneralLinear.determinant δ = a := by
      change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) a) = a
      rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_one]
    have ha' : Algebra.norm F.Carrier (a : E.Carrier) = (GeneralLinear.determinant γ : F.Carrier) :=
      congrArg (fun z : F.Carrierˣ => (z : F.Carrier)) ha
    rw [hδ, ha']
    exact (algebraMap F.Carrier E.Carrier).map_det
      (γ : Matrix (Fin 1) (Fin 1) F.Carrier)

private theorem rankOneOrder_twistedConj (x δ : GeneralLinear 1 E.Carrier) :
    rankOneOrder E (x⁻¹ * δ * entrywiseAut σ 1 x) = rankOneOrder E δ := by
  have hdet : (GeneralLinear.determinant (entrywiseAut σ 1 x) : E.Carrier) =
      σ (GeneralLinear.determinant x : E.Carrier) :=
    (σ.map_det (x : Matrix (Fin 1) (Fin 1) E.Carrier)).symm
  have h := LocalFactor.NonabelianSystem.DeligneHenniart.TopLayer.ord_algEquiv_apply
    E.canonicalTopologicalData σ (GeneralLinear.determinant x : E.Carrier)
  have horder : rankOneOrder E (entrywiseAut σ 1 x) = rankOneOrder E x := by
    unfold rankOneOrder
    rw [hdet, h]
  rw [rankOneOrder_mul, rankOneOrder_mul, rankOneOrder_inv, horder]
  omega

private theorem rankOne_twistedOrbitFunction_eq (φ : SphericalHeckeAlgebra E 0)
    (δ : GeneralLinear 1 E.Carrier) :
    twistedOrbitFunction (entrywiseAut σ 1) δ ⇑φ = fun _ => φ δ := by
  funext q
  refine Quotient.inductionOn q fun x => ?_
  rw [twistedOrbitFunction_mk]
  exact rankOne_eq_of_order E φ (rankOneOrder_twistedConj x δ)

private theorem rankOne_conj_eq {K : Type*} [Field K] (x g : GeneralLinear 1 K) :
    x⁻¹ * g * x = g := by
  rw [rankOne_mul_comm x⁻¹ g, mul_assoc, inv_mul_cancel, mul_one]

private theorem rankOne_orbitFunction_eq (f : GeneralLinear 1 F.Carrier → ℂ)
    (γ : GeneralLinear 1 F.Carrier) :
    twistedOrbitFunction (MonoidHom.id _) γ f = fun _ => f γ := by
  funext q
  refine Quotient.inductionOn q fun x => ?_
  rw [twistedOrbitFunction_mk, MonoidHom.id_apply, rankOne_conj_eq]

private theorem rankOne_sigmaOrbitalIntegral_eq (φ : SphericalHeckeAlgebra E 0)
    (δ : GeneralLinear 1 E.Carrier) (ν : Measure (LeftQuotient (sigmaCentralizer σ 1 δ))) :
    sigmaOrbitalIntegral σ 1 δ ν ⇑φ = ν.real Set.univ • φ δ := by
  rw [sigmaOrbitalIntegral, twistedOrbitalIntegral, rankOne_twistedOrbitFunction_eq, integral_const]

private theorem rankOne_orbitalIntegral_eq (f : GeneralLinear 1 F.Carrier → ℂ)
    (γ : GeneralLinear 1 F.Carrier) (ν : Measure (LeftQuotient (glCentralizer γ))) :
    orbitalIntegral γ ν f = ν.real Set.univ • f γ := by
  rw [orbitalIntegral, twistedOrbitalIntegral, rankOne_orbitFunction_eq (F := F), integral_const]

private theorem rankOne_glCentralizer_eq (γ : GeneralLinear 1 F.Carrier) :
    glCentralizer γ = glCentralizer (1 : GeneralLinear 1 F.Carrier) := by
  ext x
  rw [glCentralizer_eq_centralizer, glCentralizer_eq_centralizer,
    Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  exact iff_of_true (rankOne_mul_comm _ _) (rankOne_mul_comm _ _)

omit [IsScalarTower (Padic p) F.Carrier E.Carrier] in
private theorem rankOne_sigmaCentralizer_eq (δ : GeneralLinear 1 E.Carrier) :
    sigmaCentralizer σ 1 δ = sigmaCentralizer σ 1 (1 : GeneralLinear 1 E.Carrier) := by
  ext x
  rw [mem_sigmaCentralizer, mem_sigmaCentralizer, mul_one, rankOne_mul_comm x⁻¹ δ, mul_assoc]
  constructor
  · intro h
    apply mul_left_cancel (a := δ)
    simpa only [mul_one] using h
  · intro h
    rw [h, mul_one]

omit [IsScalarTower (Padic p) F.Carrier E.Carrier] in
private theorem isNormAssociated_one : IsNormAssociated σ l
    (1 : GeneralLinear 1 E.Carrier) (1 : GeneralLinear 1 F.Carrier) := by
  have h : cyclicNorm σ l (1 : GeneralLinear 1 E.Carrier) = 1 := by
    induction l with
    | zero => rfl
    | succ l ih => rw [cyclicNorm_succ, ih, map_one, mul_one]
  exact ⟨1, by simp [h]⟩

private theorem rankOne_regular_one :
    JacquetLanglands.IsRegularSemisimple (1 : GeneralLinear 1 F.Carrier) := by
  change (Matrix.charpoly (1 : Matrix (Fin 1) (Fin 1) F.Carrier)).Separable
  rw [Matrix.charpoly_one, Fintype.card_fin, pow_one, ← Polynomial.C_1]
  exact Polynomial.separable_X_sub_C

private theorem rankOne_quotientMass_eq (hunit : UnitFundamentalLemmaStatement.{u, v})
    (hcyc : IsCyclicAlgebra σ l) (he : E.canonicalTopologicalData.ramificationIndex =
      F.canonicalTopologicalData.ramificationIndex)
    (HF : Subgroup (GeneralLinear 1 F.Carrier)) (HE : Subgroup (GeneralLinear 1 E.Carrier))
    (hF : HF = glCentralizer (1 : GeneralLinear 1 F.Carrier))
    (hE : HE = sigmaCentralizer σ 1 (1 : GeneralLinear 1 E.Carrier))
    (μδ : Measure HE) [μδ.IsHaarMeasure] [μδ.IsMulRightInvariant]
    (μγ : Measure HF) [μγ.IsHaarMeasure] [μγ.IsMulRightInvariant]
    (νδ : Measure (LeftQuotient HE)) (νγ : Measure (LeftQuotient HF))
    (hνδ : IsCompatible HE (sphericalHaar E 0) μδ νδ)
    (hνγ : IsCompatible HF (sphericalHaar F 0) μγ νγ)
    (hmap : Measure.map (fun c : HE => (c : GeneralLinear 1 E.Carrier)) μδ =
      Measure.map (fun t : HF => baseChange F.Carrier E.Carrier 1 (t : GeneralLinear 1 F.Carrier)) μγ) :
    νδ.real Set.univ = νγ.real Set.univ := by
  subst HF
  subst HE
  have has : IsAssociatedMeasure σ l (1 : GeneralLinear 1 E.Carrier)
      (1 : GeneralLinear 1 F.Carrier) μδ μγ := by
    refine ⟨1, ?_, ?_⟩
    · obtain ⟨x, hx⟩ := isNormAssociated_one (σ := σ) (l := l)
      rw [rankOne_conj_eq] at hx ⊢
      exact hx
    · simpa only [inv_one, one_mul, mul_one] using hmap
  have hu := (hunit p F E σ l 0 hcyc he).2 1 1 isNormAssociated_one
    rankOne_regular_one μδ μγ νδ νγ hνδ hνγ has
  have hvalueF : (1 : SphericalHeckeAlgebra F 0) 1 = 1 := by
    rw [Hecke.HeckeAlgebra.Corner.one_apply, Set.indicator_of_mem (one_mem _), sphericalHaar_real_self]
    simp
  have hvalueE : (1 : SphericalHeckeAlgebra E 0) 1 = 1 := by
    rw [Hecke.HeckeAlgebra.Corner.one_apply, Set.indicator_of_mem (one_mem _), sphericalHaar_real_self]
    simp
  rw [rankOne_sigmaOrbitalIntegral_eq, rankOne_orbitalIntegral_eq (F := F),
    hvalueF, hvalueE, Complex.real_smul, Complex.real_smul, mul_one, mul_one] at hu
  exact_mod_cast hu

/-- The rank-one restriction of the full fundamental lemma follows from the
unit fundamental lemma and the Satake character statements. -/
def RankOneFundamentalLemmaReductionStatement : Prop :=
  UnitFundamentalLemmaStatement.{u, v} →
  SatakeCharacterStatement.{u} → SatakeCharacterStatement.{v} →
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) (l : ℕ),
    IsCyclicAlgebra σ l →
    E.canonicalTopologicalData.ramificationIndex =
      F.canonicalTopologicalData.ramificationIndex →
    ∀ b : SphericalHeckeAlgebra E 0 →ₐ[ℂ] SphericalHeckeAlgebra F 0,
      IsUnramifiedBaseChangeHom F E l 0 b →
      ∀ φ : SphericalHeckeAlgebra E 0,
        AreConcordant σ l (sphericalHaar F 0) (sphericalHaar E 0) ⇑φ ⇑(b φ)

theorem rankOneFundamentalLemmaReduction : RankOneFundamentalLemmaReductionStatement.{u, v} := by
  intro hunit hSatakeF hSatakeE p hp F E instFE hTower σ l hcyc he b hb φ
  constructor
  · intro γ _ hn μγ hμγ hrγ νγ hνγ
    have hndvd : ¬ (l : ℤ) ∣ rankOneOrder F γ := fun hd =>
      hn ((isNorm_rankOne_iff_dvd hcyc he γ).2 hd)
    have hzero : b φ γ = 0 := by
      rw [hb.rankOne_apply hSatakeF hSatakeE hcyc.pos.ne', ite_eq_right hndvd]
    rw [rankOne_orbitalIntegral_eq (F := F), hzero, smul_zero]
  · intro δ γ hδγ hγ μδ hμδ hrδ μγ hμγ hrγ νδ νγ hνδ hνγ has
    obtain ⟨x, hx, hmap⟩ := has
    have hconj : (fun c : sigmaCentralizer σ 1 δ => x⁻¹ * (c : GeneralLinear 1 E.Carrier) * x) =
        (fun c : sigmaCentralizer σ 1 δ => (c : GeneralLinear 1 E.Carrier)) :=
      funext fun c => rankOne_conj_eq x c
    have hmap' := (congrArg (fun f => Measure.map f μδ) hconj).symm.trans hmap
    have hm := rankOne_quotientMass_eq hunit hcyc he _ _
      (rankOne_glCentralizer_eq γ) (rankOne_sigmaCentralizer_eq δ)
      μδ μγ νδ νγ hνδ hνγ hmap'
    have hv := hb.rankOne_apply_of_order hSatakeF hSatakeE hcyc.pos.ne' φ
      (hδγ.ord_determinant_eq hcyc he)
    rw [rankOne_sigmaOrbitalIntegral_eq, rankOne_orbitalIntegral_eq (F := F), hm, hv]

end Langlands.BaseChange
