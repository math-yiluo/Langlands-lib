import Langlands.BaseChange.ConcordanceConjugation
import Langlands.BaseChange.ExactNormCentralizer
import Langlands.BaseChange.FundamentalLemmaStatement
import Langlands.BaseChange.LeviNormDescent
import Langlands.BaseChange.RegularSemisimpleLevi

/-! # Reduction of the spherical fundamental lemma to regular elliptic elements -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.ProductLeviChamber
open Langlands.QuotientIntegration Langlands.TraceFormula Langlands.Unramified

universe u v

private theorem isRegularSemisimple_conj {K : Type u} [Field K] {n : ℕ}
    {γ : GeneralLinear n K} (hγ : IsRegularSemisimple γ) (a : GeneralLinear n K) :
    IsRegularSemisimple (a⁻¹ * γ * a) := by
  change γ.val.charpoly.Separable at hγ
  change ((a⁻¹).val * γ.val * a.val).charpoly.Separable
  simpa only [Matrix.coe_units_inv, Matrix.charpoly_units_conj'] using hγ

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

private local instance (K : PadicField p) : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
private local instance (K : PadicField p) : ValuativeRel K.Carrier := K.canonicalTopologicalData.valuativeRel
private local instance (K : PadicField p) : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField
local instance (K : PadicField p) (n : ℕ) : TopologicalSpace (GeneralLinear n K.Carrier) :=
  K.canonicalGeneralLinearTopology n
local instance (K : PadicField p) (n : ℕ) : IsTopologicalGroup (GeneralLinear n K.Carrier) :=
  K.canonicalGeneralLinearTopologicalGroup n
local instance (K : PadicField p) (n : ℕ) : T2Space (GeneralLinear n K.Carrier) :=
  K.canonicalGeneralLinearT2Space n
local instance (K : PadicField p) (n : ℕ) : MeasurableSpace (GeneralLinear n K.Carrier) := borel _
local instance (K : PadicField p) (n : ℕ) : BorelSpace (GeneralLinear n K.Carrier) := ⟨rfl⟩

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

private abbrev sphericalOrbitalIntegralVanishes {r : ℕ}
    (f : SphericalHeckeAlgebra F r) (γ : GeneralLinear (r + 1) F.Carrier) : Prop :=
  ∀ (μγ : Measure (glCentralizer γ)) [μγ.IsHaarMeasure] [μγ.IsMulRightInvariant]
    (νγ : Measure (LeftQuotient (glCentralizer γ))),
    IsCompatible (glCentralizer γ) (sphericalHaar F r) μγ νγ → orbitalIntegral γ νγ ⇑f = 0

variable (E : PadicField.{v} p) [Algebra F.Carrier E.Carrier]

private abbrev sphericalConcordanceInRank
    (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) (l r : ℕ) : Prop :=
  ∀ b : SphericalHeckeAlgebra E r →ₐ[ℂ] SphericalHeckeAlgebra F r,
    IsUnramifiedBaseChangeHom F E l r b → ∀ φ : SphericalHeckeAlgebra E r,
    AreConcordant σ l (sphericalHaar F r) (sphericalHaar E r) ⇑φ ⇑(b φ)

/-- Both branches of the spherical fundamental lemma restricted to the regular elliptic set. -/
def RegularEllipticFundamentalLemmaStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) (l r : ℕ),
    IsCyclicAlgebra σ l →
    E.canonicalTopologicalData.ramificationIndex = F.canonicalTopologicalData.ramificationIndex →
    ∀ (b : SphericalHeckeAlgebra E r →ₐ[ℂ] SphericalHeckeAlgebra F r),
      IsUnramifiedBaseChangeHom F E l r b →
      ∀ (φ : SphericalHeckeAlgebra E r) (γ : GeneralLinear (r + 1) F.Carrier),
        IsRegularElliptic γ →
        (¬ IsNorm σ l γ → sphericalOrbitalIntegralVanishes F (b φ) γ) ∧
        (∀ δ : GeneralLinear (r + 1) E.Carrier, IsNormAssociated σ l δ γ →
          ConcordAt σ l (sphericalHaar F r) (sphericalHaar E r) ⇑φ ⇑(b φ) δ γ)

/-- The spherical two-block descent input. Concordance in smaller ranks gives off-norm
vanishing and exact-norm concordance for the indicated regular block diagonal elements. -/
def SphericalTwoBlockParabolicDescentStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) (l r : ℕ),
    IsCyclicAlgebra σ l →
    E.canonicalTopologicalData.ramificationIndex = F.canonicalTopologicalData.ramificationIndex →
    (∀ s < r, sphericalConcordanceInRank F E σ l s) →
    ∀ (b : SphericalHeckeAlgebra E r →ₐ[ℂ] SphericalHeckeAlgebra F r),
      IsUnramifiedBaseChangeHom F E l r b → ∀ φ : SphericalHeckeAlgebra E r,
        ∀ (k : ℕ) (hk : 0 < k) (hkr : k < r + 1),
          let B := twoBlock (r + 1) k hk hkr
          ∀ (m : B.Levi F.Carrier),
            let γ := B.leviEmbedding F.Carrier m
            IsRegularSemisimple γ →
            (∀ i, IsRegularSemisimple (m i)) →
            (Pairwise fun i j => IsCoprime (m i).val.charpoly (m j).val.charpoly) →
            ((∃ i, ¬ IsNorm σ l (m i)) → sphericalOrbitalIntegralVanishes F (b φ) γ) ∧
            (∀ d : B.Levi E.Carrier,
              (∀ i, cyclicNorm σ l (d i) = baseChange F.Carrier E.Carrier (B.size i) (m i)) →
              let δ := B.leviEmbedding E.Carrier d
              sigmaCentralizer σ (r + 1) δ =
                (glCentralizer γ).map (baseChange F.Carrier E.Carrier (r + 1)) →
              ConcordAt σ l (sphericalHaar F r) (sphericalHaar E r) ⇑φ ⇑(b φ) δ γ)

/-- The regular elliptic case and the spherical two-block descent input imply the exact
fundamental lemma at all positive ranks. -/
def FundamentalLemmaBlockReductionStatement : Prop :=
  RegularEllipticFundamentalLemmaStatement.{u,v} →
  SphericalTwoBlockParabolicDescentStatement.{u,v} →
  FundamentalLemmaStatement.{u,v}

set_option maxHeartbeats 800000 in
theorem fundamentalLemmaBlockReduction : FundamentalLemmaBlockReductionStatement.{u,v} := by
  classical
  intro helliptic hdescent p _ F E _ _ σ l r hcyc hunram
  change sphericalConcordanceInRank F E σ l r
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro b hb φ
    have hEll := helliptic p F E σ l r hcyc hunram b hb φ
    have hDesc := hdescent p F E σ l r hcyc hunram ih b hb φ
    constructor
    · intro γ hreg hnon μγ _ _ νγ hν
      by_cases hell : IsRegularElliptic γ
      · exact @(hEll γ hell).1 hnon μγ ‹_› ‹_› νγ hν
      · obtain ⟨k, hk, hkr, a, m, ha, hm₀, hm₁, hcop⟩ :=
          exists_twoBlock_of_regularSemisimple_of_not_regularElliptic (Nat.succ_pos r) γ hreg hell
        let B := twoBlock (r + 1) k hk hkr
        have hRepr : IsRegularSemisimple (B.leviEmbedding F.Carrier m) :=
          ha ▸ isRegularSemisimple_conj hreg a
        have hBlocks (i : Fin B.length) : IsRegularSemisimple (m i) := by
          change Fin 2 at i
          fin_cases i
          · exact hm₀.1
          · exact hm₁
        have hNon : ¬ IsNorm σ l (B.leviEmbedding F.Carrier m) := by
          rw [← ha, isNorm_conj_iff hcyc.pow_eq_one]
          exact hnon
        have hSome : ∃ i, ¬ IsNorm σ l (m i) :=
          not_forall.mp (fun h => hNon ((isNorm_leviEmbedding_iff B hcyc.pow_eq_one m hcop).2 h))
        apply orbitalIntegral_eq_zero_of_conj ⇑(b φ) γ a _ μγ νγ hν
        rw [ha]
        exact (hDesc k hk hkr m hRepr hBlocks hcop).1 hSome
    · intro δ γ hassoc hreg
      by_cases hell : IsRegularElliptic γ
      · exact (hEll γ hell).2 δ hassoc
      · obtain ⟨k, hk, hkr, a, m, ha, hm₀, hm₁, hcop⟩ :=
          exists_twoBlock_of_regularSemisimple_of_not_regularElliptic (Nat.succ_pos r) γ hreg hell
        let B := twoBlock (r + 1) k hk hkr
        have hRepr : IsRegularSemisimple (B.leviEmbedding F.Carrier m) :=
          ha ▸ isRegularSemisimple_conj hreg a
        have hBlocks (i : Fin B.length) : IsRegularSemisimple (m i) := by
          change Fin 2 at i
          fin_cases i
          · exact hm₀.1
          · exact hm₁
        apply concordAt_of_conj_of_cyclicNorm_eq hcyc.pow_eq_one
          (continuous_baseChange_padic F E (r + 1)).measurable δ γ a
        intro δ' hn
        rw [ha] at hn ⊢
        obtain ⟨d, hd, hNormBlocks⟩ := exists_levi_of_cyclicNorm_eq B hcyc.pow_eq_one m hcop hn
        let : Module.Finite F.Carrier E.Carrier := hcyc.1
        let : IsModuleTopology F.Carrier E.Carrier := isModuleTopology_padic_extension F E
        have hCentralizer := sigmaCentralizer_eq_map_glCentralizer_of_cyclicNorm_eq hcyc hRepr hn
        rw [hd] at hCentralizer ⊢
        exact (hDesc k hk hkr m hRepr hBlocks hcop).2 d hNormBlocks hCentralizer

end Padic

end Langlands.BaseChange
