import Langlands.BaseChange.FundamentalLemmaBlockReduction
import Langlands.BaseChange.SphericalConstantTermBaseChange
import Langlands.BaseChange.SphericalTwoBlockConstantTermExpansion
import Langlands.BaseChange.UnramifiedBaseChangeHomStatement

/-! Spherical two-block descent reduces to the ordinary and twisted orbital formulas. -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory TopologicalSpace Langlands.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.GodementJacquet.TwoBlock Langlands.RankinSelberg Langlands.Unramified
open Langlands.JacquetLanglands Langlands.QuotientIntegration Langlands.TraceFormula
open Langlands.ProductLeviChamber

universe u v

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel
attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

local instance sphericalDescentFieldMeasurable {p : ℕ} [Fact p.Prime] (K : PadicField p) :
    MeasurableSpace K.Carrier := borel _
local instance sphericalDescentFieldBorel {p : ℕ} [Fact p.Prime] (K : PadicField p) :
    BorelSpace K.Carrier := ⟨rfl⟩

private abbrev Rectangle (R : Type*) (m : Fin 2 → ℕ) :=
  Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R

private abbrev HasIntegralRectangleMassOne {p : ℕ} [Fact p.Prime] (K : PadicField p)
    {m : Fin 2 → ℕ} (dx : Measure (Rectangle K.Carrier m)) : Prop :=
  dx {x | ∀ i j, x i j ∈ (ValuativeRel.valuation K.Carrier).integer} = 1

private abbrev IsRadicalIntegralExpansion {p : ℕ} [Fact p.Prime] (K : PadicField p)
    {r : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = r + 1)
    (dx : Measure (Rectangle K.Carrier m)) (f : SphericalHeckeAlgebra K r) {N : ℕ}
    (α : Fin N → SphericalHeckeAlgebra K (m 0)) (β : Fin N → SphericalHeckeAlgebra K (m 1)) :
    Prop :=
  ∀ L : (succBlockShape m h).Levi K.Carrier,
    (K.canonicalTopologicalData.leviHalfModulus (succBlockShape m h) L : ℂ) *
      (∫ x, f (parabolicPoint h (L, x)) ∂dx) = ∑ j, α j (L 0) * β j (L 1)

private theorem exists_rectangleHaar {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)
    (m : Fin 2 → ℕ) :
    ∃ dx : Measure (Rectangle K.Carrier m),
      dx.IsAddHaarMeasure ∧ HasIntegralRectangleMassOne K dx := by
  let T := K.canonicalTopologicalData
  let : T2Space K.Carrier := T.fieldT2
  let : SecondCountableTopology K.Carrier := T.secondCountableTopology
  let O := (ValuativeRel.valuation K.Carrier).integer
  let C : PositiveCompacts K.Carrier :=
    { carrier := O
      isCompact' := T.isCompact_integers
      interior_nonempty' := by
        rw [(Valuation.isOpen_integer (v := ValuativeRel.valuation K.Carrier)).interior_eq]
        exact ⟨0, O.zero_mem⟩ }
  let da := normalizedAdditiveHaar K.Carrier C
  refine ⟨rectangularMeasure da (m 0 + 1) (m 1 + 1), inferInstance, ?_⟩
  exact rectangularMeasure_entries_one da (m 0 + 1) (m 1 + 1) O Measure.addHaarMeasure_self

/-- The ordinary orbital descent formula in finite spherical expansions. The
block quotient measures and the scalar can be fixed for all the test functions. -/
def OrdinarySphericalTwoBlockOrbitalDescentStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (r : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = r + 1)
    (dx : Measure (Rectangle F.Carrier m)) [dx.IsAddHaarMeasure],
    HasIntegralRectangleMassOne F dx →
    ∀ L : (succBlockShape m h).Levi F.Carrier,
      let γ := (succBlockShape m h).leviEmbedding F.Carrier L
      IsRegularSemisimple γ →
      (∀ i : Fin 2, IsRegularSemisimple (L i)) →
      (Pairwise fun i j : Fin 2 => IsCoprime (L i).val.charpoly (L j).val.charpoly) →
      ∀ (μγ : Measure (glCentralizer γ)) [μγ.IsHaarMeasure] [μγ.IsMulRightInvariant]
        (νγ : Measure (LeftQuotient (glCentralizer γ))),
        IsCompatible (glCentralizer γ) (sphericalHaar F r) μγ νγ →
        ∃ (c : ℂ) (μ : ∀ i : Fin 2, Measure (glCentralizer (L i)))
          (ν : ∀ i : Fin 2, Measure (LeftQuotient (glCentralizer (L i)))),
          (∀ i, (μ i).IsHaarMeasure ∧ ∃ hRight : (μ i).IsMulRightInvariant,
            letI := hRight
            IsCompatible (glCentralizer (L i)) (sphericalHaar F (m i)) (μ i) (ν i)) ∧
          (∀ (f : SphericalHeckeAlgebra F r) (N : ℕ)
              (α : Fin N → SphericalHeckeAlgebra F (m 0)) (β : Fin N → SphericalHeckeAlgebra F (m 1)),
            IsRadicalIntegralExpansion F h dx f α β →
            orbitalIntegral γ νγ ⇑f = c * ∑ j,
              orbitalIntegral (L 0) (ν 0) ⇑(α j) * orbitalIntegral (L 1) (ν 1) ⇑(β j))

/-- The ordinary and twisted descent formulas at an exact block norm use
associated block measures and a common scalar for the two finite expansions. -/
def AssociatedSphericalTwoBlockOrbitalDescentStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) (l r : ℕ)
    (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = r + 1)
    (dxF : Measure (Rectangle F.Carrier m)) [dxF.IsAddHaarMeasure]
    (dxE : Measure (Rectangle E.Carrier m)) [dxE.IsAddHaarMeasure],
    IsCyclicAlgebra σ l →
    E.canonicalTopologicalData.ramificationIndex = F.canonicalTopologicalData.ramificationIndex →
    HasIntegralRectangleMassOne F dxF → HasIntegralRectangleMassOne E dxE →
    ∀ (L : (succBlockShape m h).Levi F.Carrier) (D : (succBlockShape m h).Levi E.Carrier),
      let γ := (succBlockShape m h).leviEmbedding F.Carrier L
      let δ := (succBlockShape m h).leviEmbedding E.Carrier D
      IsRegularSemisimple γ →
      (∀ i : Fin 2, IsRegularSemisimple (L i)) →
      (Pairwise fun i j : Fin 2 => IsCoprime (L i).val.charpoly (L j).val.charpoly) →
      (∀ i : Fin 2, cyclicNorm σ l (D i) = baseChange F.Carrier E.Carrier (m i + 1) (L i)) →
      sigmaCentralizer σ (r + 1) δ = (glCentralizer γ).map (baseChange F.Carrier E.Carrier (r + 1)) →
      ∀ (μδ : Measure (sigmaCentralizer σ (r + 1) δ)) [μδ.IsHaarMeasure] [μδ.IsMulRightInvariant]
        (μγ : Measure (glCentralizer γ)) [μγ.IsHaarMeasure] [μγ.IsMulRightInvariant]
        (νδ : Measure (LeftQuotient (sigmaCentralizer σ (r + 1) δ)))
        (νγ : Measure (LeftQuotient (glCentralizer γ))),
        IsCompatible (sigmaCentralizer σ (r + 1) δ) (sphericalHaar E r) μδ νδ →
        IsCompatible (glCentralizer γ) (sphericalHaar F r) μγ νγ →
        IsAssociatedMeasure σ l δ γ μδ μγ →
        ∃ (c : ℂ) (μF : ∀ i : Fin 2, Measure (glCentralizer (L i)))
          (νF : ∀ i : Fin 2, Measure (LeftQuotient (glCentralizer (L i))))
          (μE : ∀ i : Fin 2, Measure (sigmaCentralizer σ (m i + 1) (D i)))
          (νE : ∀ i : Fin 2, Measure (LeftQuotient (sigmaCentralizer σ (m i + 1) (D i)))),
          (∀ i, (μF i).IsHaarMeasure ∧ (μE i).IsHaarMeasure ∧
            ∃ (hRightF : (μF i).IsMulRightInvariant) (hRightE : (μE i).IsMulRightInvariant),
              letI := hRightF
              letI := hRightE
              IsCompatible (glCentralizer (L i)) (sphericalHaar F (m i)) (μF i) (νF i) ∧
              IsCompatible (sigmaCentralizer σ (m i + 1) (D i))
                (sphericalHaar E (m i)) (μE i) (νE i) ∧
              IsAssociatedMeasure σ l (D i) (L i) (μE i) (μF i)) ∧
          (∀ (f : SphericalHeckeAlgebra F r) (N : ℕ)
              (α : Fin N → SphericalHeckeAlgebra F (m 0)) (β : Fin N → SphericalHeckeAlgebra F (m 1)),
            IsRadicalIntegralExpansion F h dxF f α β →
            orbitalIntegral γ νγ ⇑f = c * ∑ j,
              orbitalIntegral (L 0) (νF 0) ⇑(α j) * orbitalIntegral (L 1) (νF 1) ⇑(β j)) ∧
          (∀ (φ : SphericalHeckeAlgebra E r) (N : ℕ)
              (α : Fin N → SphericalHeckeAlgebra E (m 0)) (β : Fin N → SphericalHeckeAlgebra E (m 1)),
            IsRadicalIntegralExpansion E h dxE φ α β →
            sigmaOrbitalIntegral σ (r + 1) δ νδ ⇑φ = c * ∑ j,
              sigmaOrbitalIntegral σ (m 0 + 1) (D 0) (νE 0) ⇑(α j) *
                sigmaOrbitalIntegral σ (m 1 + 1) (D 1) (νE 1) ⇑(β j))

private theorem twoBlock_eq_succBlockShape {r k : ℕ} (hk : 0 < k) (hkr : k < r + 1)
    (h : ∑ i : Fin 2, ((![k - 1, r - k] : Fin 2 → ℕ) i + 1) = r + 1) :
    twoBlock (r + 1) k hk hkr = succBlockShape ![k - 1, r - k] h := by
  unfold twoBlock succBlockShape
  congr
  funext i
  fin_cases i <;> simp <;> omega

set_option maxHeartbeats 2000000 in
theorem sphericalTwoBlockParabolicDescent_of_orbitalDescent
    (hBaseChange : UnramifiedBaseChangeHomStatement.{u,v})
    (hOrdinary : OrdinarySphericalTwoBlockOrbitalDescentStatement.{u})
    (hAssociated : AssociatedSphericalTwoBlockOrbitalDescentStatement.{u,v}) :
    SphericalTwoBlockParabolicDescentStatement.{u,v} := by
  intro p _ F E _ _ σ l r hCyc hUnram ih b hb φ k hk hkr
  let m : Fin 2 → ℕ := ![k - 1, r - k]
  have hRanks : ∑ i, (m i + 1) = r + 1 := by
    rw [Fin.sum_univ_two]
    simp only [m, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    omega
  have hSmall (i : Fin 2) : m i < r := by
    fin_cases i <;> simp [m] <;> omega
  dsimp only
  rw [twoBlock_eq_succBlockShape hk hkr hRanks]
  intro L
  dsimp only
  intro hReg hBlocks hCop
  obtain ⟨dxF, hAddF, hMassF⟩ := exists_rectangleHaar F m
  obtain ⟨dxE, hAddE, hMassE⟩ := exists_rectangleHaar E m
  let : dxF.IsAddHaarMeasure := hAddF
  let : dxE.IsAddHaarMeasure := hAddE
  obtain ⟨b₀, hb₀, _⟩ := hBaseChange p F E l (m 0)
  obtain ⟨b₁, hb₁, _⟩ := hBaseChange p F E l (m 1)
  obtain ⟨N, α, β, hCTE⟩ := exists_twoBlock_sphericalConstantTerm_expansion E hRanks φ dxE
  obtain ⟨M, αF, βF, hCTF⟩ := exists_twoBlock_sphericalConstantTerm_expansion F hRanks (b φ) dxF
  have hBC := sphericalConstantTerm_baseChange F E hRanks dxF dxE hMassF hMassE b b₀ b₁
    hb hb₀ hb₁ φ αF βF α β hCTF hCTE
  have hExpansion : IsRadicalIntegralExpansion F hRanks dxF (b φ) (b₀ ∘ α) (b₁ ∘ β) :=
    fun L' => (hCTF L').trans (hBC L')
  constructor
  · intro hNon μγ _ _ νγ hCompat
    obtain ⟨c, μ, ν, hMeasures, hFormula⟩ := hOrdinary p F r m hRanks dxF hMassF
      L hReg hBlocks hCop μγ νγ hCompat
    rw [hFormula (b φ) N (b₀ ∘ α) (b₁ ∘ β) hExpansion]
    have hVanish (i : Fin 2) (bᵢ : SphericalHeckeAlgebra E (m i) →ₐ[ℂ] SphericalHeckeAlgebra F (m i))
        (hbᵢ : IsUnramifiedBaseChangeHom F E l (m i) bᵢ)
        (f : SphericalHeckeAlgebra E (m i)) (hNonᵢ : ¬ IsNorm σ l (L i)) :
        orbitalIntegral (L i) (ν i) ⇑(bᵢ f) = 0 := by
      obtain ⟨hHaar, hRight, hCompatibility⟩ := hMeasures i
      let : (μ i).IsHaarMeasure := hHaar
      let : (μ i).IsMulRightInvariant := hRight
      exact (ih (m i) (hSmall i) bᵢ hbᵢ f).1 (L i) (hBlocks i) hNonᵢ
        (μ i) (ν i) hCompatibility
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro j _
    simp only [Function.comp_apply]
    obtain ⟨i, hNonᵢ⟩ := hNon
    fin_cases i
    · rw [hVanish 0 b₀ hb₀ (α j) hNonᵢ, zero_mul]
    · rw [hVanish 1 b₁ hb₁ (β j) hNonᵢ, mul_zero]
  · intro D hNorm hCentralizer μδ _ _ μγ _ _ νδ νγ hCompatibleE hCompatibleF hAssociation
    obtain ⟨c, μF, νF, μE, νE, hMeasures, hFormulaF, hFormulaE⟩ :=
      hAssociated p F E σ l r m hRanks dxF dxE hCyc hUnram hMassF hMassE L D hReg hBlocks
        hCop hNorm hCentralizer μδ μγ νδ νγ hCompatibleE hCompatibleF hAssociation
    rw [hFormulaE φ N α β hCTE, hFormulaF (b φ) N (b₀ ∘ α) (b₁ ∘ β) hExpansion]
    have hMatch (i : Fin 2) (bᵢ : SphericalHeckeAlgebra E (m i) →ₐ[ℂ] SphericalHeckeAlgebra F (m i))
        (hbᵢ : IsUnramifiedBaseChangeHom F E l (m i) bᵢ) (f : SphericalHeckeAlgebra E (m i)) :
        sigmaOrbitalIntegral σ (m i + 1) (D i) (νE i) ⇑f =
          orbitalIntegral (L i) (νF i) ⇑(bᵢ f) := by
      obtain ⟨hHaarF, hHaarE, hRightF, hRightE, hCompF, hCompE, hAssoc⟩ := hMeasures i
      let : (μF i).IsHaarMeasure := hHaarF
      let : (μF i).IsMulRightInvariant := hRightF
      let : (μE i).IsHaarMeasure := hHaarE
      let : (μE i).IsMulRightInvariant := hRightE
      have hPair : IsNormAssociated σ l (D i) (L i) :=
        ⟨1, by simpa only [inv_one, one_mul, mul_one] using hNorm i⟩
      exact (ih (m i) (hSmall i) bᵢ hbᵢ f).2 (D i) (L i) hPair (hBlocks i)
        (μE i) (μF i) (νE i) (νF i) hCompE hCompF hAssoc
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg₂ (· * ·) (hMatch 0 b₀ hb₀ (α j)) (hMatch 1 b₁ hb₁ (β j))

/-- The exact fundamental lemma follows from its regular elliptic case, existence
of spherical base change and the two orbital descent formulas. -/
def FundamentalLemmaSphericalDescentReductionStatement : Prop :=
  RegularEllipticFundamentalLemmaStatement.{u,v} →
  UnramifiedBaseChangeHomStatement.{u,v} →
  OrdinarySphericalTwoBlockOrbitalDescentStatement.{u} →
  AssociatedSphericalTwoBlockOrbitalDescentStatement.{u,v} →
  FundamentalLemmaStatement.{u,v}

theorem fundamentalLemmaSphericalDescentReduction : FundamentalLemmaSphericalDescentReductionStatement.{u,v} :=
  fun hEll hBase hOrd hAssoc => fundamentalLemmaBlockReduction hEll
    (sphericalTwoBlockParabolicDescent_of_orbitalDescent hBase hOrd hAssoc)

end Langlands.BaseChange
