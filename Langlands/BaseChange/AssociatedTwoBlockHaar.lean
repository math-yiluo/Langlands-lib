import Langlands.Analysis.Local.QuotientFinTwoHaarTransport
import Langlands.BaseChange.ExactNormLeviCentralizer
import Langlands.BaseChange.OrdinarySphericalTwoBlockOrbitalDescent

/-! Common Haar normalization of associated ordinary and twisted block centralizers. -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory _root_.Topology Langlands.GeneralLinear Langlands.JacquetLanglands
open Langlands.QuotientIntegration Langlands.TraceFormula Langlands.Unramified Langlands.RankinSelberg
open scoped NNReal

universe u v w

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

local instance associatedBlockGLLocallyCompact {p : ℕ} [Fact p.Prime] (K : PadicField.{w} p) (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n K.Carrier) :=
  LocalFieldTopology.generalLinear_locallyCompactSpace K.Carrier n
local instance associatedBlockGLSecondCountable {p : ℕ} [Fact p.Prime] (K : PadicField.{w} p)
    (n : ℕ) : SecondCountableTopology (GeneralLinear n K.Carrier) :=
  LocalFieldTopology.generalLinear_secondCountableTopology K.Carrier n

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  [Algebra F.Carrier E.Carrier] [IsModuleTopology F.Carrier E.Carrier]
  {σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier} {l r : ℕ} {m : Fin 2 → ℕ}
  (h : ∑ i, (m i + 1) = r + 1)

local notation "B" => succBlockShape m h

set_option maxHeartbeats 2000000 in
/-- If the block centralizer measures and the ambient centralizer measures are
associated at exact norms, both ambient measures have the same relative scale
with respect to the products of their two block measures. -/
theorem twoBlockHaarScale_of_associated
    (L : (B).Levi F.Carrier) (D : (B).Levi E.Carrier)
    (hσ : IsCyclicAlgebra σ l) (hΓ : IsRegularSemisimple ((B).leviEmbedding F.Carrier L))
    (hReg : ∀ i : Fin 2, IsRegularSemisimple (L i))
    (hCop : Pairwise fun i j => IsCoprime (L i).val.charpoly (L j).val.charpoly)
    (hn : ∀ i : Fin 2, cyclicNorm σ l (D i) = baseChange F.Carrier E.Carrier (m i + 1) (L i))
    (μF : ∀ i : Fin 2, Measure (glCentralizer (L i))) [∀ i, (μF i).IsHaarMeasure]
    (μE : ∀ i : Fin 2, Measure (sigmaCentralizer σ (m i + 1) (D i)))
    (hAssoc : ∀ i : Fin 2, IsAssociatedMeasure σ l (D i) (L i) (μE i) (μF i))
    (μγ : Measure (glCentralizer ((B).leviEmbedding F.Carrier L)))
    (μδ : Measure (sigmaCentralizer σ (r + 1) ((B).leviEmbedding E.Carrier D)))
    (hAmbAssoc : IsAssociatedMeasure σ l ((B).leviEmbedding E.Carrier D)
      ((B).leviEmbedding F.Carrier L) μδ μγ)
    (c : ℝ≥0)
    (hScale : μγ = c • Measure.map (ordinaryLeviCentralizerEquiv F h L hCop)
      (finTwoSubgroupMeasure (fun i => glCentralizer (L i)) (μF 0) (μF 1))) :
    μδ = c • Measure.map (sigmaLeviCentralizerEquiv B L D hσ hReg hn hΓ hCop)
      (finTwoSubgroupMeasure (fun i => sigmaCentralizer σ (m i + 1) (D i)) (μE 0) (μE 1)) := by
  let C := fun i : Fin 2 => glCentralizer (L i)
  let Cσ := fun i : Fin 2 => sigmaCentralizer σ (m i + 1) (D i)
  have hClosed (i : Fin 2) : IsClosed (C i : Set (GeneralLinear (m i + 1) F.Carrier)) := by
    dsimp only [C]
    rw [glCentralizer_eq_centralizer]
    exact Set.isClosed_centralizer _
  let : ∀ i : Fin 2, LocallyCompactSpace (C i) := fun i => (hClosed i).locallyCompactSpace
  let : ∀ i : Fin 2, SecondCountableTopology (C i) := fun _ =>
    IsEmbedding.subtypeVal.secondCountableTopology
  let e := fun i : Fin 2 => exactNormCentralizerEquiv hσ (hReg i) (hn i)
  let eA := exactNormBlockCentralizerEquiv B L D hσ hReg hn
  let eF := ordinaryLeviCentralizerEquiv F h L hCop
  let eE := sigmaLeviCentralizerEquiv B L D hσ hReg hn hΓ hCop
  let hnΓ := cyclicNorm_leviEmbedding_eq_of_blockwise B L D hn
  let eG := exactNormCentralizerEquiv hσ hΓ hnΓ
  let productF := finTwoSubgroupMeasure C (μF 0) (μF 1)
  let productE := finTwoSubgroupMeasure Cσ (μE 0) (μE 1)
  have hPush (i : Fin 2) : μE i = Measure.map (e i) (μF i) :=
    (isAssociatedMeasure_iff_map_exactNormCentralizerEquiv hσ (hReg i) (hn i) _ _).mp (hAssoc i)
  have hProd : Measure.map eA productF = productE := by
    calc
      _ = finTwoSubgroupMeasure Cσ (Measure.map (e 0) (μF 0)) (Measure.map (e 1) (μF 1)) :=
        map_finTwoSubgroupMeasure C Cσ e eA
          (exactNormBlockCentralizerEquiv_coordinate B L D hσ hReg hn) (μF 0) (μF 1)
      _ = _ := by rw [← hPush 0, ← hPush 1]
  have hSquare : (⇑eG) ∘ (⇑eF) = (⇑eE) ∘ (⇑eA) := by
    funext a
    change eG (eF a) = eG (eF (eA.symm (eA a)))
    rw [ContinuousMulEquiv.symm_apply_apply]
  have hmG : Measurable (⇑eG) := eG.continuous.measurable
  have hmF : Measurable (⇑eF) := eF.continuous.measurable
  have hmE : Measurable (⇑eE) := eE.continuous.measurable
  have hmA : Measurable (⇑eA) := eA.continuous.measurable
  have hScaleF : μγ = c • Measure.map eF productF := hScale
  calc
    μδ = Measure.map eG μγ :=
      (isAssociatedMeasure_iff_map_exactNormCentralizerEquiv hσ hΓ hnΓ _ _).mp hAmbAssoc
    _ = c • Measure.map (⇑eG ∘ ⇑eF) productF := by
      rw [hScaleF, Measure.map_smul c hmG.aemeasurable, Measure.map_map hmG hmF]
    _ = c • Measure.map eE productE := by
      rw [hSquare, ← Measure.map_map hmE hmA, hProd]

end Langlands.BaseChange
