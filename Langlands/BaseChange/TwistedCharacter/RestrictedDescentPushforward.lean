import Langlands.BaseChange.TwistedCharacter.EmbeddedTestPushforward
import Langlands.HarmonicAnalysis.Distribution.Haar
import Langlands.HarmonicAnalysis.Distribution.TensorProduct

/-! # Restriction of the tensor identity in descent -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory MeasureTheory.Measure HarmonicAnalysis Set Function _root_.Topology

variable {X U X' U' Y Z : Type*} [TopologicalSpace X] [TopologicalSpace U]
  [TopologicalSpace X'] [TopologicalSpace U'] [TopologicalSpace Y] [TopologicalSpace Z]
  [T2Space X] [T2Space U] [T2Space Z]
  [MeasurableSpace X] [MeasurableSpace U] [MeasurableSpace X'] [MeasurableSpace U']
  [MeasurableSpace Y] [MeasurableSpace Z]
  [BorelSpace X] [BorelSpace U] [BorelSpace X'] [BorelSpace U'] [BorelSpace Y] [BorelSpace Z]

/-- Restrict a descent pushforward on both source factors and extend its target,
transporting its distribution tensor identity on product tests. -/
def RestrictedDescentPushforwardStatement
    {a : X' → X} (_ha : IsOpenEmbedding a) {b : U' → U} (hb : IsOpenEmbedding b)
    {j : Y → Z} (hj : IsOpenEmbedding j) (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (ω : Measure U) (ν : Measure Z) (p : X × U → Y)
    (P : SchwartzBruhat (X × U) →ₗ[ℂ] SchwartzBruhat Y) (D : Distribution Z) (T : Distribution U)
    [BorelSpace (X × U)] [BorelSpace (X' × U')]
    [SFinite μ] [SFinite ω] [SFinite (ω.comap b)] : Prop :=
  IsClosed (range j) → SchwartzBruhat.IsTestPushforward (μ.prod ω) (ν.comap j) p P →
  (D.comp (openEmbeddingTestExtension hj)).comp P = Distribution.tensor (Distribution.ofMeasure μ) T →
  ∃ Q : SchwartzBruhat (X' × U') →ₗ[ℂ] SchwartzBruhat Z,
    SchwartzBruhat.IsTestPushforward ((μ.comap a).prod (ω.comap b)) ν (j ∘ p ∘ Prod.map a b) Q ∧
    ∀ (f : SchwartzBruhat X') (g : SchwartzBruhat U'),
      D (Q (SchwartzBruhat.tensor f g)) = (∫ x, f x ∂(μ.comap a)) * T (openEmbeddingTestExtension hb g)

omit [T2Space U] [T2Space Z] [TopologicalSpace U] [TopologicalSpace U'] [TopologicalSpace Y]
  [TopologicalSpace Z] [MeasurableSpace U] [MeasurableSpace U'] [MeasurableSpace Y] [MeasurableSpace Z]
  [BorelSpace U] [BorelSpace U'] [BorelSpace Y] [BorelSpace Z] in
private theorem integral_openEmbeddingTestExtension {a : X' → X} (ha : IsOpenEmbedding a)
    (μ : Measure X) (f : SchwartzBruhat X') :
    (∫ x, openEmbeddingTestExtension ha f x ∂μ) = ∫ x, f x ∂(μ.comap a) := by
  let h := ha.measurableEmbedding
  calc
    _ = ∫ x in range a, openEmbeddingTestExtension ha f x ∂μ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun _ hx => openEmbeddingTestExtension_apply_of_not_mem ha f hx)).symm
    _ = _ := by
      rw [← h.map_comap, h.integral_map]
      simp only [openEmbeddingTestExtension_apply]

theorem restrictedDescentPushforward
    {a : X' → X} (ha : IsOpenEmbedding a) {b : U' → U} (hb : IsOpenEmbedding b)
    {j : Y → Z} (hj : IsOpenEmbedding j) (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (ω : Measure U) (ν : Measure Z) (p : X × U → Y)
    (P : SchwartzBruhat (X × U) →ₗ[ℂ] SchwartzBruhat Y) (D : Distribution Z) (T : Distribution U)
    [BorelSpace (X × U)] [BorelSpace (X' × U')]
    [SFinite μ] [SFinite ω] [SFinite (ω.comap b)] :
    RestrictedDescentPushforwardStatement ha hb hj μ ω ν p P D T := by
  intro hjClosed hP hD
  have hprod : (μ.prod ω).comap (Prod.map a b) = (μ.comap a).prod (ω.comap b) := by
    let ha' := ha.measurableEmbedding
    let hb' := hb.measurableEmbedding
    let h := ha'.prodMap hb'
    apply h.map_injective
    rw [h.map_comap, ← map_prod_map _ _ ha'.measurable hb'.measurable,
      ha'.map_comap, hb'.map_comap, range_prodMap, prod_restrict]
  let Q := (openEmbeddingTestExtension hj).comp (P.comp (openEmbeddingTestExtension (ha.prodMap hb)))
  refine ⟨Q, hprod ▸ embeddedTestPushforward (ha.prodMap hb) hj (μ.prod ω) ν p P hjClosed hP, ?_⟩
  intro f g
  change ((D.comp (openEmbeddingTestExtension hj)).comp P)
    (openEmbeddingTestExtension (ha.prodMap hb) (SchwartzBruhat.tensor f g)) = _
  rw [hD, openEmbeddingTestExtension_tensor ha hb, Distribution.tensor_apply_tensor,
    Distribution.ofMeasure_apply, integral_openEmbeddingTestExtension ha]

end Langlands.BaseChange
