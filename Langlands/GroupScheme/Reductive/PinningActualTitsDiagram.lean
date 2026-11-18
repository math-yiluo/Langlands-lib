import Langlands.GroupScheme.Reductive.StarActionFiniteStageProof
import Langlands.GroupScheme.Reductive.TitsIndexExistenceProof

/-! # An actual Tits index realizing any prescribed separable-closure pinning diagram -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.GaloisPinningData

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (p : GaloisPinningData k L G)

/-- The full star permutation of the actual simple vertices of pinning data. -/
def simpleStar (σ : L ≃ₐ[k] L) (b : p.base.support) : p.base.support :=
  ⟨(p.starAction σ).val.indexEquiv b.val,
    ((p.starAction σ).property b.val).mp b.property⟩

local instance pinningActualDiagram_closureAlgebra : Algebra k (SeparableClosure k) :=
  (separableClosure k (AlgebraicClosure k)).algebra

/-- An actual Tits index with the entire prescribed pinning diagram and every
full star permutation, using a specified separable-closure comparison. -/
structure ActualTitsDiagram (e : SeparableClosure k ≃ₐ[k] L) where
  index : TitsIndexData G
  vertices : index.Vertex ≃ p.base.support
  cartan_eq : ∀ a b,
    p.rootDatum.pairing (vertices a).val (vertices b).val = index.cartan a b
  star_eq : ∀ (τ : SeparableClosure k ≃ₐ[k] SeparableClosure k) a,
    vertices (index.star τ a) = p.simpleStar (AlgEquiv.autCongr e τ) (vertices a)

variable [Algebra.IsAlgebraic k L]

/-- Every actual semisimple group admits an actual index realizing the full
diagram of its prescribed pinning over a specified separable closure. -/
theorem nonempty_actualTitsDiagram (hG : IsSemisimple G)
    (e : SeparableClosure k ≃ₐ[k] L) : Nonempty (p.ActualTitsDiagram e) := by
  let : Algebra (SeparableClosure k) L := e.toRingHom.toAlgebra
  have hc : algebraBaseMap (SeparableClosure k) L ≫
      algebraBaseMap k (SeparableClosure k) = algebraBaseMap k L := by
    simp only [algebraBaseMap, ← Spec.map_comp]
    congr 1
    ext x
    exact e.commutes x
  have hT : IsTorus p.torus.toGrp := ⟨L, inferInstance, inferInstance, p.isSplitTorus⟩
  have hsplit := GaloisPinningData.isSplitTorus_separableClosure p.torus hT
  obtain ⟨q, ε, hεb, hεstar⟩ := StarActionFiniteStage.exists_stage p hc hsplit
  obtain ⟨d⟩ := titsIndexExistence k G hG
  obtain ⟨g, φ, ζ, hg, hχ, hζb, hζstar⟩ :=
    StarActionIndependence.starActionIndependence k (SeparableClosure k) G q d.pinning
  let f := ε.comp ζ.symm
  have hfb : ∀ a, a ∈ d.pinning.base.support ↔ f.indexEquiv a ∈ p.base.support := by
    intro a
    have hz := hζb (ζ.indexEquiv.symm a)
    simp only [Equiv.apply_symm_apply] at hz
    exact hz.symm.trans (hεb _)
  let v : d.Vertex ≃ p.base.support := f.indexEquiv.subtypeEquiv hfb
  refine ⟨⟨d, v, fun a b => f.toHom.pairing, fun τ a => Subtype.ext ?_⟩⟩
  let ρ := AlgEquiv.autCongr e τ
  have hcompat : ∀ x, ρ (algebraMap (SeparableClosure k) L x) =
      algebraMap (SeparableClosure k) L (τ x) := by
    intro x
    change e (τ (e.symm (e x))) = e (τ x)
    rw [e.symm_apply_apply]
  have hz := congrArg (fun z => z.indexEquiv (ζ.indexEquiv.symm a.val)) (hζstar τ)
  change ζ.indexEquiv
      ((q.starAction τ).val.indexEquiv (ζ.indexEquiv.symm a.val)) =
    (d.pinning.starAction τ).val.indexEquiv (ζ.indexEquiv (ζ.indexEquiv.symm a.val)) at hz
  simp only [Equiv.apply_symm_apply] at hz
  have hz' := congrArg ζ.indexEquiv.symm hz
  simp only [Equiv.symm_apply_apply] at hz'
  have he := congrArg (fun z => z.indexEquiv (ζ.indexEquiv.symm a.val))
    (hεstar τ ρ hcompat)
  change ε.indexEquiv
      (ζ.indexEquiv.symm ((d.pinning.starAction τ).val.indexEquiv a.val)) =
    (p.starAction ρ).val.indexEquiv (ε.indexEquiv (ζ.indexEquiv.symm a.val))
  rw [← hz']
  exact he

/-- Choose the actual index without changing the supplied pinning diagram. -/
def actualTitsDiagram (hG : IsSemisimple G) (e : SeparableClosure k ≃ₐ[k] L) :
    p.ActualTitsDiagram e :=
  Classical.choice (p.nonempty_actualTitsDiagram hG e)

end Langlands.GroupScheme.GaloisPinningData
