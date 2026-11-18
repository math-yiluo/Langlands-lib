import Langlands.GroupScheme.Reductive.PinningActualTitsDiagram
import Langlands.GroupScheme.Reductive.TitsPrescribedStabilizerField
import Langlands.GroupScheme.SimplyConnected.OrbitWeilFactorCover
import Langlands.GroupScheme.SimplyConnected.FactorCartanComponent

/-! # Actual component witnesses directly from stabilizer-field pinning diagrams -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.TitsIndexData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G) (E : IntermediateField k (SeparableClosure k))
  (a : d.Vertex) (H : GroupScheme (Spec (CommRingCat.of E)))
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]

local instance componentFromPinning_closureAlgebra : Algebra E (SeparableClosure E) :=
  (separableClosure E (AlgebraicClosure E)).algebra

local instance componentFromPinning_separable : Algebra.IsSeparable E (SeparableClosure k) :=
  Algebra.isSeparable_tower_top_of_isSeparable k E (SeparableClosure k)

/-- The actual factor pinning over its prescribed field and the original
separable closure, realizing the whole original component and full relative star action. -/
structure PinningComponentComparison where
  pinning : GaloisPinningData E (SeparableClosure k) H
  vertices : pinning.base.support ≃ d.CartanComponent a
  cartan_eq : ∀ b c, d.cartan (vertices b).val (vertices c).val =
    pinning.rootDatum.pairing b.val c.val
  star_eq : ∀ (ρ : SeparableClosure k ≃ₐ[E] SeparableClosure k) b,
    (vertices (pinning.simpleStar ρ b)).val = d.star (ρ.restrictScalars k) (vertices b).val

namespace PinningComponentComparison

variable {d E a H} (F : d.PinningComponentComparison E a H) (hH : IsSemisimple H)

/-- The actual Tits index realizing the prescribed extension-field pinning. -/
def actualDiagram :
    F.pinning.ActualTitsDiagram (prescribedStabilizerClosureEquiv E) :=
  F.pinning.actualTitsDiagram hH (prescribedStabilizerClosureEquiv E)

/-- Its entire actual simple-vertex set is the original entire selected component. -/
def actualVertices : (F.actualDiagram hH).index.Vertex ≃ d.CartanComponent a :=
  (F.actualDiagram hH).vertices.trans F.vertices

/-- Every original ordered Cartan entry is retained by the actual factor index. -/
theorem actual_cartan_eq (b c : (F.actualDiagram hH).index.Vertex) :
    d.cartan (F.actualVertices hH b).val (F.actualVertices hH c).val =
      (F.actualDiagram hH).index.cartan b c :=
  (F.cartan_eq _ _).trans ((F.actualDiagram hH).cartan_eq b c)

/-- The actual factor's full star action is the original relative-Galois star
action through the specified separable-closure comparison. -/
theorem actual_star_eq
    (τ : SeparableClosure E ≃ₐ[E] SeparableClosure E)
    (b : (F.actualDiagram hH).index.Vertex) :
    (F.actualVertices hH ((F.actualDiagram hH).index.star τ b)).val =
      d.star ((AlgEquiv.autCongr (prescribedStabilizerClosureEquiv E) τ).restrictScalars k)
        (F.actualVertices hH b).val := by
  change (F.vertices ((F.actualDiagram hH).vertices
    ((F.actualDiagram hH).index.star τ b))).val = _
  rw [(F.actualDiagram hH).star_eq, F.star_eq]
  rfl

/-- Each original component-stabilizer element has one factor-field lift on
all actual simple vertices simultaneously. -/
theorem actual_stabilizer_lift
    (hE : E.fixingSubgroup = d.cartanComponentStabilizer a)
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k)
    (hσ : d.CartanConnected a (d.star σ a)) :
    ∃ τ : SeparableClosure E ≃ₐ[E] SeparableClosure E,
      ∀ b, (F.actualVertices hH ((F.actualDiagram hH).index.star τ b)).val =
        d.star σ (F.actualVertices hH b).val := by
  let s : d.cartanComponentStabilizer a := ⟨σ, hσ⟩
  let τ := (d.prescribedStabilizerAbsoluteGaloisEquiv E a hE).symm s
  have hτ : (AlgEquiv.autCongr (prescribedStabilizerClosureEquiv E) τ).restrictScalars k = σ := by
    exact congrArg Subtype.val
      ((d.prescribedStabilizerAbsoluteGaloisEquiv E a hE).apply_symm_apply s)
  refine ⟨τ, fun b => ?_⟩
  simpa only [hτ] using F.actual_star_eq hH τ b

/-- Each full factor-field Galois element has one original lift acting on the
whole selected component simultaneously. -/
theorem actual_star_lift
    (hE : E.fixingSubgroup = d.cartanComponentStabilizer a)
    (τ : SeparableClosure E ≃ₐ[E] SeparableClosure E) :
    ∃ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
      ∀ b, (F.actualVertices hH ((F.actualDiagram hH).index.star τ b)).val =
        d.star σ (F.actualVertices hH b).val :=
  ⟨(d.prescribedStabilizerAbsoluteGaloisEquiv E a hE τ).val,
    fun b => F.actual_star_eq hH τ b⟩

end PinningComponentComparison

section OrbitAssembly

variable [Smooth G.X.hom]
  (D : SimplyConnectedAlmostSimpleProduct
    ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G))
  (hG : IsSemisimple
    ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G))

local instance componentFromPinning_baseChangeAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

local instance componentFromPinning_baseChangeSmooth :
    Smooth ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

attribute [local instance] SimplyConnectedAlmostSimpleProduct.factorStabilizerDescent_isAffine
  SimplyConnectedAlmostSimpleProduct.factorStabilizerDescent_locallyOfFiniteType

/-- An actual pinning/component comparison for the selected descended factor
supplies the complete original actual component witness. -/
def componentFactorOfPinningComparison (hSC : IsSimplyConnected G)
    (F : d.PinningComponentComparison
      (D.factorStabilizerField (d.geometricFactorIndex D hG a)) a
      (D.factorStabilizerDescent (d.geometricFactorIndex D hG a)).1) :
    d.ComponentFactor a := by
  let i := d.geometricFactorIndex D hG a
  have hH := (D.isSimplyConnected_factorStabilizerDescent i).isSemisimple
  have hE : (D.factorStabilizerField i).fixingSubgroup = d.cartanComponentStabilizer a :=
    (D.fixingSubgroup_factorStabilizerField i).trans
      (d.cartanComponentStabilizer_eq_geometricFactorStabilizer D hG a).symm
  exact (D.orbitWeilFactor hSC i).componentFactor
    (D.isClosedSubgroup_orbitWeilInclusion i) d a (F.actualDiagram hH).index
    (F.actualVertices hH) (F.actual_cartan_eq hH)
    (F.actual_stabilizer_lift hH hE) (F.actual_star_lift hH hE)

end OrbitAssembly
end Langlands.GroupScheme.TitsIndexData
