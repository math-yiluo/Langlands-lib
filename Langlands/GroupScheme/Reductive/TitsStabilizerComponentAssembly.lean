import Langlands.GroupScheme.Reductive.TitsPrescribedStabilizerField
import Langlands.GroupScheme.SimplyConnected.OrbitWeilFactorCover
import Langlands.GroupScheme.SimplyConnected.FactorCartanComponent

/-! # Assemble the original component witness from its exact stabilizer-field comparison -/

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
  (a : d.Vertex)
  (H : GroupScheme (Spec (CommRingCat.of E)))
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]

local instance stabilizerComponentAssembly_closureAlgebra : Algebra E (SeparableClosure E) :=
  (separableClosure E (AlgebraicClosure E)).algebra

/-- The entire selected component over its prescribed field, with the actual
factor index and each full absolute-Galois element retained. -/
structure StabilizerFieldComponentComparison where
  index : TitsIndexData H
  vertices : index.Vertex ≃
    (d.prescribedStabilizerIndexComparison E).index.CartanComponent
      ((d.prescribedStabilizerIndexComparison E).vertices a)
  cartan_eq : ∀ b c,
    (d.prescribedStabilizerIndexComparison E).index.cartan (vertices b).val (vertices c).val =
      index.cartan b c
  star_eq : ∀ (τ : SeparableClosure E ≃ₐ[E] SeparableClosure E) b,
    (vertices (index.star τ b)).val =
      (d.prescribedStabilizerIndexComparison E).index.star τ (vertices b).val

namespace StabilizerFieldComponentComparison

variable {d E a H} (F : d.StabilizerFieldComponentComparison E a H)

/-- Pull the entire relative component back to the original component. -/
def originalVertices : F.index.Vertex ≃ d.CartanComponent a :=
  F.vertices.trans ((d.prescribedStabilizerIndexComparison E).cartanComponentEquiv a).symm

theorem originalVertices_apply (b : F.index.Vertex) :
    (d.prescribedStabilizerIndexComparison E).vertices (F.originalVertices b).val =
      (F.vertices b).val :=
  congrArg Subtype.val
    (((d.prescribedStabilizerIndexComparison E).cartanComponentEquiv a).apply_symm_apply
      (F.vertices b))

/-- Every ordered Cartan entry remains exact over the original field. -/
theorem original_cartan_eq (b c : F.index.Vertex) :
    d.cartan (F.originalVertices b).val (F.originalVertices c).val = F.index.cartan b c := by
  rw [← (d.prescribedStabilizerIndexComparison E).cartan_eq,
    F.originalVertices_apply, F.originalVertices_apply]
  exact F.cartan_eq b c

/-- One factor-field Galois element lifts an original stabilizer element
simultaneously on every simple vertex. -/
theorem original_stabilizer_lift (hE : E.fixingSubgroup = d.cartanComponentStabilizer a)
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k)
    (hσ : d.CartanConnected a (d.star σ a)) :
    ∃ τ : SeparableClosure E ≃ₐ[E] SeparableClosure E,
      ∀ b, (F.originalVertices (F.index.star τ b)).val =
        d.star σ (F.originalVertices b).val := by
  obtain ⟨τ, hτ⟩ := d.prescribedStabilizerIndexComparison_stabilizer_lift E a hE σ hσ
  refine ⟨τ, fun b => ?_⟩
  apply (d.prescribedStabilizerIndexComparison E).vertices.injective
  rw [F.originalVertices_apply, F.star_eq, hτ, F.originalVertices_apply]

/-- Every factor-field Galois element has one original lift acting on the
whole original component simultaneously. -/
theorem original_star_lift (hE : E.fixingSubgroup = d.cartanComponentStabilizer a)
    (τ : SeparableClosure E ≃ₐ[E] SeparableClosure E) :
    ∃ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
      ∀ b, (F.originalVertices (F.index.star τ b)).val =
        d.star σ (F.originalVertices b).val := by
  obtain ⟨σ, _hσ, hτ⟩ := d.prescribedStabilizerIndexComparison_star_lift E a hE τ
  refine ⟨σ, fun b => ?_⟩
  apply (d.prescribedStabilizerIndexComparison E).vertices.injective
  rw [F.originalVertices_apply, F.star_eq, hτ, F.originalVertices_apply]

end StabilizerFieldComponentComparison

section OrbitAssembly

variable [Smooth G.X.hom]
  (D : SimplyConnectedAlmostSimpleProduct
    ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G))
  (hG : IsSemisimple
    ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G))

local instance orbitComponentAssembly_baseChangeAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

local instance orbitComponentAssembly_baseChangeSmooth :
    Smooth ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

attribute [local instance] SimplyConnectedAlmostSimpleProduct.factorStabilizerDescent_isAffine
  SimplyConnectedAlmostSimpleProduct.factorStabilizerDescent_locallyOfFiniteType

/-- A full Cartan/star comparison for the exact descended geometric factor
supplies every field of the original actual component witness. -/
def componentFactorOfStabilizerComparison (hSC : IsSimplyConnected G)
    (F : d.StabilizerFieldComponentComparison
      (D.factorStabilizerField (d.geometricFactorIndex D hG a)) a
      (D.factorStabilizerDescent (d.geometricFactorIndex D hG a)).1) :
    d.ComponentFactor a := by
  let i := d.geometricFactorIndex D hG a
  have hE : (D.factorStabilizerField i).fixingSubgroup = d.cartanComponentStabilizer a :=
    (D.fixingSubgroup_factorStabilizerField i).trans
      (d.cartanComponentStabilizer_eq_geometricFactorStabilizer D hG a).symm
  exact (D.orbitWeilFactor hSC i).componentFactor
    (D.isClosedSubgroup_orbitWeilInclusion i) d a F.index F.originalVertices
    F.original_cartan_eq (F.original_stabilizer_lift hE) (F.original_star_lift hE)

end OrbitAssembly
end Langlands.GroupScheme.TitsIndexData
