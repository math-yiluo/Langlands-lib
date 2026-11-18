import Langlands.GroupScheme.Reductive.TitsCartanComponentScalarExtension

/-! # Full component Galois lifts over a prescribed actual stabilizer field -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TitsIndexData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G) (E : IntermediateField k (SeparableClosure k))

local instance prescribedStabilizerClosureAlgebra : Algebra E (SeparableClosure E) :=
  (separableClosure E (AlgebraicClosure E)).algebra

local instance prescribedStabilizerAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

local instance prescribedStabilizerFiniteType :
    LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

/-- Closure comparison retaining an arbitrary specified intermediate field. -/
def prescribedStabilizerClosureEquiv : SeparableClosure E ≃ₐ[E] SeparableClosure k := by
  letI : Algebra.IsSeparable E (SeparableClosure k) :=
    Algebra.isSeparable_tower_top_of_isSeparable k E (SeparableClosure k)
  letI : IsSepClosure E (SeparableClosure k) := ⟨inferInstance, inferInstance⟩
  exact IsSepClosure.equiv _ _ _

/-- The actual index over the specified field, with the entire original
Cartan and star comparison. -/
def prescribedStabilizerIndexComparison :
    d.SeparableScalarExtension E (prescribedStabilizerClosureEquiv E) :=
  d.separableScalarExtension E (prescribedStabilizerClosureEquiv E)

/-- Exact full absolute-Galois equivalence over any specified intermediate field
whose pointwise fixer is exactly the original component stabilizer. -/
def prescribedStabilizerAbsoluteGaloisEquiv (a : d.Vertex)
    (hE : E.fixingSubgroup = d.cartanComponentStabilizer a) :
    (SeparableClosure E ≃ₐ[E] SeparableClosure E) ≃* d.cartanComponentStabilizer a :=
  (AlgEquiv.autCongr (prescribedStabilizerClosureEquiv E)).trans
    ((IntermediateField.fixingSubgroupEquiv E).symm.trans (MulEquiv.subgroupCongr hE))

/-- The represented original Galois element is precisely restriction through
the chosen actual separable-closure comparison. -/
theorem prescribedStabilizerAbsoluteGaloisEquiv_val (a : d.Vertex)
    (hE : E.fixingSubgroup = d.cartanComponentStabilizer a)
    (τ : SeparableClosure E ≃ₐ[E] SeparableClosure E) :
    (d.prescribedStabilizerAbsoluteGaloisEquiv E a hE τ).val =
      (AlgEquiv.autCongr (prescribedStabilizerClosureEquiv E) τ).restrictScalars k := rfl

/-- Each original stabilizer element has one lift over the specified field
acting simultaneously on all original simple vertices. -/
theorem prescribedStabilizerIndexComparison_stabilizer_lift (a : d.Vertex)
    (hE : E.fixingSubgroup = d.cartanComponentStabilizer a)
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k)
    (hσ : d.CartanConnected a (d.star σ a)) :
    ∃ τ : SeparableClosure E ≃ₐ[E] SeparableClosure E, ∀ b : d.Vertex,
      (d.prescribedStabilizerIndexComparison E).vertices (d.star σ b) =
        (d.prescribedStabilizerIndexComparison E).index.star τ
          ((d.prescribedStabilizerIndexComparison E).vertices b) := by
  let s : d.cartanComponentStabilizer a := ⟨σ, hσ⟩
  let τ := (d.prescribedStabilizerAbsoluteGaloisEquiv E a hE).symm s
  have hτ : (d.prescribedStabilizerAbsoluteGaloisEquiv E a hE τ).val = σ :=
    congrArg Subtype.val ((d.prescribedStabilizerAbsoluteGaloisEquiv E a hE).apply_symm_apply s)
  refine ⟨τ, fun b => ?_⟩
  have hs := (d.prescribedStabilizerIndexComparison E).star_eq τ b
  change (d.prescribedStabilizerIndexComparison E).vertices
      (d.star (d.prescribedStabilizerAbsoluteGaloisEquiv E a hE τ).val b) = _ at hs
  exact hτ ▸ hs

/-- Every Galois element over the specified field has one original stabilizer
lift acting simultaneously on all simple vertices. -/
theorem prescribedStabilizerIndexComparison_star_lift (a : d.Vertex)
    (hE : E.fixingSubgroup = d.cartanComponentStabilizer a)
    (τ : SeparableClosure E ≃ₐ[E] SeparableClosure E) :
    ∃ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
      d.CartanConnected a (d.star σ a) ∧ ∀ b : d.Vertex,
      (d.prescribedStabilizerIndexComparison E).vertices (d.star σ b) =
        (d.prescribedStabilizerIndexComparison E).index.star τ
          ((d.prescribedStabilizerIndexComparison E).vertices b) := by
  refine ⟨(d.prescribedStabilizerAbsoluteGaloisEquiv E a hE τ).val,
    (d.prescribedStabilizerAbsoluteGaloisEquiv E a hE τ).property,
    fun b => (d.prescribedStabilizerIndexComparison E).star_eq τ b⟩

/-- The full chosen component is stable over its prescribed stabilizer field. -/
theorem prescribedStabilizerIndexComparison_component_stable (a : d.Vertex)
    (hE : E.fixingSubgroup = d.cartanComponentStabilizer a)
    (τ : SeparableClosure E ≃ₐ[E] SeparableClosure E) :
    (d.prescribedStabilizerIndexComparison E).index.CartanConnected
      ((d.prescribedStabilizerIndexComparison E).vertices a)
      ((d.prescribedStabilizerIndexComparison E).index.star τ
        ((d.prescribedStabilizerIndexComparison E).vertices a)) := by
  obtain ⟨σ, hσ, hs⟩ := d.prescribedStabilizerIndexComparison_star_lift E a hE τ
  exact (hs a) ▸ ((d.prescribedStabilizerIndexComparison E).cartanConnected_iff
    a (d.star σ a)).mpr hσ

end Langlands.GroupScheme.TitsIndexData
