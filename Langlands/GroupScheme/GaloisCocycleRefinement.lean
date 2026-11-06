import Langlands.GroupScheme.GaloisCocycle
import Langlands.GroupScheme.GaloisPointTransitivity
import Langlands.GroupScheme.CocycleRefinement

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace GaloisCocycle

variable (k L M : Type u) [Field k] [Field L] [Field M]
  [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]

/-- The actual cover refinement induced by the intermediate field inclusion. -/
def coverMap : cover k M ⟶ cover k L :=
  (algSpec (CommRingCat.of k)).map
    (CommAlgCat.ofHom (IsScalarTower.toAlgHom k L M)).op

variable [Normal k L]

/-- Restriction of a coefficient automorphism is compatible with cover refinement. -/
theorem arrow_coverMap (σ : M ≃ₐ[k] M) :
    arrow k M σ ≫ coverMap k L M =
      coverMap k L M ≫ arrow k L (σ.restrictNormal L) := by
  have h : σ.toAlgHom.comp (IsScalarTower.toAlgHom k L M) =
      (IsScalarTower.toAlgHom k L M).comp (σ.restrictNormal L).toAlgHom := by
    ext x
    exact (σ.restrictNormal_commutes L x).symm
  change (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom σ.toAlgHom).op ≫
      (algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom (IsScalarTower.toAlgHom k L M)).op =
      (algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom (IsScalarTower.toAlgHom k L M)).op ≫
      (algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom (σ.restrictNormal L).toAlgHom).op
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun f : L →ₐ[k] M =>
    (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op) h

variable {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Values of the refined cocycle are extensions of values at the restricted automorphism. -/
theorem value_refine (ξ : Cocycle G (cover k L)) (σ : M ≃ₐ[k] M) :
    value (ξ.refine (coverMap k L M)) σ =
      GaloisPoint.relativeExtend k L M G (value ξ (σ.restrictNormal L)) := by
  change ξ.toFun (𝟙 _ ≫ coverMap k L M) (arrow k M σ ≫ coverMap k L M) =
    coverMap k L M ≫ ξ.toFun (𝟙 _) (arrow k L (σ.restrictNormal L))
  rw [Category.id_comp, arrow_coverMap]
  simpa only [Category.comp_id] using
    ξ.naturality (coverMap k L M) (𝟙 _) (arrow k L (σ.restrictNormal L))

variable [FiniteDimensional k L] [IsGalois k L]
  [FiniteDimensional k M] [IsGalois k M]
  [FiniteDimensional L M] [IsGalois L M] [IsAffine G.X.left]

/-- A cocycle trivialized on a finite Galois refinement is already trivial over its original
finite Galois cover; the witness descends through relative fixed coefficient points. -/
theorem isTrivial_of_refine (ξ : Cocycle G (cover k L))
    (h : (ξ.refine (coverMap k L M)).IsTrivial) : ξ.IsTrivial := by
  obtain ⟨x, hx⟩ := (isTrivial_iff (ξ.refine (coverMap k L M))).mp h
  have hfixed : x ∈ GaloisPoint.relativeFixedSubgroup k L M G := by
    intro σ
    have hval : value (ξ.refine (coverMap k L M)) (σ.restrictScalars k) = 1 := by
      rw [value_refine, GaloisPoint.restrictNormal_relativeAut]
      change GaloisPoint.relativeExtend k L M G (ξ.toFun (𝟙 _) (arrow k L 1)) = 1
      rw [arrow_one, ξ.toFun_self, map_one]
    have hmul : x * (GaloisPoint.relativeConjugate k L M G σ x)⁻¹ = 1 :=
      (hx (σ.restrictScalars k)).symm.trans hval
    exact (mul_inv_eq_one.mp hmul).symm
  let f := GaloisPoint.relativeDescend k L M G ⟨x, hfixed⟩
  have hf : GaloisPoint.relativeExtend k L M G f = x :=
    GaloisPoint.relativeExtend_descend k L M G ⟨x, hfixed⟩
  apply (isTrivial_iff ξ).mpr
  refine ⟨f, fun τ => ?_⟩
  apply GaloisPoint.relativeExtend_injective k L M G
  rw [map_mul, map_inv, GaloisPoint.relativeExtend_conjugate_lift, hf]
  calc
    GaloisPoint.relativeExtend k L M G (value ξ τ) =
        value (ξ.refine (coverMap k L M)) (τ.liftNormal M) := by
      rw [value_refine, AlgEquiv.restrict_liftNormal]
    _ = _ := hx (τ.liftNormal M)

end GaloisCocycle
end Langlands.GroupScheme
