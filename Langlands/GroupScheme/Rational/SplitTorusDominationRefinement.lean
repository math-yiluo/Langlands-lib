import Langlands.GroupScheme.Rational.TorusDominationFiniteGalois
import Langlands.GroupScheme.Torus.SplittingDescentHelpers

/-! # Scalar extension and normal-closure refinement of split torus domination -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {H H' : GroupScheme (Spec (CommRingCat.of k))}

/-- A pointed dominant split-torus parametrization transports through an actual
group-scheme isomorphism of its target. -/
theorem HasPointedSplitTorusDomination.of_iso
    (e : H ≅ H') (h : HasPointedSplitTorusDomination H) :
    HasPointedSplitTorusDomination H' := by
  obtain ⟨P, p, hP, hd, hp⟩ := h
  have : IsDominant p.left := hd
  have : IsIso e.hom.hom.hom.left :=
    Functor.map_isIso (Grp.forget _ ⋙ Over.forget _) e.hom
  refine ⟨P, p ≫ e.hom.hom.hom, hP, ?_, ?_⟩
  · change IsDominant (p.left ≫ e.hom.hom.hom.left)
    infer_instance
  · rw [← Category.assoc, hp, MonObj.one_comp]

/-- Split-torus domination of a reduced affine group persists under every field
extension by pulling back the actual pointed parametrization. -/
theorem HasPointedSplitTorusDomination.baseChange_of_isReduced
    [IsReduced H.X.left] [IsAffineHom H.X.hom]
    (h : HasPointedSplitTorusDomination H) :
    HasPointedSplitTorusDomination
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj H) := by
  obtain ⟨P, p, hP, hd, hp⟩ := h
  exact ⟨_, (Over.pullback _).map p, hP.baseChange _,
    PointedTorusDomination.isDominant_baseChange hP.isTorus p hd,
    PointedTorusDomination.pullback_map_one _ p hp⟩

/-- Split-torus domination of a smooth affine group persists under every field
extension, with no separability or algebraicity requirement. -/
theorem HasPointedSplitTorusDomination.baseChange
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (h : HasPointedSplitTorusDomination H) :
    HasPointedSplitTorusDomination
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj H) := by
  have : ConnectedSpace H.X.left := h.hasPointedTorusDomination.connectedSpace
  have : GeometricallyIntegral H.X.hom :=
    smoothConnectedAffineGeometry.1 k H inferInstance inferInstance inferInstance
  have : IsReduced H.X.left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian H.X.hom
  exact h.baseChange_of_isReduced

/-- A pointed split-torus parametrization over the middle field of a compatible
tower extends to a parametrization of the direct scalar extension. -/
theorem HasPointedSplitTorusDomination.baseChange_fieldTower
    (k L K : Type u) [Field k] [Field L] [Field K]
    [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (h : HasPointedSplitTorusDomination
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj H)) :
    HasPointedSplitTorusDomination
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj H) := by
  let : Smooth ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj H).X.hom := by
    change Smooth (CategoryTheory.Limits.pullback.snd H.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    infer_instance
  let : IsAffineHom ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj H).X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd H.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    infer_instance
  exact (h.baseChange (K := K)).of_iso (baseChangeFieldTowerIso k L K H).symm

/-- Finite separable split-torus domination of a smooth affine group refines to
finite Galois split-torus domination of that same original group. -/
theorem HasPointedSplitTorusDomination.exists_finiteGalois_of_finiteSeparable
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (h : HasPointedSplitTorusDomination
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj H)) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      FiniteDimensional k K ∧ IsGalois k K ∧
      HasPointedSplitTorusDomination
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj H) := by
  let f : L →ₐ[k] SeparableClosure k := IsSepClosed.lift
  let : Algebra L (SeparableClosure k) := f.toRingHom.toAlgebra
  let : IsScalarTower k L (SeparableClosure k) :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let K := IntermediateField.normalClosure k L (SeparableClosure k)
  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact h.baseChange_fieldTower k L K H

/-- Choose an actual finite Galois field, split torus and pointed dominant
parametrization from a supplied finite-separable split-domination witness. -/
def HasPointedSplitTorusDomination.finiteGaloisRefinement
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (h : HasPointedSplitTorusDomination
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj H)) :
    FiniteGaloisSplitTorusDomination H :=
  Classical.choice (by
    obtain ⟨K, hK, hA, hfin, hgal, P, p, hP, hd, hp⟩ :=
      h.exists_finiteGalois_of_finiteSeparable k L H
    exact ⟨{
      carrier := K
      field := hK
      algebra := hA
      finiteDimensional := hfin
      isGalois := hgal
      torus := P
      parametrization := p
      isSplitTorus := hP
      dominant := hd
      pointed := hp }⟩)

end Langlands.GroupScheme
