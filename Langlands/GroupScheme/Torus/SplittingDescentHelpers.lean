import Langlands.GroupScheme.Torus.FiniteGaloisSplittingStatement
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Torus.Geometry
import Langlands.AbelianScheme.Tate.BaseChangeCoherence
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Noetherian

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

universe u

/-- A field torus is quasi-compact, since its split base change surjects onto it. -/
theorem IsTorus.quasiCompact
    {k : Type u} [Field k]
    {T : GroupScheme (Spec (CommRingCat.of k))} (hT : IsTorus T) :
    QuasiCompact T.X.hom := by
  obtain ⟨K, hK, hA, h⟩ := hT
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : Surjective b :=
    ((flat_and_surjective_SpecMap_iff _).2
      ((RingHom.faithfullyFlat_algebraMap_iff).2 inferInstance)).2
  have : IsAffineHom ((GroupScheme.baseChange b).obj T).X.hom := h.isAffineHom
  have : IsAffine ((GroupScheme.baseChange b).obj T).X.left :=
    isAffine_of_isAffineHom ((GroupScheme.baseChange b).obj T).X.hom
  have : IsAffine (CategoryTheory.Limits.pullback T.X.hom b) :=
    ‹IsAffine ((GroupScheme.baseChange b).obj T).X.left›
  have : CompactSpace T.X.left :=
    Function.Surjective.compactSpace (CategoryTheory.Limits.pullback.fst T.X.hom b).continuous
      (CategoryTheory.Limits.pullback.fst T.X.hom b).surjective
  infer_instance

/-- A field torus is quasi-separated, since smoothness makes it locally Noetherian. -/
theorem IsTorus.quasiSeparated
    {k : Type u} [Field k]
    {T : GroupScheme (Spec (CommRingCat.of k))} (hT : IsTorus T) :
    QuasiSeparated T.X.hom := by
  have := hT.smooth
  have := LocallyOfFiniteType.isLocallyNoetherian T.X.hom
  infer_instance

/-- The actual group-scheme comparison between direct and iterated scalar extension. -/
def baseChangeFieldTowerIso
    (k L K : Type u) [CommRing k] [CommRing L] [CommRing K]
    [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K]
    (T : GroupScheme (Spec (CommRingCat.of k))) :
    ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T) ≅
    ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap L K)))).obj
        ((GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T)) := by
  have hc : Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k L)) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact (IsScalarTower.algebraMap_eq k L K).symm
  rw [← hc]
  exact baseChangeCompIso _ _ T

/-- Splitting over the last field of a tower agrees with iterated base change. -/
theorem IsSplitTorus.baseChange_fieldTower_iff
    (k L K : Type u) [CommRing k] [CommRing L] [CommRing K]
    [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K]
    (T : GroupScheme (Spec (CommRingCat.of k))) :
    IsSplitTorus ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T) ↔
    IsSplitTorus ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap L K)))).obj
        ((GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T)) :=
  IsSplitTorus.iso_iff (baseChangeFieldTowerIso k L K T)

/-- Splitting propagates through a compatible tower of scalar extensions. -/
theorem IsSplitTorus.baseChange_fieldTower
    (k L K : Type u) [CommRing k] [CommRing L] [CommRing K]
    [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K]
    (T : GroupScheme (Spec (CommRingCat.of k)))
    (h : IsSplitTorus ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T)) :
    IsSplitTorus ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T) :=
  (IsSplitTorus.baseChange_fieldTower_iff k L K T).2
    (h.baseChange (Spec.map (CommRingCat.ofHom (algebraMap L K))))

/-- Being a torus is preserved by an algebraic extension of the ground field. -/
theorem IsTorus.baseChange_of_isAlgebraic
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    (T : GroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T) :
    IsTorus ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T) := by
  obtain ⟨K, hK, hA, h⟩ := hT
  let E := AlgebraicClosure K
  let f : L →ₐ[k] E := IsAlgClosed.lift
  let : Algebra L E := f.toRingHom.toAlgebra
  let : IsScalarTower k L E :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  refine ⟨E, inferInstance, inferInstance, ?_⟩
  exact (IsSplitTorus.baseChange_fieldTower_iff k L E T).1
    (h.baseChange_fieldTower k K E T)

/-- A finite separable splitting field can be enlarged to a finite Galois one. -/
theorem IsSplitTorus.exists_finiteGalois_of_finiteSeparable
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (T : GroupScheme (Spec (CommRingCat.of k)))
    (h : IsSplitTorus ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj T)) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      FiniteDimensional k K ∧ IsGalois k K ∧
      IsSplitTorus ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T) := by
  let f : L →ₐ[k] SeparableClosure k := IsSepClosed.lift
  let : Algebra L (SeparableClosure k) := f.toRingHom.toAlgebra
  let : IsScalarTower k L (SeparableClosure k) :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let K := IntermediateField.normalClosure k L (SeparableClosure k)
  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact h.baseChange_fieldTower k L K T

end Langlands.GroupScheme
