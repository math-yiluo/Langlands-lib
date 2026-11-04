import Langlands.GroupScheme.Rational.SplitSeriesBaseChange
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Langlands.GroupScheme.Rational.FiniteGaloisSplitUnipotentDescent
import Langlands.GroupScheme.Torus.SplittingDescentHelpers

/-! # Finite-separable descent of represented split series -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- A represented split series survives a compatible tower of field extensions
without changing its length, on the directly extended original group. -/
theorem HasSplitSeries.baseChange_fieldTower
    (k L K : Type u) [Field k] [Field L] [Field K]
    [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K]
    (H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom H.X.hom]
    {n : ℕ} (h : HasSplitSeries n
      ((GroupScheme.baseChange (algebraBaseMap k L)).obj H)) :
    HasSplitSeries n ((GroupScheme.baseChange (algebraBaseMap k K)).obj H) := by
  let : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj H).X.hom := by
    change IsAffineHom (pullback.snd H.X.hom (algebraBaseMap k L))
    infer_instance
  exact (h.baseChange K).of_iso (baseChangeFieldTowerIso k L K H).symm

/-- Split unipotence propagates through a compatible tower of fields. -/
theorem IsSplitUnipotent.baseChange_fieldTower
    (k L K : Type u) [Field k] [Field L] [Field K]
    [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K]
    (H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom H.X.hom]
    (h : IsSplitUnipotent ((GroupScheme.baseChange (algebraBaseMap k L)).obj H)) :
    IsSplitUnipotent ((GroupScheme.baseChange (algebraBaseMap k K)).obj H) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hn.baseChange_fieldTower k L K H⟩

/-- An affine group split unipotent over a finite separable field extension is
split unipotent over a finite Galois extension of the original field. -/
theorem IsSplitUnipotent.exists_finiteGalois_of_finiteSeparable
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom H.X.hom]
    (h : IsSplitUnipotent ((GroupScheme.baseChange (algebraBaseMap k L)).obj H)) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      FiniteDimensional k K ∧ IsGalois k K ∧
      IsSplitUnipotent ((GroupScheme.baseChange (algebraBaseMap k K)).obj H) := by
  let f : L →ₐ[k] SeparableClosure k := IsSepClosed.lift
  let : Algebra L (SeparableClosure k) := f.toRingHom.toAlgebra
  let : IsScalarTower k L (SeparableClosure k) :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let K := IntermediateField.normalClosure k L (SeparableClosure k)
  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact h.baseChange_fieldTower k L K H

/-- Split unipotence descends along a finite separable field extension for
smooth connected affine unipotent groups, using the explicit stable-vector
premise. -/
theorem IsSplitUnipotent.of_finiteSeparable_of_stableVector
    (hstable : SplitUnipotentStableVectorSubgroupStatement.{u})
    {k : Type u} [Field k] (L : Type u) [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (hU : IsUnipotent H)
    (hsplit : IsSplitUnipotent ((GroupScheme.baseChange (algebraBaseMap k L)).obj H)) :
    IsSplitUnipotent H := by
  obtain ⟨K, hK, hA, hfin, hgal, hsplitK⟩ :=
    hsplit.exists_finiteGalois_of_finiteSeparable k L H
  let : Field K := hK
  let : Algebra k K := hA
  let : FiniteDimensional k K := hfin
  let : IsGalois k K := hgal
  exact IsSplitUnipotent.of_finiteGalois_of_stableVector hstable K H hU hsplitK

/-- Choose an actual represented ground-field split series from finite
separable splitting, retaining the explicit stable-vector premise. -/
def finiteSeparableSplitSeriesOfStableVector
    (hstable : SplitUnipotentStableVectorSubgroupStatement.{u})
    {k : Type u} [Field k] (L : Type u) [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (hU : IsUnipotent H)
    (hsplit : IsSplitUnipotent ((GroupScheme.baseChange (algebraBaseMap k L)).obj H)) :
    {n : ℕ // HasSplitSeries n H} :=
  let h := IsSplitUnipotent.of_finiteSeparable_of_stableVector hstable L H hU hsplit
  ⟨h.choose, h.choose_spec⟩

end Langlands.GroupScheme.RelativeRoot
