import Langlands.Geometry.Building.Kottwitz.TorusMap
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.Torus.BaseChange
import Langlands.GroupScheme.Torus.SplittingDescentHelpers

/-! # A finite Galois splitting field of a torus inside `F^sep / K`

For a torus `T` over a coefficient field `k` of the scalar tower `k → K → F^sep`
(where `K` is the maximal unramified extension of the nonarchimedean local field `F`),
we choose a finite Galois intermediate field `L` of `F^sep / K` over which `T` splits.
-/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.Kottwitz

/-- A torus over a coefficient field `k` of the tower `k → K → F^sep` splits over some finite
Galois intermediate field `L` of `F^sep / K`, where `K = UnramifiedClosure F`. -/
theorem exists_finiteGalois_splitting
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (k : Type u) [Field k] [Algebra k (UnramifiedClosure F)] [Algebra k (SeparableClosure F)]
    [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)] [Normal k (UnramifiedClosure F)]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T.toGrp) :
    ∃ L : IntermediateField (UnramifiedClosure F) (SeparableClosure F),
      FiniteDimensional (UnramifiedClosure F) L ∧ IsGalois (UnramifiedClosure F) L ∧
      IsSplitTorus ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp := by
  let K := UnramifiedClosure F
  -- The torus `T_K` over `K`.
  have hTK : IsTorus (baseChanged k K T.toGrp) := IsTorus.baseChange hT
  -- An abstract finite Galois splitting field `E / K` of `T_K`.
  obtain ⟨E, hE, hA, hfin, hgal, hsplit⟩ :=
    torusFiniteGaloisSplitting K (baseChanged k K T.toGrp) hTK
  -- Embed `E` into `F^sep` over `K` and take its image `L`.
  let φ : E →ₐ[K] SeparableClosure F := IsSepClosed.lift
  let L : IntermediateField K (SeparableClosure F) := φ.fieldRange
  let e : E ≃ₐ[K] L := φ.equivFieldRange
  have : FiniteDimensional K L := Module.Finite.equiv e.toLinearEquiv
  have : IsGalois K L := IsGalois.of_algEquiv e
  refine ⟨L, inferInstance, inferInstance, ?_⟩
  -- Transport the splitting of `T_K` from `E` to `L`.
  have hsplitL : IsSplitTorus (baseChanged K L (baseChanged k K T.toGrp)) := by
    obtain ⟨I, hI, ⟨s⟩⟩ := hsplit
    exact ⟨I, hI, TorusExistence.nonempty_splitIso_extension e.toRingHom
      (RingHom.ext e.commutes) _ I s⟩
  -- Identify the iterated base change `(T_K)_L` with `T_L`.
  exact (IsSplitTorus.baseChange_fieldTower_iff k K L T.toGrp).2 hsplitL

end Langlands.Geometry.Building.Kottwitz
