import Langlands.GroupScheme.Descent.TensorCoverDatum
import Langlands.GroupScheme.Descent.CentralIsogenies
import Langlands.GroupScheme.BaseChangeReflection

/-! # Actual central-isogeny descent from a tensor cover datum -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme

open Descent

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
variable {J : Type v} [Fintype J]
variable (e : (L ⊗[k] L) ≃ₐ[L] (J → L)) (s : J → L ≃ₐ[k] L)
    (he : ∀ a b i, e (a ⊗ₜ[k] b) i = a * s i b)
variable {G : GroupScheme (Spec (CommRingCat.of k))}
    {C : GroupScheme (Spec (CommRingCat.of L))}
    {π : C ⟶ (baseChange (fieldMap k L)).obj G}

local instance instTensorCoverDescent1 : Flat (fieldMap k L) := (fieldExtension_fpqc k L).2.1
local instance instTensorCoverDescent2 : Surjective (fieldMap k L) := (fieldExtension_fpqc k L).1

namespace IsSimplyConnectedCover

/-- Construct an actual descended source and its pullback identification from
the supplied cover and finite tensor decomposition. -/
def tensorDescentSolution (hπ : IsSimplyConnectedCover π) :
    Solution ((canonicalDatum (fieldMap k L) G).liftWithTensorDecomposition e s he hπ) := by
  letI : IsAffineHom C.X.hom := hπ.isSimplyConnected.isSemisimple.isConnectedReductive.isAffineHom
  letI : IsAffine C.X.left := isAffine_of_isAffineHom C.X.hom
  exact ((canonicalDatum (fieldMap k L) G).liftWithTensorDecomposition e s he hπ).affineSolution

/-- Construct the actual central isogeny from the descended source to the
original target. -/
def tensorDescentCentralIsogeny (hπ : IsSimplyConnectedCover π) :
    {a : (hπ.tensorDescentSolution e s he).obj ⟶ G // IsCentralIsogeny a} := by
  letI : IsAffineHom C.X.hom := hπ.isSimplyConnected.isSemisimple.isConnectedReductive.isAffineHom
  letI : IsAffine C.X.left := isAffine_of_isAffineHom C.X.hom
  let D := (canonicalDatum (fieldMap k L) G).liftWithTensorDecomposition e s he hπ
  exact D.affineCentralIsogenyTo G π
      ((canonicalDatum (fieldMap k L) G).compatible_liftWithTensorDecomposition e s he hπ)
      hπ.isCentralIsogeny

/-- The descended central isogeny pulls back to the supplied cover through the
constructed source identification. -/
theorem baseChange_tensorDescentCentralIsogeny (hπ : IsSimplyConnectedCover π) :
    (baseChange (fieldMap k L)).map (hπ.tensorDescentCentralIsogeny e s he).val =
      (hπ.tensorDescentSolution e s he).iso.hom ≫ π := by
  let : IsAffineHom C.X.hom := hπ.isSimplyConnected.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine C.X.left := isAffine_of_isAffineHom C.X.hom
  let D := (canonicalDatum (fieldMap k L) G).liftWithTensorDecomposition e s he hπ
  exact D.baseChange_affineCentralIsogenyTo G π
      ((canonicalDatum (fieldMap k L) G).compatible_liftWithTensorDecomposition e s he hπ)
      hπ.isCentralIsogeny

include e s he in
/-- There is exactly one central isogeny from this constructed source with the
specified pullback recovery equation. -/
theorem existsUnique_tensorDescentCentralIsogeny (hπ : IsSimplyConnectedCover π) :
    ∃! a : (hπ.tensorDescentSolution e s he).obj ⟶ G,
      IsCentralIsogeny a ∧ (baseChange (fieldMap k L)).map a =
        (hπ.tensorDescentSolution e s he).iso.hom ≫ π := by
  let : IsAffineHom C.X.hom := hπ.isSimplyConnected.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine C.X.left := isAffine_of_isAffineHom C.X.hom
  let D := (canonicalDatum (fieldMap k L) G).liftWithTensorDecomposition e s he hπ
  exact D.existsUnique_affineCentralIsogenyTo G π
      ((canonicalDatum (fieldMap k L) G).compatible_liftWithTensorDecomposition e s he hπ)
      hπ.isCentralIsogeny

end IsSimplyConnectedCover

end Langlands.GroupScheme
