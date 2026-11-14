import Langlands.Geometry.Building.SemilinearTorusNormTransport

/-! # Bounded torus norm images under a square of field isomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Geometry.Building

variable {k K L M : Type u} [Field k] [Field K] [Field L] [Field M]
  [Algebra k L] [Algebra K M]

/-- The norm-source transport in a square of field isomorphisms, with no
horizontal algebra structures in its public type. -/
def fieldIsoSquareRationalExtend
    (e : k ≃+* K) (f : L ≃+* M)
    (hcomm : (algebraMap K M).comp e.toRingHom =
      f.toRingHom.comp (algebraMap k L))
    (T : CommGroupScheme (Spec (CommRingCat.of k))) :
    rationalPoints ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp →*
      rationalPoints ((CommGroupScheme.baseChange (baseMap K M)).obj
        ((CommGroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom e.toRingHom))).obj T)).toGrp := by
  let : Algebra k K := e.toRingHom.toAlgebra
  let : Algebra L M := f.toRingHom.toAlgebra
  let : Algebra k M := (f.toRingHom.comp (algebraMap k L)).toAlgebra
  let : IsScalarTower k L M := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower k K M := IsScalarTower.of_algebraMap_eq' hcomm.symm
  exact squareRationalExtend k K L M T

variable
  [FiniteDimensional k L] [IsGalois k L]
  [FiniteDimensional K M] [IsGalois K M]
  {ΓL ΓM : Type*} [LinearOrderedCommGroupWithZero ΓL]
  [LinearOrderedCommGroupWithZero ΓM]

private instance fieldIsoTorusAffine
    (e : k ≃+* K) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    [IsAffine T.X.left] :
    IsAffine ((CommGroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom e.toRingHom))).obj T).X.left := by
  change IsAffine (CategoryTheory.Limits.pullback T.X.hom _)
  infer_instance

/-- Bounded norm images are preserved by compatible isomorphisms of the
coefficient fields and splitting fields. The auxiliary horizontal algebra
structures are confined to the proof. -/
theorem map_torusNormIwahori_le_fieldIso_square
    (e : k ≃+* K) (f : L ≃+* M)
    (hcomm : (algebraMap K M).comp e.toRingHom =
      f.toRingHom.comp (algebraMap k L))
    (vL : Valuation L ΓL) (vM : Valuation M ΓM)
    (hv : vL.IsEquiv (vM.comap f.toRingHom))
    (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left] :
    (torusNormIwahori k L vL T).map
        (baseChangeSectionHom (Spec.map (CommRingCat.ofHom e.toRingHom)) T.toGrp) ≤
      torusNormIwahori K M vM
        ((CommGroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom e.toRingHom))).obj T) := by
  let : Algebra k K := e.toRingHom.toAlgebra
  let : Algebra L M := f.toRingHom.toAlgebra
  let : Algebra k M := (f.toRingHom.comp (algebraMap k L)).toAlgebra
  let : IsScalarTower k L M := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower k K M := IsScalarTower.of_algebraMap_eq' hcomm.symm
  let ek : k ≃ₐ[k] K := AlgEquiv.ofBijective (Algebra.ofId k K) e.bijective
  let fL : L ≃ₐ[L] M := AlgEquiv.ofBijective (Algebra.ofId L M) f.bijective
  let fk : L ≃ₐ[k] M := AlgEquiv.ofRingEquiv (f := f) (fun _ => rfl)
  let : FiniteDimensional k K := Module.Finite.equiv ek.toLinearEquiv
  let : FiniteDimensional L M := Module.Finite.equiv fL.toLinearEquiv
  let : FiniteDimensional k M := Module.Finite.equiv fk.toLinearEquiv
  let : IsGalois k K := IsGalois.of_algEquiv ek
  let : IsGalois L M := IsGalois.of_algEquiv fL
  let : IsGalois k M := IsGalois.of_algEquiv fk
  let : vL.HasExtension vM := ⟨hv⟩
  have hinv (σ : M ≃ₐ[L] M) (z : M) : vM (σ z) = vM z := by
    obtain ⟨a, rfl⟩ := f.surjective z
    exact congrArg vM (σ.commutes a)
  have h := map_torusNormIwahori_le_iso_square k K L M T vL vM
    e.surjective (Module.finrank_of_bijective_algebraMap f.bijective) hinv
  exact (rationalExtend_hom_eq_baseChangeSectionHom k K T.toGrp).symm ▸ h

end Langlands.Geometry.Building
