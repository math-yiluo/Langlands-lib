import Langlands.GroupScheme.Torus.MultiplicativeTypeFiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeSubgroups
import Langlands.GroupScheme.RelativeLevi.GeometricFiberComparison
import Langlands.AlgebraicGeometry.AffineCoordinateBaseChange
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricCardinality
import Langlands.AbelianScheme.TorsionFunctor

/-! # Geometric fibre and coordinate-order transfer for fpqc descent -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- Multiplicative type over a field is reflected by every extension of that field. -/
theorem IsMultiplicativeType.of_fieldExtension
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsMultiplicativeType ((baseChange (algebraBaseMap k K)).obj G)) :
    IsMultiplicativeType G := by
  obtain ⟨L, hL, aL, Λ, hΛ, hfg, ⟨e⟩⟩ := hG
  let : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  let : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
  exact ⟨L, hL, inferInstance, Λ, hΛ, hfg,
    ⟨baseChangeFieldTowerIso k K L G ≪≫ e⟩⟩

/-- Multiplicative type over a field survives every extension of the ground field. -/
theorem IsMultiplicativeType.fieldExtension
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsMultiplicativeType G) :
    IsMultiplicativeType ((baseChange (algebraBaseMap k K)).obj G) := by
  obtain ⟨L, hL, aL, hfin, hgal, Λ, hΛ, hfg, ⟨e⟩⟩ :=
    multiplicativeTypeFiniteGaloisSplitting k G hG
  let Ω := AlgebraicClosure K
  let f : L →ₐ[k] Ω := IsAlgClosed.lift
  let : Algebra L Ω := f.toRingHom.toAlgebra
  let : IsScalarTower k L Ω := IsScalarTower.of_algHom f
  exact ⟨Ω, inferInstance, inferInstance, Λ, hΛ, hfg,
    ⟨(baseChangeFieldTowerIso k K Ω G).symm ≪≫
      baseChangeFieldTowerIso k L Ω G ≪≫
      (baseChange (algebraBaseMap L Ω)).mapIso e ≪≫
      Diagonalizable.baseChangeIso (algebraBaseMap L Ω) Λ⟩⟩

namespace FpqcMultiplicativeType

/-- Coordinate dimension with the scalar action induced by the actual structure map. -/
def coordinateOrder {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k))) : ℕ :=
  let := Langlands.AlgebraicGeometry.FiniteEtale.coordinateAlgebra X.hom
  Module.finrank k Γ(X.left, ⊤)

/-- An isomorphism over the ground field preserves the coordinate dimension. -/
theorem coordinateOrder_iso {k : Type u} [Field k]
    {X Y : Over (Spec (CommRingCat.of k))} (e : X ≅ Y) :
    coordinateOrder X = coordinateOrder Y := by
  exact (CommAlgCat.algEquivOfIso ((algΓ (.of k)).mapIso e).unop).toLinearEquiv.finrank_eq.symm

/-- Scalar extension of an affine scheme preserves its coordinate dimension,
including the value zero for infinite-dimensional coordinate algebras. -/
theorem coordinateOrder_baseChange {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] :
    coordinateOrder ((Over.pullback (algebraBaseMap k K)).obj X) =
      coordinateOrder X := by
  let e := Langlands.AlgebraicGeometry.AffineCoordinateBaseChange.baseChangeSectionsIso
    X (CommAlgCat.of k K)
  exact (CommAlgCat.algEquivOfIso e).toLinearEquiv.finrank_eq.trans
    (Module.finrank_baseChange (R := K) (S := k))

end FpqcMultiplicativeType

end Langlands.GroupScheme
