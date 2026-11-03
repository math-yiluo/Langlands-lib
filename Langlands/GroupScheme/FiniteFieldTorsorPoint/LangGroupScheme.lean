import Langlands.GroupScheme.FiniteFieldTorsorPoint.LangCorepresented
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.Rational.CharacterLatticeProof
import Langlands.GroupScheme.Lie.GroupAlgebraCoordinates
import Langlands.AlgebraicGeometry.PointTopology.ProductRingPoints

/-! # Lang's theorem for smooth connected affine group schemes over a finite field -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.FiniteFieldTorsorPoint

variable {k : Type u} [Field k]

/-- The spectrum map of an algebra homomorphism is the same whether built by `ringTestMap` or
by `algSpec`. -/
theorem ringTestMap_eq_algSpec_map {A B : Type u} [CommRing A] [CommRing B] [Algebra k A]
    [Algebra k B] (f : A →ₐ[k] B) :
    ringTestMap k f = (algSpec (CommRingCat.of k)).map
      (CommAlgCat.ofHom (R := CommRingCat.of k) f).op := by
  ext1
  rfl

/-- **Lang's theorem** for a smooth connected affine group scheme `H` over a finite field `k`:
every point of `H` with values in an algebraically closed extension `K` of `k` has the form
`g⁻¹ * Frob(g)`, where `Frob` is induced by the `#k`-power Frobenius of `K`. -/
theorem exists_eq_inv_mul_frobenius [Fintype k] (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K] (a : ringTest k K ⟶ H.X) :
    ∃ g : ringTest k K ⟶ H.X,
      a = g⁻¹ * (ringTestMap k (FiniteField.frobeniusAlgHom k K) ≫ g) := by
  have := CharacterLatticeProof.isDomain_coord H
  have : IsDomain (Lie.coordinateAlgebra H) := this
  have : Algebra.FiniteType (CommRingCat.of k) (Lie.coordinateAlgebra H) :=
    Lie.coordinateAlgebraFiniteType H
  let e := AffineLinearEmbedding.corepresentableBy H (Lie.coordinateIso H)
  obtain ⟨g, hg⟩ := exists_lang_eq e K a
  exact ⟨g, hg.trans (by rw [ringTestMap_eq_algSpec_map]; rfl)⟩

end Langlands.GroupScheme.FiniteFieldTorsorPoint
