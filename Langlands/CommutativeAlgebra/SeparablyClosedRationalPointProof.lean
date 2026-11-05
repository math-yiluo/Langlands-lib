import Langlands.AlgebraicGeometry.PointTopology.SmoothSeparablyClosedDensity
import Langlands.CommutativeAlgebra.SeparablyClosedRationalPointStatement
import Langlands.CommutativeAlgebra.RationalPointSpecialization
import Langlands.CommutativeAlgebra.GeometricallyReducedSeparatingBasis
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Unramified.Field

/-! # Rational points of geometrically reduced algebras over separably closed fields

This module proves `Langlands.CommutativeAlgebra.SeparablyClosedRationalPointStatement`: a
nonzero finitely generated geometrically reduced algebra `R` over a separably closed field `k`
has a `k`-algebra map to `k`. The residue field `K` of `R` at a minimal prime is a finitely
generated geometrically reduced field extension of `k`. It has a separating transcendence basis
`s`, so `K` is finite separable over `k(s)`. Since `k` is infinite, every nonzero polynomial in
`s` stays nonzero at some `k`-point, and the specialization lemma for fraction fields gives the
required `k`-algebra map.
-/

universe u v

open TensorProduct

namespace Langlands.CommutativeAlgebra.SeparablyClosedRationalPointProof

open RationalPointSpecialization GeometricallyReducedSeparatingBasis
open scoped IntermediateField.algebraAdjoinAdjoin

/-- A localization of a geometrically reduced algebra over a field is geometrically reduced. -/
theorem isGeometricallyReduced_localization {k B : Type*} [Field k] [CommRing B] [Algebra k B]
    [Algebra.IsGeometricallyReduced k B] (M : Submonoid B) :
    Algebra.IsGeometricallyReduced k (Localization M) := by
  rw [Algebra.isGeometricallyReduced_field_iff]
  have : IsReduced (AlgebraicClosure k ⊗[k] B) :=
    (Algebra.isGeometricallyReduced_field_iff k B).mp inferInstance
  let e := IsLocalization.tensorProductEquivOfMapIncludeRight k (AlgebraicClosure k) M
    (Localization M)
    (Localization (M.map (Algebra.TensorProduct.includeRight (R := k) (A := AlgebraicClosure k))))
  exact isReduced_of_injective e.toRingHom e.injective

/-- Let `K` be a finitely generated geometrically reduced field extension of a separably closed
field `k`. Then every finitely generated `k`-algebra with a `k`-algebra map to `K` has a
`k`-algebra map to `k`. -/
theorem nonempty_algHom_of_field {k K R : Type*} [Field k] [IsSepClosed k] [Field K]
    [Algebra k K] [Algebra.EssFiniteType k K] [Algebra.IsGeometricallyReduced k K] [CommRing R]
    [Algebra k R] [Algebra.FiniteType k R] (f : R →ₐ[k] K) : Nonempty (R →ₐ[k] k) := by
  classical
  have := Langlands.AlgebraicGeometry.PointTopology.infinite_of_isSepClosed k
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable k K
  let F := IntermediateField.adjoin k (s : Set K)
  have : Algebra.EssFiniteType F K := Algebra.EssFiniteType.of_comp k F K
  have : Algebra.FormallyUnramified F K := Algebra.FormallyUnramified.of_isSeparable F K
  have : FiniteDimensional F K := Algebra.FormallyUnramified.finite_of_free F K
  let e : MvPolynomial s k ≃ₐ[k] Algebra.adjoin k (s : Set K) :=
    hs.1.aevalEquiv.trans (Subalgebra.equivOfEq _ _ (by ext; simp))
  refine nonempty_algHom_of_isFractionRing (P := Algebra.adjoin k (s : Set K)) (F := F) f
    fun D hD => ?_
  have hp : e.symm D ≠ 0 := (map_ne_zero_iff _ e.symm.injective).mpr hD
  obtain ⟨x, hx⟩ : ∃ x : s → k, MvPolynomial.eval x (e.symm D) ≠ 0 := by
    by_contra! H
    exact hp (MvPolynomial.funext fun x => by rw [H x, map_zero])
  exact ⟨(MvPolynomial.aeval x).comp e.symm.toAlgHom, hx⟩

/-- Every nonzero finitely generated geometrically reduced algebra over a separably closed
field `k` admits a `k`-algebra homomorphism to `k`. -/
theorem separablyClosedRationalPoint : SeparablyClosedRationalPointStatement.{u, v} := by
  intro k R _ _ _ _ _ _ _
  obtain ⟨⟨q, hq⟩⟩ := Ideal.nonempty_minimalPrimes (R := R) (I := ⊥) bot_ne_top
  have := hq.1.1
  have : IsReduced R := Algebra.isReduced_of_isGeometricallyReduced k
  have : Ring.KrullDimLE 0 (Localization.AtPrime q) := .of_isLocalization _ hq _
  have : Algebra.IsGeometricallyReduced k (Localization.AtPrime q) :=
    isGeometricallyReduced_localization q.primeCompl
  let : Field (Localization.AtPrime q) := Ring.KrullDimLE.isField_of_isReduced.toField
  exact nonempty_algHom_of_field (K := Localization.AtPrime q) (IsScalarTower.toAlgHom k R _)

end Langlands.CommutativeAlgebra.SeparablyClosedRationalPointProof
