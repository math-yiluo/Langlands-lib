import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Langlands.AlgebraicGeometry.Modules.SerreVanishing.Dimension
import Mathlib.RingTheory.KrullDimension.Field

/-! # Finite Krull dimension of affine group coordinates -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Nonzero finite-type algebras over a field have finite Krull dimension. -/
theorem finiteRingKrullDim_of_finiteType
    (k : Type u) [Field k] (A : Type v) [CommRing A] [Nontrivial A]
    [Algebra k A] [Algebra.FiniteType k A] : FiniteRingKrullDim A := by
  obtain ⟨n, hn⟩ := Langlands.AlgebraicGeometry.Modules.SerreVanishing.exists_ringKrullDim_le k A
  apply finiteRingKrullDim_iff_ne_bot_and_top.mpr
  constructor
  · exact ne_of_gt (lt_of_lt_of_le (by simp) ringKrullDim_nonneg_of_nontrivial)
  · exact (lt_of_le_of_lt hn (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top n))).ne

variable {k : Type u} [Field k]

/-- The actual scalar map from the ground field to global group coordinates. -/
def globalCoordinateAlgebraMap (G : GroupScheme (Spec (CommRingCat.of k))) :
    k →+* Γ(G.X.left, ⊤) :=
  G.X.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

/-- The actual global coordinates are finite type for an affine group locally of finite type. -/
theorem globalCoordinateAlgebraMap_finiteType
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] :
    (globalCoordinateAlgebraMap G).FiniteType := by
  have h₁ : G.X.hom.appTop.hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  have h₀ : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2
  exact h₁.comp h₀

/-- The identity section forces the global coordinate ring of a group over a field to be nonzero. -/
theorem globalCoordinates_nontrivial
    (G : GroupScheme (Spec (CommRingCat.of k))) : Nontrivial Γ(G.X.left, ⊤) := by
  let ε : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := 1
  exact ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.comp ε.left.appTop.hom).domain_nontrivial

/-- A natural-number upper bound for the Krull dimension of the actual global coordinate ring. -/
theorem globalCoordinates_exists_dimensionBound
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] :
    ∃ n : ℕ, ringKrullDim Γ(G.X.left, ⊤) ≤ n := by
  let : Algebra k Γ(G.X.left, ⊤) := (globalCoordinateAlgebraMap G).toAlgebra
  have : Algebra.FiniteType k Γ(G.X.left, ⊤) := globalCoordinateAlgebraMap_finiteType G
  exact Langlands.AlgebraicGeometry.Modules.SerreVanishing.exists_ringKrullDim_le k Γ(G.X.left, ⊤)

/-- A chosen finite Krull-dimension bound for an affine group locally of finite type. -/
def coordinateKrullDimensionBound
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] : ℕ :=
  Classical.choose (globalCoordinates_exists_dimensionBound G)

theorem ringKrullDim_globalCoordinates_le
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] :
    ringKrullDim Γ(G.X.left, ⊤) ≤ coordinateKrullDimensionBound G :=
  Classical.choose_spec (globalCoordinates_exists_dimensionBound G)

/-- Actual affine finite-type group coordinates have finite Krull dimension. -/
theorem globalCoordinates_finiteRingKrullDim
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] :
    FiniteRingKrullDim Γ(G.X.left, ⊤) := by
  let : Algebra k Γ(G.X.left, ⊤) := (globalCoordinateAlgebraMap G).toAlgebra
  have : Algebra.FiniteType k Γ(G.X.left, ⊤) := globalCoordinateAlgebraMap_finiteType G
  have : Nontrivial Γ(G.X.left, ⊤) := globalCoordinates_nontrivial G
  exact finiteRingKrullDim_of_finiteType k Γ(G.X.left, ⊤)

end Langlands.GroupScheme
