import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.KrullDimension

/-! # Finite covers by relative Noether-normalization pieces -/

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.LangWeil

/-- Geometric normalization pieces for a morphism. The covering condition concerns
actual field-valued points, and the dimension comparison concerns its actual fibres. -/
structure FiniteNormalizationCover {S X : Scheme.{u}} (f : X ⟶ S) where
  count : ℕ
  base : Fin count → Scheme.{u}
  source : Fin count → Scheme.{u}
  baseAffine : ∀ i, IsAffine (base i)
  baseMap : ∀ i, base i ⟶ S
  baseImmersion : ∀ i, IsImmersion (baseMap i)
  sourceMap : ∀ i, source i ⟶ X
  sourceImmersion : ∀ i, IsImmersion (sourceMap i)
  dimension : Fin count → ℕ
  normalization : ∀ i, source i ⟶ AffineSpace (ULift.{u} (Fin (dimension i))) (base i)
  normalizationFinite : ∀ i, IsFinite (normalization i)
  normalizationSurjective : ∀ i, Function.Surjective (normalization i)
  over : ∀ i, normalization i ≫
    (AffineSpace (ULift.{u} (Fin (dimension i))) (base i) ↘ base i) ≫ baseMap i =
      sourceMap i ≫ f
  covers : ∀ (K : Type u) [Field K] (x : Spec (.of K) ⟶ X),
    ∃ (i : Fin count) (z : Spec (.of K) ⟶ source i), z ≫ sourceMap i = x
  dimension_le : ∀ (i : Fin count) (t : base i),
    (dimension i : WithBot ℕ∞) ≤ topologicalKrullDim (f.fiber (baseMap i t))

/-- A finite-type morphism over a Noetherian scheme has finitely many relative
Noether-normalization pieces, with exponents bounded by its fibre dimensions. -/
def FiniteNormalizationCoverStatement : Prop :=
  ∀ (S X : Scheme.{u}) (f : X ⟶ S), IsNoetherian S →
    LocallyOfFiniteType f → QuasiCompact f → Nonempty (FiniteNormalizationCover f)

end Langlands.AlgebraicGeometry.LangWeil
