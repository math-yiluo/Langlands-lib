import Langlands.AlgebraicGeometry.PointTopology.AffineDensity

/-! # Actual affine-space parametrizations and rational density -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- An actual dominant morphism from a nonempty open subscheme of a
finite-dimensional affine space over the ground field. -/
def IsUnirational (k : Type u) [Field k]
    (X : Over (Spec (CommRingCat.of k))) : Prop :=
  ∃ (ι : Type u) (_ : Finite ι)
      (U : (𝔸(ι; Spec (CommRingCat.of k))).Opens),
    (U : Set (𝔸(ι; Spec (CommRingCat.of k)))).Nonempty ∧
      ∃ f : Over.mk (U.ι ≫ (𝔸(ι; Spec (CommRingCat.of k)) ↘
          Spec (CommRingCat.of k))) ⟶ X,
        DenseRange f.left

/-- The rational points of an actual unirational scheme over an infinite
field are dense. -/
theorem IsUnirational.hasDenseRationalPoints
    {k : Type u} [Field k] [Infinite k]
    {X : Over (Spec (CommRingCat.of k))} (hX : IsUnirational k X) :
    HasDenseRationalPoints k X := by
  obtain ⟨ι, _, U, _, f, hf⟩ := hX
  exact hasDenseRationalPoints_of_denseRange f hf
    (hasDenseRationalPoints_open
      (Over.mk (𝔸(ι; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))) U
      (hasDenseRationalPoints_affineSpace k ι))

end Langlands.AlgebraicGeometry.PointTopology
