import Langlands.AlgebraicGeometry.PointTopology.GeometricRationalPoints
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Rational density after extension of the base field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Ordinary rational density implies geometric density for every field
extension, using the scalar extensions of the original sections. -/
def RationalDensityExtensionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Over (Spec (CommRingCat.of k))),
    HasDenseRationalPoints k X → HasDenseGeometricRationalPoints k K X

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- A section and its scalar extension form a Cartesian square. -/
theorem isPullback_geometricRationalPoint
    (X : Over (Spec (CommRingCat.of k))) (p : RationalPoint k X) :
    IsPullback (geometricRationalPoint (K := K) X p).left
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      p.left := by
  let a := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hp : p.left ≫ X.hom = 𝟙 (Spec (CommRingCat.of k)) := Over.w p
  have hsnd : (geometricRationalPoint (K := K) X p).left ≫
      pullback.snd X.hom a = 𝟙 (Spec (CommRingCat.of K)) :=
    Over.w (geometricRationalPoint (K := K) X p)
  have houter : IsPullback
      ((geometricRationalPoint (K := K) X p).left ≫ pullback.snd X.hom a)
      a a (p.left ≫ X.hom) := by
    rw [hp, hsnd]
    exact IsPullback.of_id_fst
  exact houter.of_right (geometricRationalPoint_fst X p)
    (IsPullback.of_hasPullback X.hom a).flip

/-- The image of an extended rational point is the full inverse image of its
ground-field image under the scalar-extension projection. -/
theorem range_geometricRationalPoint
    (X : Over (Spec (CommRingCat.of k))) (p : RationalPoint k X) :
    Set.range (geometricRationalPoint (K := K) X p).left =
      (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ⁻¹'
        Set.range p.left := by
  convert!
    Scheme.image_preimage_eq_of_isPullback
      (isPullback_geometricRationalPoint (K := K) X p).flip Set.univ using 1 <;>
    simp

/-- Ordinary rational density remains dense after any extension of the base
field, with the actual extended ground-field sections. -/
theorem hasDenseGeometricRationalPoints_of_hasDenseRationalPoints
    (X : Over (Spec (CommRingCat.of k))) (hX : HasDenseRationalPoints k X) :
    HasDenseGeometricRationalPoints k K X := by
  have h := hX.preimage
    (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))).isOpenMap
  simpa only [HasDenseGeometricRationalPoints, Set.preimage_iUnion,
    ← range_geometricRationalPoint (K := K) X] using h

end Langlands.AlgebraicGeometry.PointTopology
