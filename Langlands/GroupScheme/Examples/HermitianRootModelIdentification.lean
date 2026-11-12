import Langlands.GroupScheme.Examples.HermitianRootGroupScheme
import Langlands.GroupScheme.Torus.Split

/-! # Identifying the actual Hermitian group from all-test matrix points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HermitianRoot.SchemeModel

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  {Middle : Type} [Fintype Middle] [DecidableEq Middle]
  (H : DiagonalForm (SU3Root.fieldInvolution k L) Middle)
  (w : Middle → Lˣ) (hw : ∀ i, (w i : L) = H.weight i)
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (e : ∀ T : Over (Spec (CommRingCat.of k)),
    (T ⟶ G.X) ≃* specialUnitarySubgroup (tensorForm k L H T))
  (he : ∀ {T T' : Over (Spec (CommRingCat.of k))}
    (a : T' ⟶ T) (x : T ⟶ G.X),
    ((e T' (a ≫ x)).1 : Matrix (Index Middle) (Index Middle)
      (SpecialLinear.WeilRoot.tensorAlgebra k L T')) =
    ((e T x).1 : Matrix (Index Middle) (Index Middle)
      (SpecialLinear.WeilRoot.tensorAlgebra k L T)).map
        (SpecialLinear.WeilRoot.tensorMap k L a))

include he in
/-- Entrywise matrix naturality is naturality in the actual unitary subgroup. -/
theorem matrixPoints_map {T T' : Over (Spec (CommRingCat.of k))}
    (a : T' ⟶ T) (x : T ⟶ G.X) :
    e T' (a ≫ x) =
      specialUnitaryMap (SpecialLinear.WeilRoot.tensorMap k L a)
        (SU3Root.SchemeModel.tensorMap_bar k L a) (tensorMap_weight k L H a)
        (e T x) := by
  apply Subtype.ext
  apply Units.ext
  exact he a x

/-- A natural description of every test point as an actual unitary matrix identifies
the group scheme with the weighted Hermitian equalizer model. -/
def isoOfMatrixPoints : G ≅ groupScheme k L H w hw :=
  isoOfPointModels
    (fun T => specialUnitarySubgroup (tensorForm k L H T))
    (fun a => specialUnitaryMap (SpecialLinear.WeilRoot.tensorMap k L a)
      (SU3Root.SchemeModel.tensorMap_bar k L a) (tensorMap_weight k L H a))
    e (pointsEquiv k L H w hw)
    (matrixPoints_map k L H e he) (pointsEquiv_map k L H w hw)

/-- The constructed identification realizes the supplied matrix description. -/
theorem isoOfMatrixPoints_hom (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X) :
    pointsEquiv k L H w hw T
      (x ≫ (isoOfMatrixPoints k L H w hw e he).hom.hom.hom) = e T x :=
  isoOfPointModels_hom _ _ _ _ (matrixPoints_map k L H e he)
    (pointsEquiv_map k L H w hw) T x

/-- The inverse identification recovers the actual tensor matrix of a model point. -/
theorem isoOfMatrixPoints_inv (T : Over (Spec (CommRingCat.of k)))
    (y : T ⟶ (groupScheme k L H w hw).X) :
    e T (y ≫ (isoOfMatrixPoints k L H w hw e he).inv.hom.hom) =
      pointsEquiv k L H w hw T y :=
  isoOfPointModels_inv _ _ _ _ (matrixPoints_map k L H e he)
    (pointsEquiv_map k L H w hw) T y

include he in
/-- All-test matrix values uniquely determine the identification. -/
theorem isoOfMatrixPoints_unique (f : G ≅ groupScheme k L H w hw)
    (hf : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
      pointsEquiv k L H w hw T (x ≫ f.hom.hom.hom) = e T x) :
    f = isoOfMatrixPoints k L H w hw e he := by
  apply Iso.ext
  apply hom_ext_points
  intro T x
  apply (pointsEquiv k L H w hw T).injective
  rw [hf, isoOfMatrixPoints_hom]

end Langlands.GroupScheme.HermitianRoot.SchemeModel
