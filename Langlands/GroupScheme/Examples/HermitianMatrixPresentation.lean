import Langlands.GroupScheme.Examples.HermitianMatrixTensorPoints
import Langlands.GroupScheme.Examples.HermitianMatrixReindex

/-! # All-test presentations by actual Hermitian matrices -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HermitianMatrix.SchemeModel

open SU3Root

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  {Idx : Type v} [Fintype Idx] [DecidableEq Idx]
  {Other : Type w} [Fintype Other] [DecidableEq Other]

/-- Reindex the actual tensor matrices on every test scheme. -/
def tensorReindexEquiv (H : Form (fieldInvolution k L) Idx) (r : Idx ≃ Other)
    (T : Over (Spec (CommRingCat.of k))) :
    tensorPoints k L H T ≃* tensorPoints k L (H.reindex r) T :=
  specialUnitaryReindexEquiv (tensorForm k L H T) r

@[simp] theorem tensorReindexEquiv_matrix (H : Form (fieldInvolution k L) Idx)
    (r : Idx ≃ Other) (T : Over (Spec (CommRingCat.of k)))
    (g : tensorPoints k L H T) :
    ((tensorReindexEquiv k L H r T g).1 : Matrix Other Other
      (SpecialLinear.WeilRoot.tensorAlgebra k L T)) =
      Matrix.reindex r r (g.1 : Matrix Idx Idx
        (SpecialLinear.WeilRoot.tensorAlgebra k L T)) := rfl

/-- Reindexing commutes with every actual test restriction. -/
theorem tensorReindexEquiv_naturality (H : Form (fieldInvolution k L) Idx)
    (r : Idx ≃ Other) {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T)
    (g : tensorPoints k L H T) :
    tensorPointsMap k L (H.reindex r) a (tensorReindexEquiv k L H r T g) =
      tensorReindexEquiv k L H r T' (tensorPointsMap k L H a g) := by
  apply Subtype.ext
  apply Units.ext
  rfl

/-- Supplied all-test presentation data; existence is a separate obligation. -/
structure Presentation (H : Form (fieldInvolution k L) Idx)
    (G : GroupScheme (Spec (CommRingCat.of k))) where
  pointsEquiv : ∀ T : Over (Spec (CommRingCat.of k)),
    (T ⟶ G.X) ≃* tensorPoints k L H T
  matrix_naturality : ∀ {T T' : Over (Spec (CommRingCat.of k))}
    (a : T' ⟶ T) (x : T ⟶ G.X),
    ((pointsEquiv T' (a ≫ x)).1 : Matrix Idx Idx
      (SpecialLinear.WeilRoot.tensorAlgebra k L T')) =
      ((pointsEquiv T x).1 : Matrix Idx Idx
        (SpecialLinear.WeilRoot.tensorAlgebra k L T)).map
          (SpecialLinear.WeilRoot.tensorMap k L a)

namespace Presentation

variable {k L} {H J : Form (fieldInvolution k L) Idx}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Matrix naturality is equality in the actual determinant-one subgroup. -/
theorem pointsEquiv_map (e : Presentation k L H G)
    {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T) (x : T ⟶ G.X) :
    e.pointsEquiv T' (a ≫ x) = tensorPointsMap k L H a (e.pointsEquiv T x) := by
  apply Subtype.ext
  apply Units.ext
  exact e.matrix_naturality a x

/-- Compose supplied presentation data with natural equivalences of actual points. -/
def transport {Jdx : Type w} [Fintype Jdx] [DecidableEq Jdx]
    {J : Form (fieldInvolution k L) Jdx} (e : Presentation k L H G)
    (E : ∀ T : Over (Spec (CommRingCat.of k)),
      tensorPoints k L H T ≃* tensorPoints k L J T)
    (hE : ∀ {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T)
      (g : tensorPoints k L H T),
      tensorPointsMap k L J a (E T g) = E T' (tensorPointsMap k L H a g)) :
    Presentation k L J G where
  pointsEquiv T := (e.pointsEquiv T).trans (E T)
  matrix_naturality {T T'} a x := by
    have hn := hE a (e.pointsEquiv T x)
    rw [← e.pointsEquiv_map a x] at hn
    exact congrArg (fun g : tensorPoints k L J T' =>
      (g.1 : Matrix Jdx Jdx (SpecialLinear.WeilRoot.tensorAlgebra k L T'))) hn.symm

/-- Transport a presentation by an actual invertible Gram congruence. -/
def isometry (e : Presentation k L H G) (P : Matrix.GeneralLinearGroup Idx L)
    (hP : adjoint (fieldInvolution k L) (P : Matrix Idx Idx L) *
      (J.gram : Matrix Idx Idx L) * (P : Matrix Idx Idx L) = H.gram) :
    Presentation k L J G :=
  e.transport (tensorIsometryEquiv k L H J P hP)
    (tensorIsometryEquiv_naturality k L H J P hP)

@[simp] theorem isometry_pointsEquiv (e : Presentation k L H G)
    (P : Matrix.GeneralLinearGroup Idx L)
    (hP : adjoint (fieldInvolution k L) (P : Matrix Idx Idx L) *
      (J.gram : Matrix Idx Idx L) * (P : Matrix Idx Idx L) = H.gram)
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X) :
    ((e.isometry P hP).pointsEquiv T x).1 =
      tensorMatrix k L P T * (e.pointsEquiv T x).1 * (tensorMatrix k L P T)⁻¹ := rfl

/-- Relabeling the finite indices transports the entire all-test presentation. -/
def reindex (e : Presentation k L H G) (r : Idx ≃ Other) :
    Presentation k L (H.reindex r) G :=
  e.transport (tensorReindexEquiv k L H r) (tensorReindexEquiv_naturality k L H r)

@[simp] theorem reindex_pointsEquiv_matrix (e : Presentation k L H G)
    (r : Idx ≃ Other) (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X) :
    (((e.reindex r).pointsEquiv T x).1 : Matrix Other Other
      (SpecialLinear.WeilRoot.tensorAlgebra k L T)) =
      Matrix.reindex r r ((e.pointsEquiv T x).1 : Matrix Idx Idx
        (SpecialLinear.WeilRoot.tensorAlgebra k L T)) := rfl

end Presentation

end Langlands.GroupScheme.HermitianMatrix.SchemeModel
