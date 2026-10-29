import Langlands.AbelianScheme.FieldSymmetricMultiplicationPullbackStatement
import Langlands.AbelianScheme.FieldCubePullbackStatement
import Langlands.AlgebraicGeometry.Picard.LocalComparisonProof
import Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityProof
import Langlands.AlgebraicGeometry.Modules.TensorMonoidal
import Langlands.CategoryTheory.Picard.Basic
import Mathlib.Tactic.Ring

/-! # Symmetric multiplication pullback from the balanced cube identity -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.SemiCartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private theorem lineBundle_constant_pullback_trivial (K : Type u) [Field K]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of K))
    (e : Spec (CommRingCat.of K) ⟶ Y)
    (L : Langlands.AlgebraicGeometry.Picard.LineBundle Y) :
    Nonempty ((Scheme.Modules.pullback (p ≫ e)).obj L.obj ≅
      Langlands.Scheme.Modules.structureSheaf X) := by
  obtain ⟨h⟩ := Langlands.AlgebraicGeometry.Picard.fieldLineBundleTriviality K
    ((Langlands.AlgebraicGeometry.Picard.LineBundle.pullback e).obj L)
  exact ⟨((Scheme.Modules.pullbackComp p e).app L.obj).symm ≪≫
    (Scheme.Modules.pullback p).mapIso h ≪≫
      Langlands.Scheme.Modules.pullbackUnitIso p⟩

private theorem multiplication_pullback_zero (K : Type u) [Field K]
    (G : Grp (Over (Spec (CommRingCat.of K)))) [IsCommMonObj G.X]
    (L : Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left) :
    Nonempty ((Scheme.Modules.pullback (multiplication G (0 : ℤ)).hom.hom.left).obj L.obj ≅
      Langlands.Scheme.Modules.tensorPow L.obj 0) := by
  have hzero : (multiplication G (0 : ℤ)).hom.hom =
      toUnit G.X ≫ η[G.X] := by
    rw [multiplication_zero, Grp.Hom.hom_one, Mon.Hom.hom_one, Hom.one_def]
  rw [hzero]
  exact lineBundle_constant_pullback_trivial K (toUnit G.X).left η[G.X].left L

private theorem tensorObj_invertible {X : Scheme.{u}} {M N : X.Modules}
    (hM : Langlands.CategoryTheory.TensorInvertible M)
    (hN : Langlands.CategoryTheory.TensorInvertible N) :
    Langlands.CategoryTheory.TensorInvertible
      (Langlands.Scheme.Modules.tensorObj M N) :=
  Langlands.CategoryTheory.TensorInvertible.of_iso
    (Langlands.Scheme.Modules.localizedTensorIso X M N) (hM.tensor hN)

private theorem lineBundle_invertible {X : Scheme.{u}}
    (L : Langlands.AlgebraicGeometry.Picard.LineBundle X) :
    Langlands.CategoryTheory.TensorInvertible L.obj :=
  (Langlands.AlgebraicGeometry.Picard.locallyFreeRankOneIffTensorInvertible
    X L.obj).mpr L.property

private theorem lineBundle_pullback_invertible {X Y : Scheme.{u}}
    (f : X ⟶ Y) (L : Langlands.AlgebraicGeometry.Picard.LineBundle Y) :
    Langlands.CategoryTheory.TensorInvertible ((Scheme.Modules.pullback f).obj L.obj) :=
  (Langlands.AlgebraicGeometry.Picard.locallyFreeRankOneIffTensorInvertible
    X _).mpr (L.property.pullback f)

private theorem tensorPow_invertible {X : Scheme.{u}} (M : X.Modules)
    (hM : Langlands.CategoryTheory.TensorInvertible M) (n : ℕ) :
    Langlands.CategoryTheory.TensorInvertible
      (Langlands.Scheme.Modules.tensorPow M n) := by
  induction n with
  | zero => exact Langlands.CategoryTheory.TensorInvertible.unit
  | succ n ih => exact tensorObj_invertible hM ih

private theorem picard_tensorObj {X : Scheme.{u}} (M N : X.Modules)
    (hM : Langlands.CategoryTheory.TensorInvertible M)
    (hN : Langlands.CategoryTheory.TensorInvertible N)
    (hMN : Langlands.CategoryTheory.TensorInvertible
      (Langlands.Scheme.Modules.tensorObj M N)) :
    Langlands.CategoryTheory.PicardGroup.ofObject
        (Langlands.Scheme.Modules.tensorObj M N) hMN =
      Langlands.CategoryTheory.PicardGroup.ofObject M hM +
        Langlands.CategoryTheory.PicardGroup.ofObject N hN := by
  rw [← Langlands.CategoryTheory.PicardGroup.ofObject_tensor M N hM hN]
  exact (Langlands.CategoryTheory.PicardGroup.ofObject_eq_iff _ _ _ _).mpr
    ⟨(Langlands.Scheme.Modules.localizedTensorIso X M N).symm⟩

private theorem picard_tensorPow {X : Scheme.{u}} (M : X.Modules)
    (hM : Langlands.CategoryTheory.TensorInvertible M) (n : ℕ) :
    Langlands.CategoryTheory.PicardGroup.ofObject
        (Langlands.Scheme.Modules.tensorPow M n) (tensorPow_invertible M hM n) =
      n • Langlands.CategoryTheory.PicardGroup.ofObject M hM := by
  induction n with
  | zero => exact Langlands.CategoryTheory.PicardGroup.ofObject_unit
  | succ n ih =>
    refine (picard_tensorObj M _ hM (tensorPow_invertible M hM n) _).trans ?_
    rw [ih]
    exact (succ_nsmul' _ _).symm

private theorem quadratic_recurrence {A : Type*} [AddCommGroup A]
    (q : ℕ → A) (a : A) (h0 : q 0 = 0) (h1 : q 1 = a)
    (hrec : ∀ n, q (n + 2) + q n = q (n + 1) + q (n + 1) + (a + a)) :
    ∀ n, q n = (n * n) • a := by
  have hp : ∀ n, q n = (n * n) • a ∧
      q (n + 1) = ((n + 1) * (n + 1)) • a := by
    intro n
    induction n with
    | zero => simpa using And.intro h0 h1
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      apply add_right_cancel (b := q n)
      rw [hrec, ih.1, ih.2]
      have h : (n + 2) * (n + 2) + n * n =
          (n + 1) * (n + 1) + (n + 1) * (n + 1) + (1 + 1) := by ring
      simpa only [add_nsmul, one_nsmul] using congrArg (fun k : ℕ ↦ k • a) h.symm
  exact fun n ↦ (hp n).1

private theorem picard_cube_pullback
    (cube : FieldCubePullbackStatement.{u})
    (K : Type u) [Field K]
    (G : Grp (Over (Spec (CommRingCat.of K)))) [IsCommMonObj G.X]
    (hs : Smooth G.X.hom) (hp : IsProper G.X.hom)
    (hc : GeometricallyConnected G.X.hom)
    (T : Over (Spec (CommRingCat.of K))) (f g h : T ⟶ G.X)
    (L : Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left) :
    let q := fun (a : T ⟶ G.X) =>
      Langlands.CategoryTheory.PicardGroup.ofObject
        ((Scheme.Modules.pullback a.left).obj L.obj)
        (lineBundle_pullback_invertible a.left L)
    q (f * g * h) + (q f + (q g + q h)) =
      q (f * g) + (q (f * h) + q (g * h)) := by
  let invertible := fun (a : T ⟶ G.X) => lineBundle_pullback_invertible a.left L
  have heq := (Langlands.CategoryTheory.PicardGroup.ofObject_eq_iff _ _
    (tensorObj_invertible (invertible (f * g * h))
      (tensorObj_invertible (invertible f)
        (tensorObj_invertible (invertible g) (invertible h))))
    (tensorObj_invertible (invertible (f * g))
      (tensorObj_invertible (invertible (f * h)) (invertible (g * h))))).mpr
        (cube K G hs hp hc T f g h L)
  rw [picard_tensorObj _ _ (invertible (f * g * h))
      (tensorObj_invertible (invertible f)
        (tensorObj_invertible (invertible g) (invertible h))),
    picard_tensorObj _ _ (invertible f)
      (tensorObj_invertible (invertible g) (invertible h)),
    picard_tensorObj _ _ (invertible g) (invertible h),
    picard_tensorObj _ _ (invertible (f * g))
      (tensorObj_invertible (invertible (f * h)) (invertible (g * h))),
    picard_tensorObj _ _ (invertible (f * h)) (invertible (g * h))] at heq
  exact heq

/-- Conditional assembly: the unconditional balanced cube theorem is the
only remaining premise. -/
theorem fieldSymmetricMultiplicationPullbackOfCube
    (cube : FieldCubePullbackStatement.{u}) :
    FieldSymmetricMultiplicationPullbackStatement.{u} := by
  intro K _ G _ hs hp hc L hsym n _hn
  let m := fun (i : ℤ) => (multiplication G i).hom.hom
  let c := fun (f : G.X ⟶ G.X) =>
    Langlands.CategoryTheory.PicardGroup.ofObject
      ((Scheme.Modules.pullback f.left).obj L.obj)
      (lineBundle_pullback_invertible f.left L)
  let q := fun (k : ℕ) => c (m (k : ℤ))
  let a := Langlands.CategoryTheory.PicardGroup.ofObject L.obj (lineBundle_invertible L)
  have hzero : q 0 = 0 := by
    have heq := (Langlands.CategoryTheory.PicardGroup.ofObject_eq_iff _ _
      (lineBundle_pullback_invertible (m 0).left L)
      Langlands.CategoryTheory.TensorInvertible.unit).mpr
        (multiplication_pullback_zero K G L)
    exact heq.trans Langlands.CategoryTheory.PicardGroup.ofObject_unit
  have hone : q 1 = a := by
    apply (Langlands.CategoryTheory.PicardGroup.ofObject_eq_iff _ _ _ _).mpr
    exact ⟨by simpa only [m, Nat.cast_one, multiplication_one,
      Grp.id_hom_hom, Over.id_left, Functor.id_obj] using
      (Scheme.Modules.pullbackId G.X.left).app L.obj⟩
  have hminus : c (m (-1)) = a :=
    (Langlands.CategoryTheory.PicardGroup.ofObject_eq_iff _ _ _ _).mpr hsym
  have hmadd (i j : ℤ) : m i * m j = m (i + j) := by
    simp only [m, multiplication_hom, zpow_add]
  have hrec : ∀ k, q (k + 2) + q k =
      q (k + 1) + q (k + 1) + (a + a) := by
    intro k
    have h := picard_cube_pullback cube K G hs hp hc G.X
      (m ((k + 1 : ℕ) : ℤ)) (m 1) (m (-1)) L
    change c (m ((k + 1 : ℕ) : ℤ) * m 1 * m (-1)) +
        (c (m ((k + 1 : ℕ) : ℤ)) + (c (m 1) + c (m (-1)))) =
      c (m ((k + 1 : ℕ) : ℤ) * m 1) +
        (c (m ((k + 1 : ℕ) : ℤ) * m (-1)) + c (m 1 * m (-1))) at h
    simp only [hmadd] at h
    have hsum : ((k + 1 : ℕ) : ℤ) + 1 + (-1) = ((k + 1 : ℕ) : ℤ) := by omega
    have hsucc : ((k + 1 : ℕ) : ℤ) + 1 = ((k + 2 : ℕ) : ℤ) := by omega
    have hpred : ((k + 1 : ℕ) : ℤ) + (-1) = (k : ℤ) := by omega
    rw [hsum, hsucc, hpred, show (1 : ℤ) + (-1) = 0 from rfl] at h
    change q (k + 1) + (q (k + 1) + (q 1 + c (m (-1)))) =
      q (k + 2) + (q k + q 0) at h
    rw [hone, hminus, hzero, add_zero] at h
    simpa only [add_assoc] using h.symm
  apply (Langlands.CategoryTheory.PicardGroup.ofObject_eq_iff _ _
    (lineBundle_pullback_invertible (m (n : ℤ)).left L)
    (tensorPow_invertible L.obj (lineBundle_invertible L) (n * n))).mp
  exact (quadratic_recurrence q a hzero hone hrec n).trans
    (picard_tensorPow L.obj (lineBundle_invertible L) (n * n)).symm

/-- A chosen actual multiplication-pullback isomorphism, conditional on the
unconditional balanced cube statement. -/
def fieldSymmetricMultiplicationPullbackIsoOfCube
    (cube : FieldCubePullbackStatement.{u})
    (K : Type u) [Field K]
    (G : Grp (Over (Spec (CommRingCat.of K)))) [IsCommMonObj G.X]
    (hs : Smooth G.X.hom) (hp : IsProper G.X.hom)
    (hc : GeometricallyConnected G.X.hom)
    (L : Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left)
    (hsym : Nonempty
      ((Scheme.Modules.pullback (multiplication G (-1)).hom.hom.left).obj L.obj ≅ L.obj))
    (n : ℕ) (hn : 0 < n) :
    (Scheme.Modules.pullback (multiplication G (n : ℤ)).hom.hom.left).obj L.obj ≅
      Langlands.Scheme.Modules.tensorPow L.obj (n * n) :=
  Classical.choice
    (fieldSymmetricMultiplicationPullbackOfCube cube K G hs hp hc L hsym n hn)

end Langlands.GroupScheme
