import Langlands.GroupScheme.CentralSimpleNormOne
import Langlands.GroupScheme.SpecialLinearBaseChange
import Langlands.GroupScheme.Reductive.SpecialLinear

/-! # Splitting the actual reduced-norm-one group scheme -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.CentralSimpleUnits.Splitting

open Langlands.CentralSimple Langlands.ReducedNorm

variable (K A : Type u) [Field K] [Ring A] [Algebra K A]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  {L : Type u} [Field L] [Algebra K L]
  (e : L ⊗[K] A ≃ₐ[L]
    Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) L)

section Coefficients

variable (R : Type v) [CommRing R] [Algebra K R] [Algebra L R]
  [IsScalarTower K L R]

/-- The splitting chart identifies actual norm-one units with all determinant-one matrices. -/
def coefficientEquiv :
    reducedNormOne K A R ≃* Matrix.SpecialLinearGroup (Fin (reducedDegree K A)) R where
  toFun x := ⟨extendSplittingChart e R (x.val : R ⊗[K] A), by
    rw [extendSplittingChart_apply, ← reducedNorm_eq_det K A e R]
    exact (mem_reducedNormOne K A R x.val).mp x.property⟩
  invFun g := ⟨Units.map (extendSplittingChart e R).symm.toMonoidHom
      (Matrix.SpecialLinearGroup.toGL g), by
    rw [mem_reducedNormOne, reducedNorm_eq_det K A e R]
    change (extendSplittingChart e R
      ((extendSplittingChart e R).symm (g : Matrix _ _ R))).det = 1
    rw [AlgEquiv.apply_symm_apply]
    exact g.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Units.ext
    exact (extendSplittingChart e R).symm_apply_apply _
  right_inv g := by
    apply Subtype.ext
    exact (extendSplittingChart e R).apply_symm_apply _
  map_mul' x y := by
    apply Subtype.ext
    exact _root_.map_mul (extendSplittingChart e R) _ _

@[simp] theorem coefficientEquiv_val (x : reducedNormOne K A R) :
    (coefficientEquiv K A e R x : Matrix _ _ R) =
      splittingMap e R (x.val : R ⊗[K] A) := rfl

end Coefficients

omit [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A] in
/-- The chart matrix is natural for every coefficient map respecting the splitting field. -/
theorem splittingMap_naturality
    {R S : Type v} [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    [Algebra L R] [Algebra L S] [IsScalarTower K L R] [IsScalarTower K L S]
    (f : R →ₐ[K] S) (hf : ∀ l : L, f (algebraMap L R l) = algebraMap L S l)
    (x : R ⊗[K] A) :
    splittingMap e S (Algebra.TensorProduct.map f (AlgHom.id K A) x) =
      (splittingMap e R x).map f := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    ext i j
    simp [splittingMap_tmul, hf]
  | add x y hx hy =>
    simp only [_root_.map_add, hx, hy]
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, _root_.map_add]

/-- The base map of the chosen splitting field. -/
abbrev baseMap : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K L))

/-- The section algebra with its original ground-field structure. -/
abbrev coefficients (T : Over (Spec (CommRingCat.of L))) : CommAlgCat K :=
  ((algΓ (CommRingCat.of K)).obj ((Over.map (baseMap (K := K) (L := L))).obj T)).unop

local instance sectionsAlgebra (T : Over (Spec (CommRingCat.of L))) :
    Algebra L (coefficients (K := K) T) :=
  inferInstanceAs (Algebra L ((algΓ (CommRingCat.of L)).obj T).unop)

local instance sectionsScalarTower (T : Over (Spec (CommRingCat.of L))) :
    IsScalarTower K L (coefficients (K := K) T) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro r
  change (T.hom ≫ baseMap (K := K) (L := L)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv r) =
    T.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of L)).inv (algebraMap K L r))
  rw [Scheme.Hom.comp_appTop]
  exact congrArg T.hom.appTop
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap K L))) r).symm

/-- All points of the actual pullback norm-one group are special-linear section matrices. -/
def basePointsEquiv (T : Over (Spec (CommRingCat.of L))) :
    (T ⟶ ((GroupScheme.baseChange (baseMap (K := K) (L := L))).obj
      (normOne K A)).X) ≃*
        Matrix.SpecialLinearGroup (Fin (reducedDegree K A)) Γ(T.left, ⊤) :=
  (baseChangePointsEquiv (baseMap (K := K) (L := L)) (normOne K A) T).trans
    ((normOnePointsEquiv K A ((Over.map (baseMap (K := K) (L := L))).obj T)).trans
      (coefficientEquiv K A e (coefficients (K := K) T)))

/-- The all-test splitting is given by the extended algebra chart on the actual tensor unit. -/
theorem basePointsEquiv_val (T : Over (Spec (CommRingCat.of L)))
    (x : T ⟶ ((GroupScheme.baseChange (baseMap (K := K) (L := L))).obj (normOne K A)).X) :
    (basePointsEquiv K A e T x : Matrix _ _ Γ(T.left, ⊤)) =
      splittingMap e (coefficients (K := K) T)
        ((normOnePointsEquiv K A ((Over.map (baseMap (K := K) (L := L))).obj T)
          (baseChangePointsEquiv (baseMap (K := K) (L := L)) (normOne K A) T x)).val :
            coefficients (K := K) T ⊗[K] A) := rfl

/-- The splitting respects every relative test restriction. -/
theorem basePointsEquiv_naturality
    {T T' : Over (Spec (CommRingCat.of L))} (a : T' ⟶ T)
    (x : T ⟶ ((GroupScheme.baseChange (baseMap (K := K) (L := L))).obj (normOne K A)).X) :
    basePointsEquiv K A e T' (a ≫ x) =
      Matrix.SpecialLinearGroup.map a.left.appTop.hom (basePointsEquiv K A e T x) := by
  apply Subtype.ext
  rw [basePointsEquiv_val, baseChangePointsEquiv_naturality,
    normOnePointsEquiv_naturality]
  change splittingMap e (coefficients (K := K) T')
    (Algebra.TensorProduct.map
      ((algΓ (CommRingCat.of K)).map ((Over.map (baseMap (K := K) (L := L))).map a)).unop.hom
      (AlgHom.id K A) _) = _
  rw [splittingMap_naturality K A e _ (fun l =>
    ((algΓ (CommRingCat.of L)).map a).unop.hom.commutes l)]
  rfl

/-- The actual reduced-norm-one group becomes the full special-linear group over a splitting field. -/
def splittingIso :
    (GroupScheme.baseChange (baseMap (K := K) (L := L))).obj (normOne K A) ≅
      SpecialLinear.groupScheme (Fin (reducedDegree K A)) (CommRingCat.of L) :=
  isoOfPointModels (fun T =>
      Matrix.SpecialLinearGroup (Fin (reducedDegree K A)) Γ(T.left, ⊤))
    (fun a => Matrix.SpecialLinearGroup.map a.left.appTop.hom)
    (basePointsEquiv K A e)
    (SpecialLinear.pointsEquiv (Fin (reducedDegree K A)) (CommRingCat.of L))
    (basePointsEquiv_naturality K A e)
    (fun {_ _} a y => SpecialLinear.pointsEquiv_naturality a y)

/-- The scheme isomorphism recovers the prescribed matrix on every test scheme. -/
theorem splittingIso_hom_points (T : Over (Spec (CommRingCat.of L)))
    (x : T ⟶ ((GroupScheme.baseChange (baseMap (K := K) (L := L))).obj (normOne K A)).X) :
    SpecialLinear.pointsEquiv (Fin (reducedDegree K A)) (CommRingCat.of L) T
      (x ≫ (splittingIso K A e).hom.hom.hom) = basePointsEquiv K A e T x :=
  isoOfPointModels_hom _ _ _ _ (basePointsEquiv_naturality K A e)
    (fun {_ _} a y => SpecialLinear.pointsEquiv_naturality a y) T x

end Langlands.GroupScheme.CentralSimpleUnits.Splitting
