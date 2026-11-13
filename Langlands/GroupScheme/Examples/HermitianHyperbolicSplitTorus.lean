import Langlands.GroupScheme.Examples.HermitianHyperbolicDiagonal
import Langlands.GroupScheme.Examples.HermitianMatrixPresentation
import Langlands.GroupScheme.Examples.SU3Cocharacter
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Torus.UnipotentQuotientClosed
import Mathlib.RingTheory.Flat.Basic

/-! # Actual closed split tori on several Hermitian hyperbolic planes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.HermitianRoot.MultiHyperbolic

open SU3Root HermitianMatrix
open HermitianMatrix.SchemeModel

section Coefficients

variable {A B : Type*} [CommRing A] [CommRing B]
  {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

omit [Fintype α] [Fintype β] [DecidableEq β] in
/-- The full hyperbolic block matrix commutes with coefficient change. -/
theorem gram_map (f : A →+* B) (M : Matrix β β A) :
    (gram (α := α) M).map f = gram (M.map f) := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [gram, apply_ite f]

end Coefficients

section Scheme

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  (r m : ℕ)

/-- Included scalar parameters, indexed by the actual hyperbolic planes. -/
def scalarParameters (T : Over (Spec (CommRingCat.of K))) :
    (ULift.{u} (Fin r) → (Γ(T.left, ⊤))ˣ) →*
      (Fin r → (SpecialLinear.WeilRoot.tensorAlgebra K L T)ˣ) where
  toFun t i := Units.map (SpecialLinear.WeilRoot.includeSections K L T).toMonoidHom
    (t (ULift.up i))
  map_one' := by funext i; simp
  map_mul' t s := by funext i; simp

omit [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L] in
/-- Scalar extension does not identify different ground-base parameters. -/
theorem scalarParameters_injective (T : Over (Spec (CommRingCat.of K))) :
    Function.Injective (scalarParameters K L r T) := by
  have hi : Function.Injective (SpecialLinear.WeilRoot.includeSections K L T) := by
    change Function.Injective (Algebra.TensorProduct.includeRight :
      SpecialLinear.WeilRoot.sectionAlgebra K T →ₐ[K]
        L ⊗[K] SpecialLinear.WeilRoot.sectionAlgebra K T)
    exact Algebra.TensorProduct.includeRight_injective
      (RingHom.injective (algebraMap K L))
  intro t s h
  funext i
  apply Units.ext
  apply hi
  exact congrArg (fun z : Fin r → (SpecialLinear.WeilRoot.tensorAlgebra K L T)ˣ =>
    (z i.down : SpecialLinear.WeilRoot.tensorAlgebra K L T)) h

/-- Every diagonal parameter is fixed by the coefficient involution. -/
theorem scalarParameters_bar (T : Over (Spec (CommRingCat.of K)))
    (t : ULift.{u} (Fin r) → (Γ(T.left, ⊤))ˣ) (i : Fin r) :
    (SU3Root.SchemeModel.coefficientInvolution K L T).bar
      (scalarParameters K L r T t i : SpecialLinear.WeilRoot.tensorAlgebra K L T) =
        (scalarParameters K L r T t i : SpecialLinear.WeilRoot.tensorAlgebra K L T) :=
  SU3Root.SchemeModel.sectionToTensor_bar K L T _

omit [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L] in
/-- Included parameters commute with all test-scheme restrictions. -/
theorem scalarParameters_map {T T' : Over (Spec (CommRingCat.of K))}
    (a : T' ⟶ T) (t : ULift.{u} (Fin r) → (Γ(T.left, ⊤))ˣ) :
    (fun i => Units.map (SpecialLinear.WeilRoot.tensorMap K L a).toMonoidHom
      (scalarParameters K L r T t i)) =
      scalarParameters K L r T'
        (fun i => Units.map a.left.appTop.hom.toMonoidHom (t i)) := by
  funext i
  apply Units.ext
  exact SpecialLinear.WeilRoot.tensorMap_includeSections K L a _

variable {K L r m}
  (H : Form (fieldInvolution K L) (Index (Fin r) (Fin m)))
  (M : Matrix (Fin m) (Fin m) L)
  (hH : (H.gram : Matrix (Index (Fin r) (Fin m)) (Index (Fin r) (Fin m)) L) = gram M)

include hH in
/-- The displayed block equation extends to every actual tensor coefficient ring. -/
theorem tensorForm_gram_eq (T : Over (Spec (CommRingCat.of K))) :
    ((tensorForm K L H T).gram : Matrix (Index (Fin r) (Fin m))
      (Index (Fin r) (Fin m)) (SpecialLinear.WeilRoot.tensorAlgebra K L T)) =
        gram (M.map (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L T))) := by
  rw [tensorForm_gram, hH, gram_map]

/-- The actual determinant-one diagonal isometries on each test scheme. -/
def torusMatrices (T : Over (Spec (CommRingCat.of K))) :
    (ULift.{u} (Fin r) → (Γ(T.left, ⊤))ˣ) →* tensorPoints K L H T :=
  (diagonal (β := Fin m)).comp (scalarParameters K L r T) |>.codRestrict
    (HermitianMatrix.specialUnitarySubgroup (tensorForm K L H T)) (fun t => by
      constructor
      · change HermitianMatrix.adjoint _ _ * _ * _ = _
        rw [tensorForm_gram_eq H M hH]
        exact diagonal_preserves _ _ _ (scalarParameters_bar K L r T t)
      · exact det_diagonal _)

@[simp] theorem torusMatrices_val (T : Over (Spec (CommRingCat.of K)))
    (t : ULift.{u} (Fin r) → (Γ(T.left, ⊤))ˣ) :
    (torusMatrices H M hH T t).1 = diagonal (scalarParameters K L r T t) := rfl

/-- The displayed diagonal matrices recover every input parameter. -/
theorem torusMatrices_injective (T : Over (Spec (CommRingCat.of K))) :
    Function.Injective (torusMatrices H M hH T) := by
  intro t s h
  apply scalarParameters_injective K L r T
  apply diagonal_injective (β := Fin m)
  exact congrArg Subtype.val h

/-- Restricting the actual matrices restricts exactly the scalar parameters. -/
theorem torusMatrices_map {T T' : Over (Spec (CommRingCat.of K))}
    (a : T' ⟶ T) (t : ULift.{u} (Fin r) → (Γ(T.left, ⊤))ˣ) :
    tensorPointsMap K L H a (torusMatrices H M hH T t) =
      torusMatrices H M hH T'
        (fun i => Units.map a.left.appTop.hom.toMonoidHom (t i)) := by
  apply Subtype.ext
  change Matrix.GeneralLinearGroup.map (SpecialLinear.WeilRoot.tensorMap K L a)
    (diagonal (scalarParameters K L r T t)) = _
  rw [diagonal_map, scalarParameters_map]
  rfl

variable {G : GroupScheme (Spec (CommRingCat.of K))}
  (e : Presentation K L H G)

/-- The split torus family on every actual test scheme of the supplied group. -/
def torusPoints (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (splitTorus (Spec (CommRingCat.of K)) (ULift.{u} (Fin r))).X) →*
      (T ⟶ G.X) :=
  (e.pointsEquiv T).symm.toMonoidHom.comp
    ((torusMatrices H M hH T).comp
      (splitTorus.pointsEquiv (ULift.{u} (Fin r)) T).toMonoidHom)

@[simp] theorem pointsEquiv_torusPoints (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (splitTorus (Spec (CommRingCat.of K)) (ULift.{u} (Fin r))).X) :
    e.pointsEquiv T (torusPoints H M hH e T x) =
      torusMatrices H M hH T (splitTorus.pointsEquiv (ULift.{u} (Fin r)) T x) :=
  (e.pointsEquiv T).apply_symm_apply _

/-- The torus family is natural on all test schemes. -/
theorem torusPoints_naturality {T T' : Over (Spec (CommRingCat.of K))}
    (a : T' ⟶ T)
    (x : T ⟶ (splitTorus (Spec (CommRingCat.of K)) (ULift.{u} (Fin r))).X) :
    torusPoints H M hH e T' (a ≫ x) = a ≫ torusPoints H M hH e T x := by
  apply (e.pointsEquiv T').injective
  rw [e.pointsEquiv_map, pointsEquiv_torusPoints, pointsEquiv_torusPoints,
    splitTorus.pointsEquiv_naturality, torusMatrices_map]
  rfl

/-- An actual split torus scaling each hyperbolic pair by inverse parameters. -/
def torusHom :
    splitTorus (Spec (CommRingCat.of K)) (ULift.{u} (Fin r)) ⟶ G :=
  homOfPoints (torusPoints H M hH e) (torusPoints_naturality H M hH e)

instance mono_torusHom : Mono (torusHom H M hH e).hom.hom := by
  constructor
  intro T g h hgh
  apply (splitTorus.pointsEquiv (ULift.{u} (Fin r)) T).injective
  have heq := congrArg (e.pointsEquiv T) hgh
  rw [torusHom, comp_homOfPoints, comp_homOfPoints,
    pointsEquiv_torusPoints, pointsEquiv_torusPoints] at heq
  exact torusMatrices_injective H M hH T heq

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- This actual diagonal split torus is a closed subgroup. -/
theorem isClosedSubgroup_torusHom : IsClosedSubgroup (torusHom H M hH e) := by
  have := isAffineHom_splitTorus (Spec (CommRingCat.of K)) (ULift.{u} (Fin r))
  exact IsTorus.isClosedSubgroup_of_mono
    (IsSplitTorus.isTorus (isSplitTorus_splitTorus _)) _

include H M hH e in
/-- Each displayed hyperbolic plane contributes one to the actual split rank. -/
theorem planes_le_splitRank : (r : ℕ∞) ≤ splitRank G := by
  simpa using card_le_splitRank (ULift.{u} (Fin r)) (torusHom H M hH e)
    (isClosedSubgroup_torusHom H M hH e)

end Scheme

end Langlands.GroupScheme.HermitianRoot.MultiHyperbolic
