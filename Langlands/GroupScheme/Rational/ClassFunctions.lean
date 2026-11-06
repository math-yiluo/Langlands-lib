import Langlands.GroupScheme.Lie.AffineCoordinates
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Regular class functions and the canonical affine conjugation quotient -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ClassFunctions

variable {K : Type u} [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]

/-- The actual affine coordinate algebra presenting the given group scheme. -/
abbrev Coord : CommAlgCat (CommRingCat.of K) := Lie.coordinateAlgebra G

/-- The coordinate inclusion for the acting, left factor. -/
abbrev includeLeft : Coord G →ₐ[K] Coord G ⊗[K] Coord G :=
  Algebra.TensorProduct.includeLeft

/-- The coordinate inclusion for the point being conjugated, the right factor. -/
abbrev includeRight : Coord G →ₐ[K] Coord G ⊗[K] Coord G :=
  Algebra.TensorProduct.includeRight

/-- The first universal point over the tensor coordinate algebra. -/
def leftPoint : Lie.AffinePoints G (Coord G ⊗[K] Coord G) :=
  (Lie.pointCoordinates G).symm (includeLeft G)

/-- The second universal point over the tensor coordinate algebra. -/
def rightPoint : Lie.AffinePoints G (Coord G ⊗[K] Coord G) :=
  (Lie.pointCoordinates G).symm (includeRight G)

/-- The actual conjugation morphism of the given group scheme. -/
def conjugationHom : G.X ⊗ G.X ⟶ G.X :=
  fst G.X G.X * snd G.X G.X * (fst G.X G.X)⁻¹

omit [IsAffineHom G.X.hom] in
/-- Conjugation on every scheme-valued test is induced by the actual morphism. -/
theorem conjugationHom_apply {Z : Over (Spec (CommRingCat.of K))}
    (g x : Z ⟶ G.X) :
    lift g x ≫ conjugationHom G = g * x * g⁻¹ := by
  simp only [conjugationHom, MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd]

/-- Pullback by actual conjugation, expressed at the two universal points. -/
def conjugationPullback : Coord G →ₐ[K] Coord G ⊗[K] Coord G :=
  Lie.pointCoordinates G (leftPoint G * rightPoint G * (leftPoint G)⁻¹)

/-- The tensor formula is the coordinate pullback of the actual conjugation map. -/
theorem conjugationPullback_eq :
    conjugationPullback G =
      Lie.pointCoordinates G (lift (leftPoint G) (rightPoint G) ≫ conjugationHom G) := by
  rw [conjugationHom_apply]
  rfl

variable {A : Type u} [CommRing A] [Algebra K A]

/-- Evaluate the two tensor factors at any two actual coefficient points. -/
def tensorEvaluation (g x : Lie.AffinePoints G A) :
    Coord G ⊗[K] Coord G →ₐ[K] A :=
  Algebra.TensorProduct.lift (Lie.pointCoordinates G g) (Lie.pointCoordinates G x)
    (fun _ _ => Commute.all _ _)

@[simp] theorem tensorEvaluation_includeLeft (g x : Lie.AffinePoints G A) :
    (tensorEvaluation G g x).comp (includeLeft G) = Lie.pointCoordinates G g :=
  Algebra.TensorProduct.lift_comp_includeLeft _ _ _

@[simp] theorem tensorEvaluation_includeRight (g x : Lie.AffinePoints G A) :
    (tensorEvaluation G g x).comp (includeRight G) = Lie.pointCoordinates G x :=
  Algebra.TensorProduct.lift_comp_includeRight' _ _ _

@[simp] theorem tensorEvaluation_leftPoint (g x : Lie.AffinePoints G A) :
    Lie.affineMap G (tensorEvaluation G g x) (leftPoint G) = g := by
  apply (Lie.pointCoordinates G).injective
  rw [Lie.pointCoordinates_naturality, leftPoint, Equiv.apply_symm_apply,
    tensorEvaluation_includeLeft]

@[simp] theorem tensorEvaluation_rightPoint (g x : Lie.AffinePoints G A) :
    Lie.affineMap G (tensorEvaluation G g x) (rightPoint G) = x := by
  apply (Lie.pointCoordinates G).injective
  rw [Lie.pointCoordinates_naturality, rightPoint, Equiv.apply_symm_apply,
    tensorEvaluation_includeRight]

/-- Conjugation pullback evaluates at the actual conjugate over every coefficient algebra. -/
theorem evaluate_conjugationPullback (g x : Lie.AffinePoints G A) :
    (tensorEvaluation G g x).comp (conjugationPullback G) =
      Lie.pointCoordinates G (g * x * g⁻¹) := by
  unfold conjugationPullback
  rw [← Lie.pointCoordinates_naturality G (tensorEvaluation G g x)]
  simp only [map_mul, map_inv, tensorEvaluation_leftPoint, tensorEvaluation_rightPoint]

/-- The subalgebra of scheme-theoretically conjugation-invariant regular functions. -/
def algebra : Subalgebra K (Coord G) :=
  AlgHom.equalizer (conjugationPullback G) (includeRight G)

/-- The defining coordinate equalizer, exposed for consumers. -/
theorem mem_algebra {f : Coord G} :
    f ∈ algebra G ↔ conjugationPullback G f = includeRight G f := Iff.rfl

/-- Conjugation invariance is tested on every commutative coefficient algebra. -/
def IsInvariant (f : Coord G) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra K A] (g x : Lie.AffinePoints G A),
    Lie.pointCoordinates G (g * x * g⁻¹) f = Lie.pointCoordinates G x f

/-- The equalizer is exactly invariance on all algebra-valued points, including nilpotents. -/
theorem mem_algebra_iff_invariant {f : Coord G} :
    f ∈ algebra G ↔ IsInvariant G f := by
  constructor
  · intro hf A _ _ g x
    have h := congrArg (tensorEvaluation G g x) ((mem_algebra G).mp hf)
    have hc := DFunLike.congr_fun (evaluate_conjugationPullback G g x) f
    have hx := DFunLike.congr_fun (tensorEvaluation_includeRight G g x) f
    exact hc.symm.trans (h.trans hx)
  · intro hf
    apply (mem_algebra G).mpr
    simpa only [conjugationPullback, rightPoint, Equiv.apply_symm_apply] using
      hf (Coord G ⊗[K] Coord G) (leftPoint G) (rightPoint G)

/-- The inclusion whose spectrum defines the canonical quotient map. -/
abbrev inclusion : algebra G →ₐ[K] Coord G := (algebra G).val

/-- The invariant inclusion equalizes the actual conjugation and projection pullbacks. -/
theorem inclusion_equalizes :
    (conjugationPullback G).comp (inclusion G) =
      (includeRight G).comp (inclusion G) := by
  ext f
  exact f.property

/-- The spectrum of the actual regular class-function subalgebra. -/
def quotient : Over (Spec (CommRingCat.of K)) :=
  (algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K (algebra G)))

/-- The canonical map from the original group scheme to its affine class quotient. -/
def rho : G.X ⟶ quotient G :=
  (Lie.coordinateIso G).inv ≫
    (algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom (inclusion G)).op

/-- In the chosen actual coordinates, rho is precisely Spec of the inclusion. -/
theorem coordinateIso_hom_rho :
    (Lie.coordinateIso G).hom ≫ rho G =
      (algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom (inclusion G)).op := by
  simp [rho]

/-- Quotient points in the coordinates of the invariant subalgebra. -/
def quotientPointCoordinates :
    ((algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K A)) ⟶ quotient G) ≃
      (algebra G →ₐ[K] A) where
  toFun x := (algSpec.fullyFaithful.preimage x).unop.hom
  invFun f := (algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom f).op
  left_inv x := by exact algSpec.fullyFaithful.map_preimage x
  right_inv f := by simp

/-- On affine tests rho restricts the evaluation homomorphism to the invariant subalgebra. -/
theorem quotientPointCoordinates_rho (x : Lie.AffinePoints G A) :
    quotientPointCoordinates G (x ≫ rho G) =
      (Lie.pointCoordinates G x).comp (inclusion G) := by
  have hx : x = (algSpec (CommRingCat.of K)).map
      (CommAlgCat.ofHom (Lie.pointCoordinates G x)).op ≫ (Lie.coordinateIso G).hom :=
    ((Lie.pointCoordinates G).symm_apply_apply x).symm
  apply (quotientPointCoordinates G).symm.injective
  rw [Equiv.symm_apply_apply]
  change x ≫ rho G = (algSpec (CommRingCat.of K)).map
    (CommAlgCat.ofHom ((Lie.pointCoordinates G x).comp (inclusion G))).op
  conv_lhs => rw [hx, Category.assoc, coordinateIso_hom_rho]
  rw [CommAlgCat.ofHom_comp, op_comp, Functor.map_comp]

/-- Two affine points have the same quotient image exactly when all class functions agree. -/
theorem rho_eq_iff (y w : Lie.AffinePoints G A) :
    y ≫ rho G = w ≫ rho G ↔
      ∀ f : algebra G, Lie.pointCoordinates G y f.val = Lie.pointCoordinates G w f.val := by
  rw [← (quotientPointCoordinates G).injective.eq_iff,
    quotientPointCoordinates_rho, quotientPointCoordinates_rho]
  exact AlgHom.ext_iff

/-- Equal quotient images force equal values of every regular class function.
This applies in particular to every field extension of K. -/
theorem evaluation_eq_of_rho_eq (y w : Lie.AffinePoints G A)
    (h : y ≫ rho G = w ≫ rho G) (f : algebra G) :
    Lie.pointCoordinates G y f.val = Lie.pointCoordinates G w f.val :=
  (rho_eq_iff G y w).mp h f

/-- Rho is invariant on every affine test, including nonreduced coefficient algebras. -/
theorem rho_conjugation_affine (g x : Lie.AffinePoints G A) :
    (g * x * g⁻¹) ≫ rho G = x ≫ rho G := by
  apply (rho_eq_iff G _ _).mpr
  intro f
  exact (mem_algebra_iff_invariant G).mp f.property A g x

private def affineLift {Z : Over (Spec (CommRingCat.of K))} (x : Z ⟶ G.X) :
    (algSpec (CommRingCat.of K)).obj ((algΓ (CommRingCat.of K)).obj Z) ⟶ G.X :=
  (algSpec (CommRingCat.of K)).map
      (((algΓAlgSpecAdjunction (CommRingCat.of K)).homEquiv Z (op (Coord G))).symm
        (x ≫ (Lie.coordinateIso G).inv)) ≫
    (Lie.coordinateIso G).hom

private theorem affineLift_factor {Z : Over (Spec (CommRingCat.of K))}
    (x : Z ⟶ G.X) :
    (algΓAlgSpecAdjunction (CommRingCat.of K)).unit.app Z ≫ affineLift G x = x := by
  unfold affineLift
  rw [← Category.assoc]
  have h :
      (algΓAlgSpecAdjunction (CommRingCat.of K)).unit.app Z ≫
        (algSpec (CommRingCat.of K)).map
          (((algΓAlgSpecAdjunction (CommRingCat.of K)).homEquiv Z (op (Coord G))).symm
            (x ≫ (Lie.coordinateIso G).inv)) =
      x ≫ (Lie.coordinateIso G).inv :=
    ((algΓAlgSpecAdjunction (CommRingCat.of K)).homEquiv Z (op (Coord G))).apply_symm_apply _
  rw [h]
  simp

/-- The canonical quotient map is conjugation-invariant on every test scheme. -/
theorem rho_conjugation {Z : Over (Spec (CommRingCat.of K))} (g x : Z ⟶ G.X) :
    (g * x * g⁻¹) ≫ rho G = x ≫ rho G := by
  have h := rho_conjugation_affine G
    (A := ((algΓ (CommRingCat.of K)).obj Z).unop) (affineLift G g) (affineLift G x)
  have hh := congrArg
    (fun f => (algΓAlgSpecAdjunction (CommRingCat.of K)).unit.app Z ≫ f) h
  simpa only [← Category.assoc, MonObj.comp_mul, GrpObj.comp_inv, affineLift_factor] using hh

/-- The single morphism identity inducing invariance on all test schemes. -/
theorem conjugationHom_rho :
    conjugationHom G ≫ rho G = snd G.X G.X ≫ rho G :=
  rho_conjugation G (fst G.X G.X) (snd G.X G.X)

end Langlands.GroupScheme.ClassFunctions
