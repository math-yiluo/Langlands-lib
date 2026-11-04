import Langlands.GroupScheme.Lie.AffineCoordinates
import Langlands.GroupScheme.Lie.ElementCentralizer
import Langlands.CommutativeAlgebra.SemisimpleDerivation

/-! # The coordinate derivation of actual infinitesimal conjugation -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R))
variable {A B : Type u} [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B]

/-- Constant dual-number points commute with extension of coefficients. -/
@[simp] theorem constant_naturality (f : A →ₐ[R] B) (g : AffinePoints G A) :
    affineMap G (GeneralLinear.DualNumber.coefficientAlgMap f) (constant G g) =
      constant G (affineMap G f g) := by
  simp only [constant, ← affineMap_comp]
  have he : (GeneralLinear.DualNumber.coefficientAlgMap f).comp
      (TrivSqZeroExt.inlAlgHom R A A) =
      (TrivSqZeroExt.inlAlgHom R B B).comp f := by
    apply AlgHom.ext
    intro a
    apply TrivSqZeroExt.ext
    · rfl
    · exact map_zero f
  rw [he]

/-- Conjugation of a constant point by the scalar extension of an actual
identity-kernel point. -/
def infinitesimalConjugate (X : lieKernel G R) (g : AffinePoints G A) :
    AffinePoints G (DualNumber A) :=
  (lieKernelMap G (Algebra.ofId R A) X).val * constant G g *
    (lieKernelMap G (Algebra.ofId R A) X).val⁻¹

@[simp] theorem reduction_infinitesimalConjugate
    (X : lieKernel G R) (g : AffinePoints G A) :
    reduction G (infinitesimalConjugate G X g) = g := by
  have hx : reduction G (lieKernelMap G (Algebra.ofId R A) X).val = 1 :=
    (lieKernelMap G (Algebra.ofId R A) X).property
  simp only [infinitesimalConjugate, map_mul, map_inv, hx,
    reduction_constant, one_mul, inv_one, mul_one]

/-- Actual infinitesimal conjugation is natural on every affine test algebra. -/
theorem infinitesimalConjugate_naturality (f : A →ₐ[R] B)
    (X : lieKernel G R) (g : AffinePoints G A) :
    affineMap G (GeneralLinear.DualNumber.coefficientAlgMap f)
        (infinitesimalConjugate G X g) =
      infinitesimalConjugate G X (affineMap G f g) := by
  have hf : f.comp (Algebra.ofId R A) = Algebra.ofId R B := Subsingleton.elim _ _
  have hx : affineMap G (GeneralLinear.DualNumber.coefficientAlgMap f)
      (lieKernelMap G (Algebra.ofId R A) X).val =
      (lieKernelMap G (Algebra.ofId R B) X).val := by
    change (lieKernelMap G f (lieKernelMap G (Algebra.ofId R A) X)).val = _
    rw [← lieKernelMap_comp, hf]
  simp only [infinitesimalConjugate, map_mul, map_inv, hx, constant_naturality]

/-- Equality of the infinitesimal conjugate and the constant lift is the
actual centralizer condition. -/
theorem infinitesimalConjugate_eq_constant_iff
    (X : lieKernel G R) (g : AffinePoints G A) :
    infinitesimalConjugate G X g = constant G g ↔
      g ∈ (elementCentralizer G X).carrier
        ((algSpec R).obj (op (CommAlgCat.of R A))) := by
  rw [mem_elementCentralizer_affine_iff, ← commute_constant_iff]
  rw [infinitesimalConjugate, mul_inv_eq_iff_eq_mul]
  constructor
  · intro h
    exact (commute_iff_eq _ _).2 h.symm
  · intro h
    exact h.eq.symm

section Coordinates

variable [IsAffineHom G.X.hom]

/-- The affine point represented by the identity map on the coordinate algebra. -/
def universalPoint : AffinePoints G (coordinateAlgebra G) :=
  (pointCoordinates G).symm (AlgHom.id R (coordinateAlgebra G))

@[simp] theorem pointCoordinates_universalPoint :
    pointCoordinates G (universalPoint G) = AlgHom.id R (coordinateAlgebra G) :=
  (pointCoordinates G).apply_symm_apply _

/-- Every affine point is obtained from the universal point by its coordinate map. -/
@[simp] theorem affineMap_universalPoint (f : coordinateAlgebra G →ₐ[R] A) :
    affineMap G f (universalPoint G) = (pointCoordinates G).symm f := by
  apply (pointCoordinates G).injective
  simp only [pointCoordinates_naturality, pointCoordinates_universalPoint,
    AlgHom.comp_id, Equiv.apply_symm_apply]

/-- The algebra map induced by actual infinitesimal conjugation of the
universal point. -/
def conjugationLift (X : lieKernel G R) :
    coordinateAlgebra G →ₐ[R] DualNumber (coordinateAlgebra G) :=
  pointCoordinates G (infinitesimalConjugate G X (universalPoint G))

@[simp] theorem conjugationLift_fst (X : lieKernel G R) :
    (TrivSqZeroExt.fstHom R (coordinateAlgebra G) (coordinateAlgebra G)).comp
      (conjugationLift G X) = AlgHom.id R (coordinateAlgebra G) := by
  rw [conjugationLift, ← pointCoordinates_naturality]
  change pointCoordinates G (reduction G _) = _
  rw [reduction_infinitesimalConjugate, pointCoordinates_universalPoint]

/-- The global coordinate derivation obtained by differentiating actual
conjugation by the Lie element. -/
def conjugationDerivation (X : lieKernel G R) :
    Derivation R (coordinateAlgebra G) (coordinateAlgebra G) :=
  liftDerivation (conjugationLift G X) (conjugationLift_fst G X)

@[simp] theorem conjugationDerivation_apply (X : lieKernel G R)
    (c : coordinateAlgebra G) :
    conjugationDerivation G X c = (conjugationLift G X c).snd := rfl

/-- The dual-number lift of the derived coordinate derivation is the
original algebra map of actual conjugation. -/
theorem derivationLift_conjugationDerivation (X : lieKernel G R) :
    derivationLift (conjugationDerivation G X) = conjugationLift G X := by
  apply AlgHom.ext
  intro c
  apply TrivSqZeroExt.ext
  · exact (DFunLike.congr_fun (conjugationLift_fst G X) c).symm
  · rfl

/-- Coordinates of conjugation on an arbitrary affine test are obtained by
extending the universal dual-number lift along its actual point coordinates. -/
theorem pointCoordinates_infinitesimalConjugate
    (X : lieKernel G R) (g : AffinePoints G A) :
    pointCoordinates G (infinitesimalConjugate G X g) =
      (GeneralLinear.DualNumber.coefficientAlgMap (pointCoordinates G g)).comp
        (derivationLift (conjugationDerivation G X)) := by
  rw [derivationLift_conjugationDerivation]
  have hn := pointCoordinates_naturality G
    (GeneralLinear.DualNumber.coefficientAlgMap (pointCoordinates G g))
    (infinitesimalConjugate G X (universalPoint G))
  rw [infinitesimalConjugate_naturality, affineMap_universalPoint,
    Equiv.symm_apply_apply] at hn
  exact hn

/-- The infinitesimal coefficient of actual conjugation is evaluation of the
global derivation by the point's coordinate homomorphism. -/
theorem pointCoordinates_infinitesimalConjugate_snd
    (X : lieKernel G R) (g : AffinePoints G A) (c : coordinateAlgebra G) :
    (pointCoordinates G (infinitesimalConjugate G X g) c).snd =
      pointCoordinates G g (conjugationDerivation G X c) := by
  rw [pointCoordinates_infinitesimalConjugate]
  rfl

/-- Actual conjugation fixes a test point exactly when its coordinates
annihilate every value of the coordinate derivation. -/
theorem infinitesimalConjugate_eq_constant_iff_coordinates
    (X : lieKernel G R) (g : AffinePoints G A) :
    infinitesimalConjugate G X g = constant G g ↔
      ∀ c : coordinateAlgebra G,
        pointCoordinates G g (conjugationDerivation G X c) = 0 := by
  constructor
  · intro h c
    have hc := congrArg (fun p => (pointCoordinates G p c).snd) h
    rw [pointCoordinates_infinitesimalConjugate_snd] at hc
    simp only [constant, pointCoordinates_naturality] at hc
    exact hc
  · intro h
    apply (pointCoordinates G).injective
    rw [pointCoordinates_infinitesimalConjugate, constant,
      pointCoordinates_naturality]
    apply AlgHom.ext
    intro c
    apply TrivSqZeroExt.ext
    · rfl
    · exact h c

/-- The ideal of equations generated by actual infinitesimal conjugation. -/
def conjugationIdeal (X : lieKernel G R) : Ideal (coordinateAlgebra G) :=
  Ideal.span (Set.range (conjugationDerivation G X))

/-- The actual Lie-element centralizer is cut out on every affine test
algebra by the image ideal of the global conjugation derivation. -/
theorem mem_elementCentralizer_affine_iff_conjugationIdeal
    (X : lieKernel G R) (g : AffinePoints G A) :
    g ∈ (elementCentralizer G X).carrier
        ((algSpec R).obj (op (CommAlgCat.of R A))) ↔
      conjugationIdeal G X ≤ RingHom.ker (pointCoordinates G g).toRingHom := by
  rw [← infinitesimalConjugate_eq_constant_iff,
    infinitesimalConjugate_eq_constant_iff_coordinates]
  change (∀ c, pointCoordinates G g (conjugationDerivation G X c) = 0) ↔
    Ideal.span _ ≤ _
  rw [Ideal.span_le]
  constructor
  · intro h y hy
    obtain ⟨c, rfl⟩ := hy
    exact h c
  · intro h c
    exact h ⟨c, rfl⟩

end Coordinates

section Field

variable {k : Type u} [Field k]
  (H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom H.X.hom]

/-- Over a field, the actual conjugation ideal is the image ideal used by
the semisimple-derivation smooth-quotient theorem. -/
theorem conjugationIdeal_eq_imageIdeal (X : lieKernel H k) :
    conjugationIdeal H X =
      Langlands.Algebra.SemisimpleDerivation.imageIdeal (conjugationDerivation H X) :=
  rfl

end Field

end Langlands.GroupScheme.Lie
