import Langlands.GroupScheme.Lie.ElementCentralizer
import Langlands.GroupScheme.Lie.ScalarExtensionCoordinates
import Langlands.GroupScheme.MatrixRepresentation.SchemeAction
import Langlands.GroupScheme.MatrixRepresentation.NormalFixedCoordinates
import Langlands.GroupScheme.StabilizerClosedSubgroup

/-! # Closed representability of actual Lie-element centralizers -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  [IsAffineHom G.X.hom] {d : ℕ} (c : FiniteCoordinates G d)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- The actual algebraic adjoint representation in natural finite Lie coordinates. -/
def adjointRepresentation : MatrixRepresentation G (Fin d) :=
  (AutomorphicAction.conjugation (𝟙 G)).finiteRepresentation c

/-- The coordinate representation acts by the actual adjoint action. -/
theorem adjointRepresentation_affineAction (A : CommAlgCat.{u} R)
    (g : G.affinePoints A) (X : Additive (lieKernel G A)) :
    (adjointRepresentation c).affineAction A g (c.equiv A X) =
      c.equiv A (adjoint G A g X) := by
  rw [adjointRepresentation, AutomorphicAction.finiteRepresentation_affineAction,
    AutomorphicAction.differential_conjugation, Grp.id_hom_hom, Category.comp_id]

private theorem hom_ext_of_affineRefinements {T Y : Over (Spec R)} {f g : T ⟶ Y}
    (h : ∀ (A : Type u) [CommRing A] [Algebra R A]
      (a : (algSpec R).obj (op (CommAlgCat.of R A)) ⟶ T), a ≫ f = a ≫ g) :
    f = g := by
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext T.left.affineOpenCover.openCover _ _ fun j => ?_
  let : Algebra R (T.left.affineOpenCover.X j) :=
    (Spec.preimage (T.left.affineOpenCover.f j ≫ T.hom)).hom.toAlgebra
  let a : (algSpec R).obj
      (op (CommAlgCat.of R (T.left.affineOpenCover.X j))) ⟶ T :=
    Over.homMk (T.left.affineOpenCover.f j) (by
      change _ = Spec.map (CommRingCat.ofHom (algebraMap R _))
      exact (Spec.map_preimage _).symm)
  exact congrArg CommaMorphism.left (h _ a)

/-- Over an affine test, fixing the coefficient vector of a Lie element is
exactly the original actual adjoint stabilizer equation. -/
theorem mem_adjointRepresentation_stabilizer_affine
    (X : lieKernel G R) (A : CommAlgCat.{u} R) (g : G.affinePoints A) :
    g ∈ ((adjointRepresentation c).schemeAction.stabilizer
      (MatrixRepresentation.constantCoefficientPoint
        (c.equiv (.of R R) (Additive.ofMul X)))).carrier
          ((algSpec R).obj (op A)) ↔
      g ∈ (elementCentralizer G X).carrier ((algSpec R).obj (op A)) := by
  rw [SchemeAction.mem_stabilizer, mem_elementCentralizer_adjoint_iff]
  rw [← (MatrixRepresentation.coefficientCoordinates_injective _).eq_iff]
  rw [MatrixRepresentation.coefficientCoordinates_act,
    MatrixRepresentation.coefficientCoordinates_constant]
  rw [MatrixRepresentation.affine_fixed_iff]
  let f : CommAlgCat.of R R ⟶ A := CommAlgCat.ofHom (Algebra.ofId R A)
  have hv := c.naturality f (Additive.ofMul X)
  change c.equiv A (lieKernelMapLinear G (Algebra.ofId R A) (Additive.ofMul X)) =
    (fun i => algebraMap R A (c.equiv (.of R R) (Additive.ofMul X) i)) at hv
  rw [← hv, ← MatrixRepresentation.affineAction_apply,
    adjointRepresentation_affineAction]
  exact (c.equiv A).injective.eq_iff

/-- The all-test centralizer of a Lie element is the actual closed stabilizer
of its constant coefficient vector in the adjoint representation. -/
theorem elementCentralizer_eq_adjointRepresentation_stabilizer
    (X : lieKernel G R) :
    elementCentralizer G X =
      (adjointRepresentation c).schemeAction.stabilizer
        (MatrixRepresentation.constantCoefficientPoint
          (c.equiv (.of R R) (Additive.ofMul X))) := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro g
  constructor
  · intro hg
    rw [SchemeAction.mem_stabilizer]
    apply hom_ext_of_affineRefinements
    intro A _ _ a
    have ha := (mem_adjointRepresentation_stabilizer_affine c X
      (.of R A) (a ≫ g)).2 ((elementCentralizer G X).comp_mem a hg)
    rw [SchemeAction.mem_stabilizer] at ha
    rw [SchemeAction.naturality, comp_toUnit_assoc]
    exact ha
  · intro hg A _ _ a
    have ha := (((adjointRepresentation c).schemeAction.stabilizer
      (MatrixRepresentation.constantCoefficientPoint
        (c.equiv (.of R R) (Additive.ofMul X)))).comp_mem a hg)
    have he := (mem_adjointRepresentation_stabilizer_affine c X (.of R A) (a ≫ g)).1 ha
    simpa only [Category.id_comp] using he A (𝟙 _)

include c in
/-- Finite natural Lie coordinates give an actual closed subgroup scheme
representing the Lie-element centralizer on every test scheme. -/
theorem elementCentralizer_isClosedRepresentable_of_finiteCoordinates
    (X : lieKernel G R) :
    (elementCentralizer G X).IsClosedRepresentable := by
  rw [elementCentralizer_eq_adjointRepresentation_stabilizer c X]
  exact SchemeAction.stabilizer_isClosedRepresentable _ _

variable {k : Type u} [Field k]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]

/-- For an affine locally finite type group over any field, every actual
Lie-element centralizer is a closed representable subgroup functor. -/
theorem elementCentralizer_isClosedRepresentable (X : lieKernel H k) :
    (elementCentralizer H X).IsClosedRepresentable :=
  elementCentralizer_isClosedRepresentable_of_finiteCoordinates (finiteCoordinates H) X

end Langlands.GroupScheme.Lie
