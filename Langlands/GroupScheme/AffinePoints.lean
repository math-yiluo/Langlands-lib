import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Group.Affine

/-! # Coefficient points of an actual group scheme -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Lie

variable {R : CommRingCat.{u}}

/-- Points on an actual affine test algebra over the fixed base ring. -/
abbrev AffinePoints (G : GroupScheme (Spec R))
    (A : Type u) [CommRing A] [Algebra R A] :=
  (algSpec R).obj (op (CommAlgCat.of R A)) ⟶ G.X

variable (G : GroupScheme (Spec R))
variable {A B C : Type u} [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]

/-- An algebra map acts on points by precomposing its spectrum map. -/
def affineMap (f : A →ₐ[R] B) : AffinePoints G A →* AffinePoints G B :=
  (G.points.map ((algSpec R).map (CommAlgCat.ofHom f).op).op).hom

@[simp] theorem affineMap_apply (f : A →ₐ[R] B) (x : AffinePoints G A) :
    affineMap G f x = (algSpec R).map (CommAlgCat.ofHom f).op ≫ x := rfl

@[simp] theorem affineMap_id (x : AffinePoints G A) :
    affineMap G (AlgHom.id R A) x = x := by
  simp [affineMap_apply]

@[simp] theorem affineMap_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C)
    (x : AffinePoints G A) :
    affineMap G (g.comp f) x = affineMap G g (affineMap G f x) := by
  simp [affineMap_apply, ← Category.assoc, ← Functor.map_comp]

end Lie

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R))

/-- The covariant algebra-point functor, obtained by restricting the group-valued Yoneda
functor to affine test schemes. -/
abbrev affinePointFunctor : CommAlgCat.{u} R ⥤ GrpCat.{u} :=
  (algSpec R).rightOp ⋙ G.points

/-- Actual scheme points with coefficients in an algebra over the base. -/
abbrev affinePoints (A : CommAlgCat.{u} R) :=
  (algSpec R).obj (op A) ⟶ G.X

/-- Extension of coefficients is pullback along the actual spectrum map. -/
def affinePointMap {A B : CommAlgCat.{u} R} (f : A ⟶ B) :
    G.affinePoints A →* G.affinePoints B :=
  Lie.affineMap G f.hom

@[simp] theorem affinePointMap_apply {A B : CommAlgCat.{u} R} (f : A ⟶ B)
    (x : G.affinePoints A) :
    G.affinePointMap f x = (algSpec R).map f.op ≫ x := rfl

@[simp] theorem affinePointMap_id (A : CommAlgCat.{u} R) :
    G.affinePointMap (𝟙 A) = MonoidHom.id (G.affinePoints A) := by
  ext x
  simp [affinePointMap_apply]

@[simp] theorem affinePointMap_comp {A B C : CommAlgCat.{u} R}
    (f : A ⟶ B) (g : B ⟶ C) :
    G.affinePointMap (f ≫ g) = (G.affinePointMap g).comp (G.affinePointMap f) := by
  ext x
  simp [affinePointMap_apply]

/-- A group-scheme homomorphism acts on coefficient points by postcomposition. -/
def affinePointsTarget {H : GroupScheme (Spec R)} (f : G ⟶ H)
    (A : CommAlgCat.{u} R) : G.affinePoints A →* H.affinePoints A :=
  ((pointsMap f).app (op ((algSpec R).obj (op A)))).hom

@[simp] theorem affinePointsTarget_apply {H : GroupScheme (Spec R)} (f : G ⟶ H)
    (A : CommAlgCat.{u} R) (x : G.affinePoints A) :
    G.affinePointsTarget f A x = x ≫ f.hom.hom := rfl

/-- Coefficient extension commutes with homomorphisms of group schemes. -/
theorem affinePointsTarget_naturality {H : GroupScheme (Spec R)} (f : G ⟶ H)
    {A B : CommAlgCat.{u} R} (a : A ⟶ B) :
    (H.affinePointMap a).comp (G.affinePointsTarget f A) =
      (G.affinePointsTarget f B).comp (G.affinePointMap a) := by
  ext x
  simp [affinePointMap_apply, affinePointsTarget_apply]

end Langlands.GroupScheme
