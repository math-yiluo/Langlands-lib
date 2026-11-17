import Langlands.GroupScheme.RelativeUnipotent.RootWeightTorusAction
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.Rational.TorusCoordinateWeights

/-! # Actual homogeneous polynomial coordinates on root charts -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace AutomorphicAction

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  {I : Type u} [Fintype I]

/-- The actual action on the affine-point functor, over an arbitrary ring. -/
def affineTorusAction (b : AutomorphicAction (splitTorus (Spec R) I) G) :
    Corepresented.TorusAction G.affinePointFunctor I where
  act {A} s x := b.act (Corepresented.torusPt I A s) x
  act_one x := by rw [Corepresented.torusPt, map_one, b.act_one_left]
  act_mul s s' x := by rw [Corepresented.torusPt, map_mul, b.act_mul_left]
  act_map_mul s x y := b.act_mul_right _ x y
  naturality f s x := by
    change (algSpec R).map f.op ≫ b.act (Corepresented.torusPt I _ s) x = _
    rw [b.naturality, Corepresented.torusPt_naturality]
    rfl

end AutomorphicAction

namespace RelativeUnipotent.RootHeightChart

open LocalSplitCell Corepresented

variable {R : Type u} [CommRing R]
  {I J : Type u} [Fintype I] [DecidableEq I]
  {U G : GroupScheme (Spec (CommRingCat.of R))}
  {t : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {ch : J → I → ℤ} {fam : J → (Ga R ⟶ G)}
  (C : RootHeightChart U) (j : U ⟶ G) [Mono j.hom.hom]
  {index : Fin C.dimension → J}
  (hroot : ∀ k, C.roots (ULift.up k) ≫ j = fam (index k))
  (hu : TorusEquivariant t ch fam)

/-- The original polynomial algebra corepresents the actual group law on U.
The root chart itself need not be a group homomorphism. -/
abbrev polynomialCorepresentation :
    (U.affinePointFunctor ⋙ forget GrpCat).CorepresentableBy
      (VectorGroup.coordinateAlgebra (CommRingCat.of R) C.dimension) :=
  AffineLinearEmbedding.corepresentableBy U C.chart

/-- Affine algebra coordinates, after the section comparison, are precisely the
original ordered root coordinates. -/
theorem polynomialCoordinate_sections {A : CommAlgCat.{u} (CommRingCat.of R)}
    (x : U.affinePoints A) (k : Fin C.dimension) :
    (affineSectionsIso A).inv.hom
      (coord C.polynomialCorepresentation x (X k)) =
        C.coordinates ((algSpec (CommRingCat.of R)).obj (op A)) x k := by
  have h := congrArg (fun y => y.toAdd k)
    (pointsEquiv_eq_affinePointsEquiv
      (VectorGroup.functor (CommRingCat.of R) C.dimension)
      (VectorGroup.corepresentableBy (CommRingCat.of R) C.dimension) A
      (x ≫ C.chart.inv))
  exact h.symm

/-- The action on the polynomial corepresentation retains the actual torus
conjugation on U. -/
abbrev polynomialTorusAction : TorusAction U.affinePointFunctor I :=
  (C.torusAction j hroot hu).affineTorusAction

/-- The actual polynomial variables are homogeneous of exactly their root
characters, over the original arbitrary coefficient ring. -/
theorem isHomogeneous_polynomialVariable (k : Fin C.dimension) :
    IsHomogeneous C.polynomialCorepresentation (C.polynomialTorusAction j hroot hu)
      (ch (index k)) (X k) := by
  apply (isHomogeneous_iff_coord_act _ _ _ _).2
  intro A s x
  apply (ConcreteCategory.bijective_of_isIso (affineSectionsIso A).inv).1
  rw [map_mul, C.polynomialCoordinate_sections, C.polynomialCoordinate_sections]
  change C.coordinates _ ((C.torusAction j hroot hu).act (torusPt I A s) x) k = _
  rw [C.coordinates_torusAction j hroot hu]
  dsimp only
  rw [mul_comm]
  congr 1
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    (torusChar (ch (index k)) ((algSpec (CommRingCat.of R)).obj (op A))
      (torusPt I A s)) = _
  have hchar := charValue_torusPt (R := CommRingCat.of R) (A := A)
    (ch (index k)) s
  exact hchar.trans
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id _).symm

end RelativeUnipotent.RootHeightChart

end Langlands.GroupScheme
