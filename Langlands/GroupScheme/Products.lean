import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}}

/-- Points of a binary product, with the actual scheme group laws. -/
def productPointsEquiv (G H : GroupScheme S) (T : Over S) :
    (T ⟶ (G ⊗ H).X) ≃* (T ⟶ G.X) × (T ⟶ H.X) :=
  { homEquivToProd with
    map_mul' := fun x y => by
      apply Prod.ext <;> simp only [homEquivToProd, Prod.mul_def]
      · exact MonObj.mul_comp x y (fst G.X H.X)
      · exact MonObj.mul_comp x y (snd G.X H.X) }

@[simp] theorem productPointsEquiv_fst (G H : GroupScheme S) (T : Over S)
    (x : T ⟶ (G ⊗ H).X) : (productPointsEquiv G H T x).1 = x ≫ fst G.X H.X := rfl

@[simp] theorem productPointsEquiv_snd (G H : GroupScheme S) (T : Over S)
    (x : T ⟶ (G ⊗ H).X) : (productPointsEquiv G H T x).2 = x ≫ snd G.X H.X := rfl

/-- Binary product coordinates commute with arbitrary test-scheme maps. -/
theorem productPointsEquiv_naturality (G H : GroupScheme S)
    {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ (G ⊗ H).X) :
    productPointsEquiv G H T' (a ≫ x) =
      (a ≫ (productPointsEquiv G H T x).1, a ≫ (productPointsEquiv G H T x).2) := by
  apply Prod.ext <;> exact Category.assoc _ _ _

variable {I : Type u} [Finite I] (G : I → GroupScheme S)

/-- The categorical finite product of group schemes. -/
abbrev pi : GroupScheme S := ∏ᶜ G

/-- The underlying product fan is limiting because group objects create limits. -/
def piIsLimit : IsLimit (Fan.mk (pi G).X fun i => (Pi.π G i).hom.hom) :=
  isLimitOfHasProductOfPreservesLimit (Grp.forget (Over S)) G

/-- Points of a finite product are families of points, with componentwise multiplication. -/
def piPointsEquiv (T : Over S) :
    (T ⟶ (pi G).X) ≃* (∀ i, T ⟶ (G i).X) where
  toFun x i := x ≫ (Pi.π G i).hom.hom
  invFun x := Fan.IsLimit.lift (piIsLimit G) x
  left_inv x := by
    apply Fan.IsLimit.hom_ext (piIsLimit G)
    intro i
    exact Fan.IsLimit.fac (piIsLimit G) _ i
  right_inv x := by
    funext i
    exact Fan.IsLimit.fac (piIsLimit G) x i
  map_mul' x y := by
    funext i
    exact MonObj.mul_comp x y (Pi.π G i).hom.hom

@[simp] theorem piPointsEquiv_apply (T : Over S) (x : T ⟶ (pi G).X) (i : I) :
    piPointsEquiv G T x i = x ≫ (Pi.π G i).hom.hom := rfl

/-- The inverse is the unique scheme map with the given component points. -/
@[simp] theorem piPointsEquiv_symm_π (T : Over S) (x : ∀ i, T ⟶ (G i).X) (i : I) :
    (piPointsEquiv G T).symm x ≫ (Pi.π G i).hom.hom = x i :=
  Fan.IsLimit.fac (piIsLimit G) x i

/-- Finite product coordinates commute with arbitrary test-scheme maps. -/
theorem piPointsEquiv_naturality {T T' : Over S} (a : T' ⟶ T)
    (x : T ⟶ (pi G).X) :
    piPointsEquiv G T' (a ≫ x) = fun i => a ≫ piPointsEquiv G T x i := by
  funext i
  exact Category.assoc a x (Pi.π G i).hom.hom

/-- The presheaf of families of points of a finite family of group schemes. -/
def familyPoints : (Over S)ᵒᵖ ⥤ GrpCat where
  obj T := GrpCat.of (∀ i, T.unop ⟶ (G i).X)
  map a := GrpCat.ofHom {
    toFun := fun x i => a.unop ≫ x i
    map_one' := by funext i; exact MonObj.comp_one _
    map_mul' := by intro x y; funext i; exact MonObj.comp_mul _ _ _ }
  map_id T := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    funext i
    exact Category.id_comp (x i)
  map_comp a b := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    funext i
    exact Category.assoc b.unop a.unop (x i)

/-- The full group-valued point presheaf of the categorical finite product. -/
def piPointsIso : points (pi G) ≅ familyPoints G :=
  NatIso.ofComponents (fun T => (piPointsEquiv G T.unop).toGrpIso) (by
    intro T T' a
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact piPointsEquiv_naturality G a.unop x)

end Langlands.GroupScheme
