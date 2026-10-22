import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Integer multiplication on commutative group schemes

The integer power of the identity in the pointwise group of homomorphisms
constructs multiplication by every integer using the actual group law.
-/

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme

universe u

variable {S : Scheme.{u}}

/-- Multiplication by an integer on a commutative group scheme over `S`. -/
noncomputable def multiplication (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℤ) : G ⟶ G :=
  (𝟙 G) ^ n

@[simp]
lemma multiplication_hom (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℤ) :
    (multiplication G n).hom.hom = (𝟙 G.X) ^ n := by
  simp [multiplication]

/-- The morphism on every group of sections is the usual integer power map. -/
@[simp]
lemma points_multiplication (G : Grp (Over S)) [IsCommMonObj G.X]
    (n : ℤ) (T : Over S) (x : T ⟶ G.X) :
    x ≫ (multiplication G n).hom.hom = x ^ n := by
  simp [GrpObj.comp_zpow]

@[simp]
lemma multiplication_zero (G : Grp (Over S)) [IsCommMonObj G.X] :
    multiplication G 0 = 1 := by simp [multiplication]

@[simp]
lemma multiplication_one (G : Grp (Over S)) [IsCommMonObj G.X] :
    multiplication G 1 = 𝟙 G := by simp [multiplication]

lemma multiplication_add (G : Grp (Over S)) [IsCommMonObj G.X] (m n : ℤ) :
    multiplication G (m + n) = multiplication G m * multiplication G n := by
  simp [multiplication, zpow_add]

lemma multiplication_mul (G : Grp (Over S)) [IsCommMonObj G.X] (m n : ℤ) :
    multiplication G (m * n) = multiplication G m ≫ multiplication G n := by
  apply Grp.hom_ext
  simp [GrpObj.comp_zpow, zpow_mul]

/-- Integer multiplication commutes with all homomorphisms of commutative group schemes. -/
lemma multiplication_naturality {G H : Grp (Over S)}
    [IsCommMonObj G.X] [IsCommMonObj H.X] (f : G ⟶ H) (n : ℤ) :
    multiplication G n ≫ f = f ≫ multiplication H n := by
  apply Grp.hom_ext
  simp [GrpObj.zpow_comp, GrpObj.comp_zpow]

/-- The pullback group object inherits commutativity. -/
instance baseChange_isCommMonObj {S' : Scheme.{u}} (f : S' ⟶ S)
    (G : Grp (Over S)) [IsCommMonObj G.X] :
    IsCommMonObj ((Over.pullback f).mapGrp.obj G).X := by
  change IsCommMonObj ((Over.pullback f).obj G.X)
  infer_instance

/-- Multiplication commutes with pullback to an arbitrary base scheme. -/
lemma multiplication_baseChange {S' : Scheme.{u}} (f : S' ⟶ S)
    (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℤ) :
    (Over.pullback f).mapGrp.map (multiplication G n) =
      multiplication ((Over.pullback f).mapGrp.obj G) n := by
  apply Grp.hom_ext
  change (Over.pullback f).map ((multiplication G n).hom.hom) = _
  rw [multiplication_hom, multiplication_hom]
  simpa using! (Functor.homMonoidHom (Over.pullback f)).map_zpow (𝟙 G.X) n

end Langlands.GroupScheme
