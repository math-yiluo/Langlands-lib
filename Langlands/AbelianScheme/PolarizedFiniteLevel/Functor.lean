import Langlands.AbelianScheme.PolarizedFiniteLevel.Base
import Langlands.AbelianScheme.PolarizedFiniteLevel.PullbackCoherence

/-! # The ordinary polarized full finite-level moduli functor -/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- The ordinary polarized degree-`d²`, full-level-`n` isomorphism-class functor
on every morphism between locally noetherian universe-zero schemes where `n`
is invertible. Its values lie in `Type 1`. -/
def moduliFunctor (P : Prerequisites.{0}) (g d n : ℕ) (_hd : 0 < d) (_hn : 3 ≤ n) :
    (LevelBase n)ᵒᵖ ⥤ Type 1 where
  obj S := Moduli P S.unop.obj g d n
  map b := TypeCat.ofHom (Moduli.pullback b.unop.hom)
  map_id S := by
    ext x
    exact Moduli.pullback_id x
  map_comp b c := by
    ext x
    exact Moduli.pullback_comp b.unop.hom c.unop.hom x

variable (P : Prerequisites.{0}) (g d n : ℕ) (hd : 0 < d) (hn : 3 ≤ n)

@[simp] theorem moduliFunctor_obj (S : LevelBase n) :
    (moduliFunctor P g d n hd hn).obj (.op S) = Moduli P S.obj g d n := rfl

/-- The restriction map takes the class of an actual datum to the class of its
constructed actual pullback. -/
@[simp] theorem moduliFunctor_map_classOf {S T : LevelBase n} (b : S ⟶ T)
    (a : Datum P T.obj g d n) :
    (moduliFunctor P g d n hd hn).map b.op a.classOf = (a.pullback b.hom).classOf :=
  rfl

/-- The same representative formula for any actual scheme morphism between
objects of the full base category. -/
theorem moduliFunctor_map_scheme_classOf {S T : LevelBase n} (b : S.obj ⟶ T.obj)
    (a : Datum P T.obj g d n) :
    (moduliFunctor P g d n hd hn).map (LevelBase.homMk b).op a.classOf =
      (a.pullback b).classOf := rfl

/-- At every restriction, any alternative changed dual evaluation gives the
same representative class as the constructed one. -/
theorem moduliFunctor_map_classOf_with {S T : LevelBase n} (b : S ⟶ T)
    (a : Datum P T.obj g d n)
    (W : DualWitness ((baseChange b.hom).obj a.abelian)) :
    (moduliFunctor P g d n hd hn).map b.op a.classOf =
      (a.pullbackWith b.hom W).classOf :=
  Moduli.pullback_classOf_with b.hom a W

end Langlands.AbelianScheme.PolarizedFiniteLevel
