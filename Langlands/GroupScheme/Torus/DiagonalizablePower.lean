import Langlands.GroupScheme.Torus.EndomorphismDichotomy
import Langlands.GroupScheme.Torus.DiagonalizableFaithfullyFlat
import Langlands.GroupScheme.Torus.KernelDiagonalizable

/-! # Power maps and diagonalizable character restrictions -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme

section Power

variable {S S' : Scheme.{u}} (G : GroupScheme S) [IsCommMonObj G.X]

/-- The actual power endomorphism of a commutative group scheme. -/
def powerHom (n : ℕ) : G ⟶ G := (𝟙 G) ^ n

theorem powerHom_points (n : ℕ) {U : Over S} (x : U ⟶ G.X) :
    x ≫ (powerHom G n).hom.hom = x ^ n := by
  simp [powerHom, Grp.Hom.hom_pow, Mon.Hom.hom_pow, MonObj.comp_pow]

theorem baseChange_powerHom (b : S' ⟶ S) (n : ℕ) :
    (GroupScheme.baseChange b).map (powerHom G n) =
      powerHom ((GroupScheme.baseChange b).obj G) n := by
  apply Grp.hom_ext
  change (Over.pullback b).map ((powerHom G n).hom.hom) = _
  simp only [powerHom, Grp.Hom.hom_pow, Mon.Hom.hom_pow]
  change (Over.pullback b).map ((𝟙 G.X) ^ n) =
    (𝟙 ((Over.pullback b).obj G.X)) ^ n
  simpa [Functor.homMonoidHom] using
    (map_pow (Functor.homMonoidHom (Over.pullback b)) (𝟙 G.X) n)

theorem powerHom_naturality {H : GroupScheme S} [IsCommMonObj H.X]
    (f : G ⟶ H) (n : ℕ) :
    powerHom G n ≫ f = f ≫ powerHom H n := by
  apply hom_ext_points
  intro U x
  simp only [Grp.comp_hom_hom, ← Category.assoc, powerHom_points]
  rw [MonObj.pow_comp]
  rw [MonObj.comp_pow]

end Power

namespace Diagonalizable

variable (R : CommRingCat.{u}) {A B C : Type u}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

theorem restrictMap_comp (g : B →+ A) (h : C →+ B) :
    restrictMap R g ≫ restrictMap R h = restrictMap R (g.comp h) := by
  apply hom_ext_points
  intro U x
  apply (characterPointsEquiv R C U).injective
  apply MonoidHom.ext
  intro c
  change characterPointsEquiv R C U
    ((x ≫ (restrictMap R g).hom.hom) ≫ (restrictMap R h).hom.hom) (.ofAdd c.toAdd) =
      characterPointsEquiv R C U
        (x ≫ (restrictMap R (g.comp h)).hom.hom) (.ofAdd c.toAdd)
  calc
    _ = characterPointsEquiv R B U (x ≫ (restrictMap R g).hom.hom)
        (.ofAdd (h c.toAdd)) :=
      pointsEquiv_restrictMap R h (x ≫ (restrictMap R g).hom.hom) c.toAdd
    _ = characterPointsEquiv R A U x (.ofAdd (g (h c.toAdd))) :=
      pointsEquiv_restrictMap R g x (h c.toAdd)
    _ = _ := (pointsEquiv_restrictMap R (g.comp h) x c.toAdd).symm

theorem restrictMap_nsmul_id (n : ℕ) :
    restrictMap R (n • AddMonoidHom.id A) = powerHom (groupScheme R A).toGrp n := by
  apply hom_ext_points
  intro U x
  apply (characterPointsEquiv R A U).injective
  apply MonoidHom.ext
  intro a
  change characterPointsEquiv R A U
      (x ≫ (restrictMap R (n • AddMonoidHom.id A)).hom.hom) (.ofAdd a.toAdd) =
    characterPointsEquiv R A U
      (x ≫ (powerHom (groupScheme R A).toGrp n).hom.hom) (.ofAdd a.toAdd)
  have heval : characterPointsEquiv R A U
      (x ≫ (restrictMap R (n • AddMonoidHom.id A)).hom.hom) (.ofAdd a.toAdd) =
      characterPointsEquiv R A U x (.ofAdd (n • a.toAdd)) :=
    pointsEquiv_restrictMap R (n • AddMonoidHom.id A) x a.toAdd
  rw [heval, powerHom_points, map_pow]
  change characterPointsEquiv R A U x (.ofAdd (n • a.toAdd)) =
    characterPointsEquiv R A U x a ^ n
  rw [ofAdd_nsmul, map_pow]
  rfl

end Diagonalizable
end Langlands.GroupScheme
