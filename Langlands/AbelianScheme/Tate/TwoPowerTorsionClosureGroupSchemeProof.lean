import Langlands.AbelianScheme.Tate.TwoPowerTorsionClosureGroupSchemeStatement
import Langlands.AbelianScheme.Tate.TwoPowerTorsionSmoothClosureProof
import Langlands.AbelianScheme.Tate.TwoPowerTorsionClosureGroupGeometry
import Langlands.CategoryTheory.GroupObjectDescent

/-! # A smooth proper group scheme realizing the actual torsion closure -/

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace Langlands.AbelianScheme.Tate

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem twoPowerTorsionClosureGroupScheme_exists :
    TwoPowerTorsionClosureGroupSchemeStatement.{u} := by
  intro K _ _ A
  obtain ⟨Y, i, hi, hs, hrange, ⟨e, he⟩, ⟨v, hv⟩, _⟩ :=
    twoPowerTorsionSmoothClosure_exists K A
  have : IsClosedImmersion i := hi
  have : Smooth (i ≫ A.X.hom) := hs
  let P := Over.mk (i ≫ A.X.hom)
  let j : P ⟶ A.X := Over.homMk i
  let e' : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P :=
    Over.homMk e (by
      change e ≫ i ≫ A.X.hom = 𝟙 _
      rw [← Category.assoc, he, Over.w]
      rfl)
  have he' : e' ≫ j = η[A.X] := by
    apply Over.OverMorphism.ext
    change e ≫ i = η[A.X].left
    change e ≫ i = (𝟙 (Spec (CommRingCat.of K))) ≫ η[A.X].left at he
    exact he.trans (Category.id_comp η[A.X].left)
  let v' : P ⟶ P := Over.homMk v.hom (by
    change v.hom ≫ i ≫ A.X.hom = i ≫ A.X.hom
    rw [← Category.assoc, hv, Category.assoc, Over.w])
  have hv' : v' ≫ j = j ≫ ι[A.X] :=
    Over.OverMorphism.ext hv
  obtain ⟨m, hm⟩ := exists_mul_on_smooth_twoPowerTorsionClosure A Y i hrange
  let := Langlands.CategoryTheory.GroupObjectDescent.grpObjOfMono
    j e' m v' he' hm hv'
  have : IsMonHom j :=
    Langlands.CategoryTheory.GroupObjectDescent.isMonHom_grpObjOfMono
      j e' m v' he' hm hv'
  have : IsCommMonObj P :=
    Langlands.CategoryTheory.GroupObjectDescent.commMonObjOfMono j
  let G : CommGroupScheme (Spec (CommRingCat.of K)) := { X := P }
  let f : G ⟶ A.toCommGroupScheme := Additive.ofMul (Grp.homMk j)
  exact ⟨G, f, hi, hs, inferInstanceAs (IsProper (i ≫ A.X.hom)), hrange⟩

end Langlands.AbelianScheme.Tate
