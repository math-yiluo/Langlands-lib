import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.BaseChangeReflection

/-! # Solvability of rational points from geometric-point solvability -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section BasePointExtension

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (G : GroupScheme S)

/-- Pull a section of a group scheme back along an arbitrary base morphism. -/
def basePointExtension :
    (Over.mk (𝟙 S) ⟶ G.X) →*
      (Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange b).obj G).X) :=
  (baseChangePointsEquiv b G (Over.mk (𝟙 S'))).symm.toMonoidHom.comp
    (G.points.map
      (Over.homMk b (by simp) :
        (Over.map b).obj (Over.mk (𝟙 S')) ⟶ Over.mk (𝟙 S)).op).hom

/-- The extended section projects to the original section composed with the base map. -/
@[simp]
theorem basePointExtension_fst (x : Over.mk (𝟙 S) ⟶ G.X) :
    (basePointExtension b G x).left ≫
        CategoryTheory.Limits.pullback.fst G.X.hom b = b ≫ x.left := by
  have h := (baseChangePointsEquiv b G (Over.mk (𝟙 S'))).apply_symm_apply
    ((Over.homMk b (by simp) :
      (Over.map b).obj (Over.mk (𝟙 S')) ⟶ Over.mk (𝟙 S)) ≫ x)
  exact congrArg (fun y => y.left) h

/-- Pulling sections back along an epimorphism is injective. -/
theorem basePointExtension_injective [Epi b] :
    Function.Injective (basePointExtension b G) := by
  intro x y h
  apply Over.OverMorphism.ext
  apply (cancel_epi b).mp
  have h' := congrArg
    (fun z => z.left ≫ CategoryTheory.Limits.pullback.fst G.X.hom b) h
  exact (basePointExtension_fst b G x).symm.trans
    (h'.trans (basePointExtension_fst b G y))

end BasePointExtension

section Field

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Geometric-point solvability implies solvability of the rational-point group. -/
theorem IsSolvableGroupScheme.rationalPoints (h : IsSolvableGroupScheme G) :
    Group.IsSolvable (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) := by
  have hb := fieldExtension_fpqc k (AlgebraicClosure k)
  have : Flat (toAlgebraicClosure k) := hb.2.1
  have : Surjective (toAlgebraicClosure k) := hb.1
  have : Epi (toAlgebraicClosure k) :=
    Flat.epi_of_flat_of_surjective (toAlgebraicClosure k)
  have : Group.IsSolvable
      (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))) ⟶
        ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X) := h
  exact Group.isSolvable_of_isSolvable_injective
    (f := basePointExtension (toAlgebraicClosure k) G)
    (basePointExtension_injective (toAlgebraicClosure k) G)

end Field

end Langlands.GroupScheme
