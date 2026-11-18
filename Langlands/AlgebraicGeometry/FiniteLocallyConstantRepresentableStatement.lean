import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Sites.Over

/-! # Statement: finite locally constant étale sheaves are representable by finite étale schemes -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- **Representability of finite locally constant étale sheaves.** Let `F` be a sheaf of sets on
the big étale site of `S`. Suppose that on every member `𝒰.X i` of some étale cover of `S`, the
restriction of `F` is isomorphic to the constant presheaf of a finite set `A` (continuous maps to
`A` with the discrete topology). Then `F` is represented by a finite étale `S`-scheme. -/
def FiniteLocallyConstantRepresentableStatement : Prop :=
  ∀ (S : Scheme.{u}) (F : (Over S)ᵒᵖ ⥤ Type u),
    Presheaf.IsSheaf (Scheme.etaleTopology.over S) F →
    (∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S, ∀ i : 𝒰.I₀,
      ∃ A : Type u, Finite A ∧
        Nonempty ((Over.map (𝒰.f i)).op ⋙ F ≅
          letI : TopologicalSpace A := ⊥
          (Over.forget (𝒰.X i)).op ⋙ continuousMapPresheaf.{u, u} A)) →
    ∃ (X : Scheme.{u}) (q : X ⟶ S), IsFinite q ∧ Etale q ∧ Nonempty (F.RepresentableBy (Over.mk q))

end Langlands.AlgebraicGeometry
