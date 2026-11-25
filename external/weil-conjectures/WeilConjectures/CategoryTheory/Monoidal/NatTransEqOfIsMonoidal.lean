/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Monoidal natural transformations out of a monoidal left adjoint on abelian groups

Let `F : Ab ⥤ D` be a strong monoidal functor which is a left adjoint, for instance the constant
(pre)sheaf functor, and `G : Ab ⥤ D` a lax monoidal functor. Then there is at most one monoidal
natural transformation `F ⟶ G` (`CategoryTheory.NatTrans.eq_of_isMonoidal`).

Indeed, by adjunction a natural transformation `τ : F ⟶ G` is a natural family of morphisms
`A ⟶ R(G A)` of abelian groups, where `R` is the right adjoint of `F`. Such a family is
determined by its component at the unit `ℤ = 𝟙_ Ab`, every element `a` of `A` being the image of
`1` under the morphism `ℤ ⟶ A`, `n ↦ n • a`. Finally the component of a monoidal `τ` at the
unit is determined by the unit comparison maps: `τ.app (𝟙_ Ab) = (ε F)⁻¹ ≫ ε G`.

This rigidity is what makes the coefficient comparisons of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison` compatible with each other
without any computation.
-/

@[expose] public section

universe w v u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

namespace CategoryTheory.NatTrans

variable {D : Type u} [Category.{v} D] [MonoidalCategory D] {F G : Ab.{w} ⥤ D} [F.Monoidal]
  [G.LaxMonoidal] [F.IsLeftAdjoint]

/-- Two monoidal natural transformations from a strong monoidal left adjoint `F : Ab ⥤ D` to a
lax monoidal functor agree. -/
theorem eq_of_isMonoidal (τ₁ τ₂ : F ⟶ G) [NatTrans.IsMonoidal τ₁] [NatTrans.IsMonoidal τ₂] :
    τ₁ = τ₂ := by
  let adj := Adjunction.ofIsLeftAdjoint F
  have h₁ : τ₁.app (𝟙_ Ab.{w}) = τ₂.app (𝟙_ Ab.{w}) := by
    rw [← cancel_epi (ε F), NatTrans.IsMonoidal.unit, NatTrans.IsMonoidal.unit]
  ext A : 2
  apply (adj.homEquiv _ _).injective
  ext a
  let â : 𝟙_ Ab.{w} ⟶ A :=
    AddCommGrpCat.ofHom
      (AddMonoidHom.mk' (fun n : ULift.{w} ℤ ↦ n.down • a) fun _ _ ↦ add_smul _ _ _)
  have key (τ : F ⟶ G) : (adj.homEquiv _ _ (τ.app A)).hom a =
      (adj.homEquiv _ _ (τ.app (𝟙_ Ab.{w})) ≫ F.rightAdjoint.map (G.map â)).hom
        (ULift.up 1) := by
    rw [← Adjunction.homEquiv_naturality_right, ← τ.naturality,
      Adjunction.homEquiv_naturality_left]
    exact congrArg (adj.homEquiv _ _ (τ.app A)).hom (one_smul ℤ a).symm
  rw [key τ₁, key τ₂, h₁]

end CategoryTheory.NatTrans
