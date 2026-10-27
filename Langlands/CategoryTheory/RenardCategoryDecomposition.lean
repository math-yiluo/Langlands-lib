import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Renard A.IX: decompositions of a category by full subcategories

Source: Renard, *Représentations des groupes réductifs p-adiques* (French edition
dated 9 July 2026), Appendix A.IX, printed page 268 / PDF page 274.

For a family `P : I → ObjectProperty C` of full subcategories, the source writes
`𝓜 = ∏ᵢ 𝓜ᵢ` when every object is a direct sum of one object from each `𝓜ᵢ` and
all Hom groups between objects of distinct `𝓜ᵢ` are zero. The two conditions are
defined separately and then combined. The direct-sum condition asks for an actual
coproduct cofan with the ambient object as vertex; it needs only a category. The
Hom condition needs zero morphisms. Object universe `u`, Hom universe `v` and
index universe `w` are independent, and `I` may be empty. The source's
Grothendieck and AB6 hypotheses are not needed to form the definitions, and no
consequence of a decomposition is asserted.
-/

universe w v u

open CategoryTheory Limits

namespace Langlands.Renard

variable {C : Type u} [Category.{v} C] {I : Type w}

section Coproduct

/-- Renard A.IX, for one object: `X` is the vertex of an actual coproduct cofan
`(ιᵢ : Yᵢ ⟶ X)ᵢ` whose component `Yᵢ` lies in the full subcategory `P i` for
every `i`. -/
def IsCoproductOfComponents (P : I → ObjectProperty C) (X : C) : Prop :=
  ∃ (Y : I → C) (ι : ∀ i, Y i ⟶ X),
    (∀ i, P i (Y i)) ∧ Nonempty (IsColimit (Cofan.mk X ι))

/-- Renard A.IX, first condition of `𝓜 = ∏ᵢ 𝓜ᵢ`: every object is the vertex of
an actual coproduct cofan with one component from each full subcategory `P i`. -/
def EveryObjectIsCoproductOfComponents (P : I → ObjectProperty C) : Prop :=
  ∀ X : C, IsCoproductOfComponents P X

/-- The per-object condition, with components taken as objects of the actual full
subcategories `(P i).FullSubcategory` and mapped to `C` by their inclusions
`(P i).ι`. -/
theorem isCoproductOfComponents_iff_fullSubcategory (P : I → ObjectProperty C) (X : C) :
    IsCoproductOfComponents P X ↔
      ∃ (Y : ∀ i, (P i).FullSubcategory) (ι : ∀ i, (P i).ι.obj (Y i) ⟶ X),
        Nonempty (IsColimit (Cofan.mk X ι)) := by
  constructor
  · rintro ⟨Y, ι, hY, hc⟩
    exact ⟨fun i => ⟨Y i, hY i⟩, ι, hc⟩
  · rintro ⟨Y, ι, hc⟩
    exact ⟨fun i => (Y i).obj, ι, fun i => (Y i).property, hc⟩

/-- When the component family has a chosen coproduct, a cofan with vertex `X` is
a coproduct exactly when the induced map `∐ Y ⟶ X` is an isomorphism. This is
Mathlib's `Cofan.nonempty_isColimit_iff_isIso_sigmaDesc` for `Cofan.mk X ι`. -/
theorem nonempty_isColimit_cofanMk_iff_isIso_sigmaDesc {Y : I → C} [HasCoproduct Y]
    {X : C} (ι : ∀ i, Y i ⟶ X) :
    Nonempty (IsColimit (Cofan.mk X ι)) ↔ IsIso (Sigma.desc ι) :=
  Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk X ι)

end Coproduct

section Zero

variable [HasZeroMorphisms C]

/-- Renard A.IX, second condition of `𝓜 = ∏ᵢ 𝓜ᵢ`: for distinct indices `i ≠ j`,
every morphism from an object of `P i` to an object of `P j` is zero. -/
def OffDiagonalHomsZero (P : I → ObjectProperty C) : Prop :=
  ∀ i j : I, i ≠ j → ∀ X Y : C, P i X → P j Y → ∀ f : X ⟶ Y, f = 0

/-- Renard A.IX, the notation `𝓜 = ∏ᵢ 𝓜ᵢ`: every object is the vertex of an
actual coproduct cofan of components in the full subcategories `P i`, and all
morphisms between objects of distinct `P i` are zero. -/
def IsCategoryDecomposition (P : I → ObjectProperty C) : Prop :=
  EveryObjectIsCoproductOfComponents P ∧ OffDiagonalHomsZero P

/-- With zero morphisms, the Hom condition says that each off-diagonal Hom set is a
subsingleton. -/
theorem offDiagonalHomsZero_iff_subsingleton (P : I → ObjectProperty C) :
    OffDiagonalHomsZero P ↔
      ∀ i j : I, i ≠ j → ∀ X Y : C, P i X → P j Y → Subsingleton (X ⟶ Y) := by
  constructor
  · intro h i j hij X Y hX hY
    exact ⟨fun f g => (h i j hij X Y hX hY f).trans (h i j hij X Y hX hY g).symm⟩
  · intro h i j hij X Y hX hY f
    have := h i j hij X Y hX hY
    exact Subsingleton.elim f 0

/-- The Hom condition, quantified over objects of the actual full subcategories
and their images under the inclusions `(P i).ι`. -/
theorem offDiagonalHomsZero_iff_fullSubcategory (P : I → ObjectProperty C) :
    OffDiagonalHomsZero P ↔
      ∀ i j : I, i ≠ j → ∀ (X : (P i).FullSubcategory) (Y : (P j).FullSubcategory)
        (f : (P i).ι.obj X ⟶ (P j).ι.obj Y), f = 0 := by
  constructor
  · intro h i j hij X Y f
    exact h i j hij X.obj Y.obj X.property Y.property f
  · intro h i j hij X Y hX hY f
    exact h i j hij ⟨X, hX⟩ ⟨Y, hY⟩ f

end Zero

end Langlands.Renard
