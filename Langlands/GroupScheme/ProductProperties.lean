import Langlands.GroupScheme.Products
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.Limits.MorphismProperty

/-! # Properties of structure morphisms of finite products of group schemes -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace Langlands.GroupScheme

variable (P : MorphismProperty Scheme.{u}) [P.IsStableUnderComposition]
  [P.IsStableUnderBaseChange] [P.ContainsIdentities] [P.RespectsIso]

omit [P.ContainsIdentities] [P.RespectsIso] in
/-- Binary products over the base of schemes with structure morphisms in `P`. -/
theorem prop_tensor_hom {S : Scheme.{u}} (X Y : Over S) (hX : P X.hom) (hY : P Y.hom) :
    P (X ⊗ Y).hom := by
  change P (pullback.fst X.hom Y.hom ≫ X.hom)
  exact P.comp_mem _ _ (P.pullback_fst _ _ hY) hX

private instance overObj_closedUnderBinary (S : Scheme.{u}) :
    (MorphismProperty.overObj P (X := S)).IsClosedUnderBinaryProducts where
  limitsOfShape_le X h := by
    obtain ⟨p⟩ := h
    let Y := p.diag.obj ⟨WalkingPair.left⟩
    let Z := p.diag.obj ⟨WalkingPair.right⟩
    let c : BinaryFan Y Z := BinaryFan.mk (p.π.app ⟨WalkingPair.left⟩)
      (p.π.app ⟨WalkingPair.right⟩)
    have hc : IsLimit c :=
      (IsLimit.equivOfNatIsoOfIso (diagramIsoPair p.diag) _ _
        (by exact Cone.ext (Iso.refl _) (by rintro ⟨_ | _⟩ <;> simp [c]))).1 p.isLimit
    exact (MorphismProperty.overObj P).prop_of_iso
      (hc.conePointUniqueUpToIso (tensorProductIsBinaryProduct Y Z)).symm
      (prop_tensor_hom P Y Z (p.prop_diag_obj ⟨WalkingPair.left⟩)
        (p.prop_diag_obj ⟨WalkingPair.right⟩))

/-- If every factor of a finite product of group schemes has structure morphism in `P`,
so does the product. -/
theorem prop_pi_hom {S : Scheme.{u}} {I : Type u} [Finite I] (G : I → GroupScheme S)
    (hG : ∀ i, P (G i).X.hom) : P (pi G).X.hom := by
  let : (MorphismProperty.overObj P (X := S)).IsClosedUnderFiniteProducts :=
    ObjectProperty.IsClosedUnderFiniteProducts.mk'
  exact (MorphismProperty.overObj P (X := S)).prop_of_isLimit_fan (piIsLimit G) hG

end Langlands.GroupScheme
