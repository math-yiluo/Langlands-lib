import Langlands.GroupScheme.Products
import Langlands.GroupScheme.Multiplicative
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.MorphismProperty.Comma

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace Langlands.GroupScheme

/-- Smoothness is preserved by an isomorphism over the same base scheme. -/
theorem smooth_of_over_iso {S : Scheme.{u}} {X Y : Over S} (e : X ≅ Y)
    (hY : Smooth Y.hom) : Smooth X.hom := by
  let : Smooth Y.hom := hY
  let : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  rw [← e.hom.w]
  infer_instance

/-- Binary products of smooth schemes over the base are smooth. -/
theorem smooth_tensor {S : Scheme.{u}} (X Y : Over S)
    (hX : Smooth X.hom) (hY : Smooth Y.hom) : Smooth (X ⊗ Y).hom := by
  let : Smooth X.hom := hX
  let : Smooth Y.hom := hY
  change Smooth (pullback.fst X.hom Y.hom ≫ X.hom)
  infer_instance

private instance smoothOver_closedUnderEmpty (S : Scheme.{u}) :
    (MorphismProperty.overObj (@Smooth) (X := S)).IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty) where
  limitsOfShape_le X h := by
    obtain ⟨p⟩ := h
    have hX : IsTerminal X :=
      (IsLimit.equivOfNatIsoOfIso p.diag.uniqueFromEmpty _ _
        (by exact Cone.ext (Iso.refl _) (by rintro ⟨⟨⟩⟩))).1 p.isLimit
    exact smooth_of_over_iso (hX.uniqueUpToIso (isTerminalTensorUnit (C := Over S)))
      (show Smooth (𝟙_ (Over S)).hom from inferInstanceAs (Smooth (𝟙 S)))

private instance smoothOver_closedUnderBinary (S : Scheme.{u}) :
    (MorphismProperty.overObj (@Smooth) (X := S)).IsClosedUnderBinaryProducts where
  limitsOfShape_le X h := by
    obtain ⟨p⟩ := h
    let Y := p.diag.obj ⟨WalkingPair.left⟩
    let Z := p.diag.obj ⟨WalkingPair.right⟩
    let c : BinaryFan Y Z := BinaryFan.mk (p.π.app ⟨WalkingPair.left⟩)
      (p.π.app ⟨WalkingPair.right⟩)
    have hc : IsLimit c :=
      (IsLimit.equivOfNatIsoOfIso (diagramIsoPair p.diag) _ _
        (by exact Cone.ext (Iso.refl _) (by rintro ⟨_ | _⟩ <;> simp [c]))).1 p.isLimit
    exact smooth_of_over_iso (hc.conePointUniqueUpToIso (tensorProductIsBinaryProduct Y Z))
      (smooth_tensor Y Z (p.prop_diag_obj ⟨WalkingPair.left⟩)
        (p.prop_diag_obj ⟨WalkingPair.right⟩))

/-- A finite product of actual smooth group schemes is smooth over its base. -/
theorem smooth_pi {S : Scheme.{u}} {I : Type u} [Finite I] (G : I → GroupScheme S)
    (hG : ∀ i, Smooth (G i).X.hom) : Smooth (pi G).X.hom := by
  let : (MorphismProperty.overObj (@Smooth) (X := S)).IsClosedUnderFiniteProducts :=
    ObjectProperty.IsClosedUnderFiniteProducts.mk'
  exact (MorphismProperty.overObj (@Smooth) (X := S)).prop_of_isLimit_fan (piIsLimit G) hG

/-- The actual multiplicative group over any scheme is smooth. -/
theorem smooth_gm (S : Scheme.{u}) : Smooth (Gm S).X.hom := by
  let : Algebra.Smooth (ULift.{u} ℤ) (Polynomial (ULift.{u} ℤ)) :=
    ⟨inferInstance, inferInstance⟩
  let : Algebra.Smooth (Polynomial (ULift.{u} ℤ)) (LaurentPolynomial (ULift.{u} ℤ)) :=
    Algebra.Smooth.of_isLocalization_Away (Polynomial.X : Polynomial (ULift.{u} ℤ))
  let : Algebra.Smooth (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) :=
    Algebra.Smooth.comp (ULift.{u} ℤ) (Polynomial (ULift.{u} ℤ))
      (LaurentPolynomial (ULift.{u} ℤ))
  have h : Smooth Gm.overSpecZ.{u}.hom := by
    change Smooth (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C (R := ULift.{u} ℤ))))
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    change (algebraMap (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ))).Smooth
    rw [RingHom.smooth_algebraMap]
    infer_instance
  change Smooth (pullback.snd Gm.overSpecZ.hom (Gm.toSpecZ S))
  let : Smooth Gm.overSpecZ.{u}.hom := h
  infer_instance

end Langlands.GroupScheme
