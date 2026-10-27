import Langlands.Representation.Filtration.Transport

/-! Scalar twists commute naturally with actual successive quotient functors. -/

open CategoryTheory

namespace Langlands

universe uR uG uV uC vC

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  [TopologicalSpace G] {C : Type uC} [Category.{vC} C]
  {F : C ⥤ Rep.{uV} R G}

namespace RepSubfunctor

/-- The canonical quotient comparison for two arbitrary actual subfunctors.
Its component maps are the identity on the unchanged underlying quotient modules. -/
def twistQuotientIso (S T : RepSubfunctor F) (χ : Induction.SmoothCharacter R G) :
    (S.twist χ).quotientFunctor (T.twist χ) ≅ (S.quotientFunctor T) ⋙ χ.twistFunctor :=
  NatIso.ofComponents (fun X => Rep.mkIso
    { toLinearEquiv := LinearEquiv.refl R (S.quotientObj T X)
      isIntertwining' g := by
        ext v
        rfl }) (by
    intro X Y f
    ext v
    rfl)

@[simp]
theorem twistQuotientIso_hom_app_apply (S T : RepSubfunctor F)
    (χ : Induction.SmoothCharacter R G) (X : C)
    (v : (S.twist χ).quotientObj (T.twist χ) X) :
    ((S.twistQuotientIso T χ).hom.app X).hom v = v := rfl

@[simp]
theorem twistQuotientIso_inv_app_apply (S T : RepSubfunctor F)
    (χ : Induction.SmoothCharacter R G) (X : C) (v : S.quotientObj T X) :
    ((S.twistQuotientIso T χ).inv.app X).hom v = v := rfl

/-- The forward comparison preserves the actual quotient representative. -/
@[simp]
theorem twistQuotientIso_hom_projection (S T : RepSubfunctor F)
    (χ : Induction.SmoothCharacter R G) (X : C) (v : (T.twist χ).representation X) :
    ((S.twistQuotientIso T χ).hom.app X).hom
        (((S.twist χ).quotientProjection (T.twist χ) X).hom v) =
      (S.quotientProjection T X).hom v := rfl

/-- The inverse comparison preserves the actual quotient representative. -/
@[simp]
theorem twistQuotientIso_inv_projection (S T : RepSubfunctor F)
    (χ : Induction.SmoothCharacter R G) (X : C) (v : T.representation X) :
    ((S.twistQuotientIso T χ).inv.app X).hom ((S.quotientProjection T X).hom v) =
      ((S.twist χ).quotientProjection (T.twist χ) X).hom v := rfl

end RepSubfunctor

namespace RepFunctorFiltration

variable {n : ℕ}

/-- Twisting commutes naturally with every actual graded piece, at its original index. -/
def twistGradedIso (s : RepFunctorFiltration F n)
    (χ : Induction.SmoothCharacter R G) (i : Fin n) :
    (s.twist χ).graded i ≅ (s.graded i) ⋙ χ.twistFunctor :=
  (s.step i.castSucc).twistQuotientIso (s.step i.succ) χ

@[simp]
theorem twistGradedIso_hom_app_apply (s : RepFunctorFiltration F n)
    (χ : Induction.SmoothCharacter R G) (i : Fin n) (X : C)
    (v : ((s.twist χ).graded i).obj X) :
    ((s.twistGradedIso χ i).hom.app X).hom v = v := rfl

@[simp]
theorem twistGradedIso_inv_app_apply (s : RepFunctorFiltration F n)
    (χ : Induction.SmoothCharacter R G) (i : Fin n) (X : C)
    (v : (s.graded i).obj X) :
    ((s.twistGradedIso χ i).inv.app X).hom v = v := rfl

end RepFunctorFiltration

end Langlands
