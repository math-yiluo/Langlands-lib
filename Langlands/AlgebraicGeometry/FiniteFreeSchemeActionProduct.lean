import Langlands.AlgebraicGeometry.FiniteFreeSchemeActionQuotientMap
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Products of finite free scheme actions and their affine quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry

/-- A property stable under composition and base change is stable under products
of two morphisms. -/
theorem schemeMorphismProperty_prod_map (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ X') (g : Y ⟶ Y') (hf : P f) (hg : P g) :
    P (prod.map f g) := by
  have hleft : P (prod.map f (𝟙 Y)) :=
    MorphismProperty.of_isPullback (IsPullback.of_prod_fst_with_id f Y) hf
  have hright : IsPullback (prod.snd : X' ⨯ Y ⟶ Y)
      (prod.map (𝟙 X') g) g (prod.snd : X' ⨯ Y' ⟶ Y') := by
    apply (IsPullback.of_prod_fst_with_id g X').of_iso
      (prod.braiding Y X') (Iso.refl Y) (prod.braiding Y' X') (Iso.refl Y')
    all_goals simp
  have hright' : P (prod.map (𝟙 X') g) :=
    MorphismProperty.of_isPullback hright hg
  have hfactor : prod.map f g = prod.map f (𝟙 Y) ≫ prod.map (𝟙 X') g := by simp
  rw [hfactor]
  exact P.comp_mem _ _ hleft hright'

namespace FiniteFreeSchemeAction

variable {G H : Type u} [Group G] [Group H] {X Y : Scheme.{u}}
  (A : FiniteFreeSchemeAction G X) (B : FiniteFreeSchemeAction H Y)

/-- The product action, with independent actions on the two factors. -/
def product : FiniteFreeSchemeAction (G × H) (X ⨯ Y) where
  act g := prod.mapIso (A.act g.1) (B.act g.2)
  one := by
    apply prod.hom_ext <;> simp [A.one, B.one]
  mul g h := by
    apply prod.hom_ext <;> simp [← A.mul, ← B.mul]
  free f := by
    intro g h heq
    apply Prod.ext
    · apply A.free (f ≫ prod.fst)
      simpa using congrArg (· ≫ prod.fst) heq
    · apply B.free (f ≫ prod.snd)
      simpa using congrArg (· ≫ prod.snd) heq

/-- Projection of a product-action relation arrow to its first action arrow. -/
def productRelationLeft : (A.product B).relationScheme ⟶ A.relationScheme :=
  Sigma.desc fun g => prod.fst ≫ Sigma.ι (fun _ : G => X) g.1

/-- Projection of a product-action relation arrow to its second action arrow. -/
def productRelationRight : (A.product B).relationScheme ⟶ B.relationScheme :=
  Sigma.desc fun g => prod.snd ≫ Sigma.ι (fun _ : H => Y) g.2

@[reassoc (attr := simp)]
theorem productRelationLeft_target :
    A.productRelationLeft B ≫ A.target = (A.product B).target ≫ prod.fst := by
  apply Sigma.hom_ext
  intro g
  simp [productRelationLeft, product]

@[reassoc (attr := simp)]
theorem productRelationLeft_source :
    A.productRelationLeft B ≫ A.source = (A.product B).source ≫ prod.fst := by
  apply Sigma.hom_ext
  intro g
  simp [productRelationLeft, product]

@[reassoc (attr := simp)]
theorem productRelationRight_target :
    A.productRelationRight B ≫ B.target = (A.product B).target ≫ prod.snd := by
  apply Sigma.hom_ext
  intro g
  simp [productRelationRight, product]

@[reassoc (attr := simp)]
theorem productRelationRight_source :
    A.productRelationRight B ≫ B.source = (A.product B).source ≫ prod.snd := by
  apply Sigma.hom_ext
  intro g
  simp [productRelationRight, product]

variable [Finite G] [Finite H]

/-- Finite extensivity identifies the relation of a product action with the
product of the two action relations. -/
theorem productRelation_isPullback :
    IsPullback (A.productRelationLeft B) (A.productRelationRight B)
      (terminal.from A.relationScheme) (terminal.from B.relationScheme) := by
  have h := IsUniversalColimit.isPullback_prod_of_isColimit
    (FinitaryPreExtensive.isUniversal_finiteCoproducts
      (coproductIsCoproduct (fun _ : G => X)))
    (FinitaryPreExtensive.isUniversal_finiteCoproducts
      (coproductIsCoproduct (fun _ : H => Y)))
    (fun _ => terminal.from X) (fun _ => terminal.from Y)
    (terminal.from A.relationScheme) (terminal.from B.relationScheme)
    (fun _ _ => IsPullback.of_hasBinaryProduct' X Y)
    (Cofan.mk _ (Sigma.ι (fun _ : G × H => X ⨯ Y)))
    (coproductIsCoproduct (fun _ : G × H => X ⨯ Y))
  have hl : Cofan.IsColimit.desc (coproductIsCoproduct (fun _ : G × H => X ⨯ Y))
      (fun g => prod.fst ≫ Sigma.ι (fun _ : G => X) g.1) =
      A.productRelationLeft B := by
    apply Sigma.hom_ext
    intro g
    simp only [productRelationLeft, Sigma.ι_comp_desc]
    exact Cofan.IsColimit.fac (coproductIsCoproduct (fun _ : G × H => X ⨯ Y)) _ g
  have hr : Cofan.IsColimit.desc (coproductIsCoproduct (fun _ : G × H => X ⨯ Y))
      (fun g => prod.snd ≫ Sigma.ι (fun _ : H => Y) g.2) =
      A.productRelationRight B := by
    apply Sigma.hom_ext
    intro g
    simp only [productRelationRight, Sigma.ι_comp_desc]
    exact Cofan.IsColimit.fac (coproductIsCoproduct (fun _ : G × H => X ⨯ Y)) _ g
  change IsPullback
    (Cofan.IsColimit.desc (coproductIsCoproduct (fun _ : G × H => X ⨯ Y))
      (fun g => prod.fst ≫ Sigma.ι (fun _ : G => X) g.1))
    (Cofan.IsColimit.desc (coproductIsCoproduct (fun _ : G × H => X ⨯ Y))
      (fun g => prod.snd ≫ Sigma.ι (fun _ : H => Y) g.2))
    (terminal.from A.relationScheme) (terminal.from B.relationScheme) at h
  simpa only [hl, hr] using h

variable (Q : A.AffineQuotient) (Q' : B.AffineQuotient)

/-- The product action relation is the kernel pair of the product quotient map. -/
theorem productQuotient_isPullback :
    IsPullback (A.product B).target (A.product B).source
      (prod.map Q.map Q'.map) (prod.map Q.map Q'.map) := by
  have hp := A.productRelation_isPullback B
  refine IsPullback.mk' ?_ ?_ ?_
  · apply prod.hom_ext
    · simpa only [Category.assoc, prod.map_fst,
        productRelationLeft_target_assoc, productRelationLeft_source_assoc] using
        congrArg (fun k => A.productRelationLeft B ≫ k) Q.condition
    · simpa only [Category.assoc, prod.map_snd,
        productRelationRight_target_assoc, productRelationRight_source_assoc] using
        congrArg (fun k => A.productRelationRight B ≫ k) Q'.condition
  · intro T a b ht hs
    apply hp.hom_ext
    · apply Q.isPullback.hom_ext
      · simpa using congrArg (· ≫ prod.fst) ht
      · simpa using congrArg (· ≫ prod.fst) hs
    · apply Q'.isPullback.hom_ext
      · simpa using congrArg (· ≫ prod.snd) ht
      · simpa using congrArg (· ≫ prod.snd) hs
  · intro T a b hab
    have hl : (a ≫ prod.fst) ≫ Q.map = (b ≫ prod.fst) ≫ Q.map := by
      simpa using congrArg (· ≫ prod.fst) hab
    have hr : (a ≫ prod.snd) ≫ Q'.map = (b ≫ prod.snd) ≫ Q'.map := by
      simpa using congrArg (· ≫ prod.snd) hab
    let l := Q.isPullback.lift (a ≫ prod.fst) (b ≫ prod.fst) hl
    let r := Q'.isPullback.lift (a ≫ prod.snd) (b ≫ prod.snd) hr
    refine ⟨hp.lift l r (by simp), ?_, ?_⟩
    · apply prod.hom_ext
      · rw [Category.assoc, ← A.productRelationLeft_target B,
          ← Category.assoc, hp.lift_fst]
        exact Q.isPullback.lift_fst _ _ _
      · rw [Category.assoc, ← A.productRelationRight_target B,
          ← Category.assoc, hp.lift_snd]
        exact Q'.isPullback.lift_fst _ _ _
    · apply prod.hom_ext
      · rw [Category.assoc, ← A.productRelationLeft_source B,
          ← Category.assoc, hp.lift_fst]
        exact Q.isPullback.lift_snd _ _ _
      · rw [Category.assoc, ← A.productRelationRight_source B,
          ← Category.assoc, hp.lift_snd]
        exact Q'.isPullback.lift_snd _ _ _

/-- Products of actual affine quotients are affine quotients of product actions. -/
def productQuotient : (A.product B).AffineQuotient where
  scheme := Q.scheme ⨯ Q'.scheme
  isAffine := IsAffine.of_isIso (prodIsoPullback Q.scheme Q'.scheme).hom
  map := prod.map Q.map Q'.map
  condition := (A.productQuotient_isPullback B Q Q').w
  finite := schemeMorphismProperty_prod_map (@IsFinite) _ _ inferInstance inferInstance
  etale := schemeMorphismProperty_prod_map (@Etale) _ _ inferInstance inferInstance
  surjective := schemeMorphismProperty_prod_map (@Surjective) _ _ inferInstance inferInstance
  isPullback := A.productQuotient_isPullback B Q Q'
  isColimit := by
    have : Etale (prod.map Q.map Q'.map) :=
      schemeMorphismProperty_prod_map (@Etale) _ _ inferInstance inferInstance
    have : IsFinite (prod.map Q.map Q'.map) :=
      schemeMorphismProperty_prod_map (@IsFinite) _ _ inferInstance inferInstance
    have : Surjective (prod.map Q.map Q'.map) :=
      schemeMorphismProperty_prod_map (@Surjective) _ _ inferInstance inferInstance
    exact isColimitCoforkOfEffectiveEpi _
      (A.productQuotient_isPullback B Q Q').cone
      (A.productQuotient_isPullback B Q Q').isLimit

end FiniteFreeSchemeAction
end Langlands.AlgebraicGeometry
