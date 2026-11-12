import Langlands.AlgebraicGeometry.AlgebraicSpace.RelativeDiagonalCharts
import Langlands.AlgebraicGeometry.AlgebraicSpace.DiagonalEqualizer
import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalRepresentationProperties
import Langlands.AlgebraicGeometry.Descent.LocallyQuasiFiniteDescent.QuasiAffineChart
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Geometry of represented algebraic-space equalizers -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace
namespace WeilRestrictionDiagonalGeometry

set_option backward.isDefEq.respectTransparency false

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

/-- A pullback of two maps is the pullback of the diagonal along their product. -/
theorem diagonalSquare {C : Type*} [Category C] [HasBinaryProducts C]
    {R U F : C} {p q : R ⟶ U} {a : U ⟶ F} (h : IsPullback p q a a) :
    IsPullback (p ≫ a) (prod.lift p q) (diag F) (prod.map a a) := by
  apply IsPullback.mk'
  · apply prod.hom_ext <;> simp [h.w]
  · intro T f g h₁ h₂
    apply h.hom_ext
    · simpa using congrArg (fun k => k ≫ prod.fst) h₂
    · simpa using congrArg (fun k => k ≫ prod.snd) h₂
  · intro T x y e
    have e₁ : y ≫ prod.fst ≫ a = x := by
      simpa using (congrArg (fun k => k ≫ prod.fst) e).symm
    have e₂ : y ≫ prod.snd ≫ a = x := by
      simpa using (congrArg (fun k => k ≫ prod.snd) e).symm
    refine ⟨h.lift (y ≫ prod.fst) (y ≫ prod.snd)
      (by simpa only [Category.assoc] using e₁.trans e₂.symm), ?_, ?_⟩
    · rw [← Category.assoc, h.lift_fst, Category.assoc, e₁]
    · apply prod.hom_ext <;> simp

/-- A property stable under composition and base change passes to product maps. -/
theorem property_prodMap {C : Type*} [Category C] [HasFiniteLimits C]
    (P : MorphismProperty C) [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    {A B D E : C} {f : A ⟶ B} {g : D ⟶ E} (hf : P f) (hg : P g) :
    P (prod.map f g) := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have h := MorphismProperty.pullbackMap (P := P)
    (f := terminal.from A) (g := terminal.from D)
    (f' := terminal.from B) (g' := terminal.from E) hf hg (by simp) (by simp)
  have eq : prod.map f g = (prodIsoPullback A D).hom ≫
      pullback.map (terminal.from A) (terminal.from D) (terminal.from B) (terminal.from E)
        f g (𝟙 _) (by simp) (by simp) ≫ (prodIsoPullback B E).inv := by
    apply prod.hom_ext <;> simp
  rw [eq, P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]
  exact h

local instance {S : Scheme.{u}} :
    (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).IsStableUnderComposition := by
  let : MorphismProperty.IsStableUnderComposition (@Etale.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative (@Etale.{u})).toIsStableUnderComposition
  exact MorphismProperty.IsStableUnderComposition.inverseImage (Over.forget S)

local instance {S : Scheme.{u}} :
    (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).IsStableUnderComposition := by
  let : MorphismProperty.IsStableUnderComposition (@Surjective.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative (@Surjective.{u})).toIsStableUnderComposition
  exact MorphismProperty.IsStableUnderComposition.inverseImage (Over.forget S)

/-- Every algebraic-space diagonal is representable and locally of finite type. -/
theorem locallyOfFiniteType_diagonal {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (MorphismProperty.inverseImage (@LocallyOfFiniteType.{u}) (Over.forget S)).relative
      (schemeYoneda S) (diag X.presheaf) := by
  obtain ⟨U, a, ha, hs⟩ := X.property.2
  let Y := schemeYoneda S
  let b := prodComparison Y U U ≫ prod.map a a
  have he : IsEtale b := by
    apply IsEtale.iso_comp (asIso (prodComparison Y U U))
    exact property_prodMap
      ((MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).relative Y)
      ha ha
  have ht : IsSurjective b := by
    apply (MorphismProperty.cancel_left_of_respectsIso
      ((MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).relative Y) _ _).mpr
    exact property_prodMap _ hs hs
  let R := ha.rep.pullback a
  let p : R ⟶ U := ha.rep.fst' a
  let q : R ⟶ U := ha.rep.snd a
  let r : R ⟶ U ⨯ U := prod.lift p q
  have hpq := ha.rep.isPullback' a
  have sq : IsPullback (Y.map p ≫ a) (Y.map r) (diag X.presheaf) b := by
    have hi : IsPullback (𝟙 (Y.obj R)) (Y.map r)
        (prod.lift (Y.map p) (Y.map q)) (prodComparison Y U U) := by
      apply IsPullback.of_horiz_isIso
      constructor
      apply prod.hom_ext <;> simp [r, ← Functor.map_comp]
    exact hi.paste_horiz (diagonalSquare hpq)
  have : Etale q.left := ha.property a _ q hpq
  have hrlft : LocallyOfFiniteType r.left := by
    have : LocallyOfFiniteType (r.left ≫ (prod.snd : U ⨯ U ⟶ U).left) := by
      simpa [← Over.comp_left, r] using (inferInstance : LocallyOfFiniteType q.left)
    exact locallyOfFiniteType_of_comp r.left (prod.snd : U ⨯ U ⟶ U).left
  let hd := X.hasRepresentableDiagonal
  let d := Y.preimageIso ((hd.isPullback b).isoIsPullback _ _ sq)
  have ed : d.hom ≫ r = hd.snd b := by
    apply Y.map_injective
    rw [Functor.map_comp]
    change Y.map (Y.preimage _) ≫ Y.map r = _
    rw [Y.map_preimage]
    exact (hd.isPullback b).isoIsPullback_hom_snd _ _ sq
  have : IsIso d.hom.left := (Over.forget S).map_isIso d.hom
  have : MorphismProperty.DescendsAlong (@LocallyOfFiniteType.{u})
      (@Etale.{u} ⊓ @Surjective.{u}) :=
    SchemeFlatPropertyDescent.descendsAlong_etale_surjective _
  apply relativeProperty_of_etale_atlas (@LocallyOfFiniteType) hd b he ht
  rw [← ed, Over.comp_left]
  exact (MorphismProperty.cancel_left_of_respectsIso (@LocallyOfFiniteType) _ _).mpr hrlft

end WeilRestrictionDiagonalGeometry
end Langlands.AlgebraicGeometry.AlgebraicSpace
