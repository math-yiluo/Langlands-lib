/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.Limits.Indization.Category
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.ObjectProperty.Ind
import WeilConjectures.CategoryTheory.SixFunctors.IndHeartRealization
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSmall
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleExtContinuity
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# Constructible sheaves are finitely presented and realize the ind-heart fully faithfully

The coefficient ring objects carry their canonical ring-object structures: the one of
`Profinite.continuousMapRingObj E` resp. `Profinite.padicAlgClRingObj ℓ`, and on
`Λ_X = condensedRingObj Λ X` the one transported along `upperStarFromPoint X` (the scoped
instance `Functor.monObjObj` of `CategoryTheory.Obj`). Small diagrams are indexed by categories
in `Type (u + 1)`, the hom universe of the module category, as in `CategoryTheory.Ind`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem finitelyPresentable_of_continuity
    {A : Type*} [Category.{u + 1} A] [HasFilteredColimits A]
    {D : Type*} [Category.{u + 1} D] [Preadditive D]
    (F : A ⥤ D) [F.Full] [F.Faithful] (C : A) (T : D) (e : F.obj C ≅ T)
    (h : ∀ (J : Type (u + 1)) [SmallCategory J] [IsFiltered J] (M : J ⥤ A),
      IsIso (colimit.post M (F ⋙ preadditiveCoyoneda.obj (Opposite.op T)))) :
    IsFinitelyPresentable.{u + 1} C := by
  let G := F ⋙ preadditiveCoyoneda.obj (Opposite.op T)
  have : PreservesFilteredColimitsOfSize.{u + 1, u + 1} G := by
    constructor
    intro J _ _
    constructor
    intro M
    have := h J M
    exact preservesColimit_of_isIso_post G M
  let i : coyoneda.obj (Opposite.op C) ≅ G ⋙ forget AddCommGrpCat :=
    NatIso.ofComponents (fun Y ↦
      ((Functor.FullyFaithful.ofFullyFaithful F).homEquiv.trans
        (Iso.homCongr e (Iso.refl (F.obj Y)))).toIso) (by
          intro Y Z f
          ext g
          change e.inv ≫ F.map (g ≫ f) ≫ 𝟙 _ =
            (e.inv ≫ F.map g ≫ 𝟙 _) ≫ F.map f
          simp [Functor.map_comp, Category.assoc])
  rw [isFinitelyPresentable_iff_preservesFilteredColimitsOfSize]
  exact ⟨fun J _ _ ↦ preservesColimitsOfShape_of_natIso i.symm⟩

private theorem constructible_finitelyPresentable
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj R)]
    (hR : R = Profinite.padicSubfieldCondensedRing ℓ E ∨
      R = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (C : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X))
    (hC : IsConstantModelConstructible (coefficientHeartRingObj R) X C) :
    IsFinitelyPresentable.{u + 1} C := by
  let S := DerivedCategory.singleFunctor
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X)) 0
  apply finitelyPresentable_of_continuity
    (S ⋙ shiftFunctor _ (0 : ℤ)) C (S.obj C) ((shiftFunctorZero _ ℤ).app (S.obj C))
  intro J _ _ M
  exact constructible_sheaf_ext_continuity ℓ E R hR X C hC M
    (colimit.cocone M) (colimit.isColimit M) 0

/-- Finite presentation and full faithfulness of the ind-heart realization for a condensed
coefficient ring object `Λ` and a scheme `X`, in `Mod_{Λ_X}` (internal modules over
`Λ_X = p_X^* Λ`):
1. every constructible module is finitely presentable, i.e.
`Hom(C, -)` preserves all small filtered colimits;
2. there is a functor `Φ: Ind(Cons(X, Λ)) ⥤ Mod_{Λ_X}` which is the realization: its
restriction along `Ind.yoneda` is isomorphic to the inclusion of the constructible modules,
and it sends the canonical colimit of the presentation diagram of every ind-object to an actual
colimit; this `Φ` is full and faithful, and its essential image is `ObjectProperty.ind.{u + 1}`
of the constructible modules, i.e. `IndCons(X, Λ)`. -/
def IndHeartFullFaithfulnessAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) : Prop :=
  (∀ C : ObjectProperty.FullSubcategory (IsConstantModelConstructible Λ X),
    IsFinitelyPresentable.{u + 1}
      (C.1 : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))) ∧
  ∃ Φ : CategoryTheory.Ind (ObjectProperty.FullSubcategory
      (IsConstantModelConstructible Λ X)) ⥤
    CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
    Nonempty (CategoryTheory.Ind.yoneda ⋙ Φ ≅
      ObjectProperty.ι (IsConstantModelConstructible Λ X)) ∧
    (∀ Z : CategoryTheory.Ind (ObjectProperty.FullSubcategory
        (IsConstantModelConstructible Λ X)),
      Nonempty (IsColimit
        (Φ.mapCocone (colimit.cocone
          ((CategoryTheory.Ind.presentation Z).F ⋙ CategoryTheory.Ind.yoneda))))) ∧
    Φ.Full ∧ Φ.Faithful ∧
    (∀ M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X),
      Φ.essImage M ↔ ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) M)

/-- Constructible coefficient modules are finitely presented, and their ordinary ind-category
realizes fully faithfully as the filtered-colimit closure in the ambient module category, for
both coefficient choices `Λ = E` (a finite extension of `ℚ_ℓ` inside `\bar ℚ_ℓ`) and
`Λ = \bar ℚ_ℓ`, on a Noetherian scheme `X` (locally Noetherian and quasi-compact). -/
theorem indHeart_fullFaithfulness
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X] :
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      IndHeartFullFaithfulnessAssertions (Profinite.continuousMapRingObj.{u} E) X) ∧
    IndHeartFullFaithfulnessAssertions (Profinite.padicAlgClRingObj.{u} ℓ) X := by
  constructor
  · intro E
    let R := Profinite.padicSubfieldCondensedRing ℓ E
    let P := IsConstantModelConstructible (coefficientHeartRingObj R) X
    let C := ObjectProperty.FullSubcategory P
    let M := CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X)
    have hfp : ∀ Y : C, IsFinitelyPresentable.{u + 1} (Y.1 : M) := by
      intro Y
      exact constructible_finitelyPresentable ℓ E R (Or.inl rfl) X Y.1 Y.2
    have : EssentiallySmall.{u + 1} C :=
      coefficientHeart_essentiallySmall ℓ R (Or.inl ⟨E.1, E.2, rfl⟩) X
    obtain ⟨Φ, hyon, hcol, hfull, hfaith, himage⟩ :=
      ind_realization_of_finitelyPresentable P hfp
    exact ⟨hfp, Φ, hyon, hcol, hfull, hfaith, himage⟩
  · let R := Profinite.padicAlgClCondensedRing ℓ
    let P := IsConstantModelConstructible (coefficientHeartRingObj R) X
    let C := ObjectProperty.FullSubcategory P
    let M := CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X)
    have hfp : ∀ Y : C, IsFinitelyPresentable.{u + 1} (Y.1 : M) := by
      intro Y
      exact constructible_finitelyPresentable ℓ (Classical.arbitrary _) R (Or.inr rfl) X Y.1 Y.2
    have : EssentiallySmall.{u + 1} C :=
      coefficientHeart_essentiallySmall ℓ R (Or.inr rfl) X
    obtain ⟨Φ, hyon, hcol, hfull, hfaith, himage⟩ :=
      ind_realization_of_finitelyPresentable P hfp
    exact ⟨hfp, Φ, hyon, hcol, hfull, hfaith, himage⟩
end AlgebraicGeometry.ProEtale
