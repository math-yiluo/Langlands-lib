/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Algebra.Homology.KFlat
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.RingedSpacePastedPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.RingedSpaceKFlatDirectImageHomLocalization

/-!
# The pasted direct-image unit tested on K-flat complexes

Source: Stacks Project, Cohomology, Tags 079W, 0D5S and 0D5T.
(blueprint: lem-pc-ringed-space-pasted-unit-kflat-hom).
-/

@[expose] public section

universe u wX wY wZ

open CategoryTheory

set_option autoImplicit false

namespace AlgebraicGeometry.RingedSpace

private theorem hom_bijective_of_compatible_adjunctions
    {C D DC DD : Type*} [Category* C] [Category* D] [Category* DC] [Category* DD]
    {G : C ⥤ D} {F : D ⥤ C} (adj : G ⊣ F)
    {G' : DC ⥤ DD} {F' : DD ⥤ DC} (adj' : G' ⊣ F')
    (Q₁ : C ⥤ DC) (Q₂ : D ⥤ DD)
    (α : Q₁ ⋙ G' ⟶ G ⋙ Q₂) (β : F ⋙ Q₁ ⟶ Q₂ ⋙ F')
    (hη : ∀ X, adj'.unit.app (Q₁.obj X) ≫ F'.map (α.app X) =
      Q₁.map (adj.unit.app X) ≫ β.app (G.obj X))
    (K : C) (I : D) [IsIso (α.app K)]
    (hQ : Function.Bijective (Q₂.map : (G.obj K ⟶ I) → _)) :
    Function.Bijective (fun a : K ⟶ F.obj I ↦ Q₁.map a ≫ β.app I) := by
  let e := Iso.homCongr (asIso (α.app K)).symm (Iso.refl (Q₂.obj I))
  have hb := (adj'.homEquiv (Q₁.obj K) (Q₂.obj I)).bijective.comp
    (e.bijective.comp (hQ.comp (adj.homEquiv K I).symm.bijective))
  convert! hb using 1
  funext a
  dsimp [Function.comp, e, Iso.homCongr]
  rw [Category.comp_id, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, hη, Category.assoc]
  have hn := β.naturality ((adj.homEquiv K I).symm a)
  dsimp at hn
  rw [← hn]
  rw [← Category.assoc, ← Q₁.map_comp]
  have ha := (adj.homEquiv K I).apply_symm_apply a
  rw [Adjunction.homEquiv_unit] at ha
  rw [ha]

/-- Postcomposition with the pasted derived units induces a Hom bijection when the
source is a localized K-flat complex and the original target is K-injective.
Source: Stacks Project, Cohomology, `lemma-adjoint` (079W),
`lemma-derived-pullback-composition` (0D5S), and the argument of
`lemma-derived-pushforward-composition` (0D5T).
(blueprint: lem-pc-ringed-space-pasted-unit-kflat-hom).

Proof: write H for the homotopy category and P = f* g* for successive tensor
pullback. Pullback preserves K-flatness by `isKFlat_pullback`, so P K computes
Lf* Lg* QK. Choose the derived adjunctions induced from the underived adjunctions,
not arbitrary adjunctions with the same functors. Their Hom equivalences and the
K-injective Hom computation identify Hom(QK, Rg* Rf* QI) with Hom_H(P K, I).

Here is the localization step, which does not treat K-flat as K-projective.
Represent a map QK to Q(g* f* I) by a roof K ←s K' →a g* f* I. Resolve K' by a
K-flat complex K''; replace s and a by their composites with the resolution.
The new s has K-flat endpoints. Successive pullback takes s to a quasi-isomorphism:
on K-flat complexes it computes the derived pullback, which inverts Q(s).
Adjunction takes a to a map b : P K'' → I. The roof defines
Q(b) composed with the inverse of Q(P s), a map Q(P K) to QI, hence a unique
homotopy class P K → I by K-injectivity. Naturality of adjunction makes this
independent of refinement of the roof. Conversely a homotopy class P K → I
has an underived adjunct K → g* f* I, whose localization gives a preimage.
These operations are inverse: for the original roof the composite of this
adjunct with s is homotopic to a, since their adjuncts become equal after
localization and maps into I are computed faithfully in H. This proves both
surjectivity and injectivity, with common refinements for equality of roofs.

Finally apply the unit/counit compatibility for the derived adjunction induced
from the underived adjunction (`Adjunction.derivedε_fac_app`), first for f and
then for g. Under the two derived Hom equivalences the localized underived
adjunct of b : P K → I maps back to that adjunct followed by ηg(f* I) and
Rg*(ηf(I)). Naturality gives the same identity for roofs. Thus precisely the
displayed postcomposition function is the composite of the two Hom bijections.
This expands the adjunction argument of 079W and 0D5T on K-flat representatives;
no preservation of K-injectivity by direct image is used. -/
theorem moduleDirectImage_pastedUnit_kFlat_hom_bijective
    {X Y Z : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ) [I.IsKInjective]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Z)) ℤ) (hK : K.IsKFlatTensor) :
    Function.Bijective (fun
      (a : DerivedCategory.Q.obj K ⟶ DerivedCategory.Qh.obj
        (((moduleDirectImage g).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          (((moduleDirectImage f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)))) =>
      a ≫ (moduleDirectImage g).rightDerivedFunctorUnit.app
          (((moduleDirectImage f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
        (derivedModuleDirectImage g).map
          ((moduleDirectImage f).rightDerivedFunctorUnit.app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  obtain ⟨G, adj, L, adj', α, hα, hη⟩ := exists_pasted_tensorPullback_adjunction f g
  let K₀ := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K
  let I₀ := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I
  let β := (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      ((moduleDirectImage f).mapHomotopyCategory (ComplexShape.up ℤ))
      (moduleDirectImage g).rightDerivedFunctorUnit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (moduleDirectImage f).rightDerivedFunctorUnit
      (derivedModuleDirectImage g) ≫ (Functor.associator _ _ _).hom
  let : IsIso (α.app K₀) := hα K hK
  have hb := hom_bijective_of_compatible_adjunctions adj adj'
    DerivedCategory.Qh DerivedCategory.Qh α β hη K₀ I₀
    (CochainComplex.IsKInjective.Qh_map_bijective (G.obj K₀) I)
  have hloc := moduleDirectImage_kFlat_hom_localization_bijective f g I K hK
  have hβ : β.app I₀ =
      (moduleDirectImage g).rightDerivedFunctorUnit.app
        (((moduleDirectImage f).mapHomotopyCategory (ComplexShape.up ℤ)).obj I₀) ≫
      (derivedModuleDirectImage g).map
        ((moduleDirectImage f).rightDerivedFunctorUnit.app I₀) := by
    simp [β]
  constructor
  · intro a b hab
    obtain ⟨a₀, rfl⟩ := hloc.surjective a
    obtain ⟨b₀, rfl⟩ := hloc.surjective b
    congr 1
    apply hb.injective
    simpa only [hβ, Category.assoc] using hab
  · intro b
    obtain ⟨a, ha⟩ := hb.surjective b
    refine ⟨DerivedCategory.Qh.map a, ?_⟩
    simpa only [hβ, Category.assoc] using ha

end AlgebraicGeometry.RingedSpace
