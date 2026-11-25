/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition
import WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionMateUnit

/-! # Normalized direct-image square as a pullback mate
Source: Stacks Project, cohomology.tex, Tags 08HY, 0D5T and 0D5W.
(blueprint: lem-sc-derived-direct-image-square-mate).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
/-- The fixed direct-image composition comparison, typed on schemes.
Source: Stacks Project, Tag 0D5T.
(blueprint: lem-sc-derived-direct-image-square-mate). -/
noncomputable def schemeNormalizedDirectImageCompIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    schemeDerivedDirectImage f ⋙ schemeDerivedDirectImage g ≅
      schemeDerivedDirectImage (f ≫ g) :=
  Classical.choose (RingedSpace.exists_derivedModuleDirectImageComposition
    f.toLRSHom.toShHom g.toLRSHom.toShHom)

-- Checking canonical comparison choices expands derived-functor and sheaf instances.
/-- The mate of the fixed pullback square is the normalized direct-image square.
Source: Stacks Project, Tags 08HY and 0D5T.
(blueprint: lem-sc-derived-direct-image-square-mate).

Proof: Use the left-derived counit equation of the chosen pullback composition
comparison and the Hom-equivalence normalization of the pinned adjunctions.
Transpose this equation using the underived tensor-pullback/direct-image adjunction.
The underived transpose is the identity identification of the two pushforward paths.
The resulting equation says that the mate, precomposed with the pasted right-derived
unit for the first path, equals the pasted unit for the second path. The inverse
composition comparisons satisfy exactly these equations by
exists_derivedModuleDirectImageComposition. Thus the composite of the first
comparison, the equality transport, and the inverse second comparison has the same
unit equation. On a K-injective representative the pasted unit is invertible, by
acyclicity of direct image for further direct image. Cancel it there, and transport
along a K-injective resolution to every derived object. No global sections or module
localization occurs. Identity squares give identity maps; zero objects give zero
components, and no flatness or nonemptiness assumption is used. -/
theorem derivedDirectImage_square_mate
    {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (gX : X' ⟶ X)
    (h : gX ≫ f = f' ≫ g) :
    let a := fun {A D : Scheme.{u}} (t : A ⟶ D) ↦ schemeHomPullbackAdjunction t
    let p := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
    let k := p f' g ≪≫
      eqToIso (congrArg (fun t ↦ derivedPullback t) h.symm) ≪≫ (p gX f).symm
    let e₁ : schemeDerivedDirectImage gX ⋙ schemeDerivedDirectImage f ≅
        schemeDerivedDirectImage (gX ≫ f) :=
      schemeNormalizedDirectImageCompIso gX f
    let e₂ : schemeDerivedDirectImage f' ⋙ schemeDerivedDirectImage g ≅
        schemeDerivedDirectImage (f' ≫ g) :=
      schemeNormalizedDirectImageCompIso f' g
    conjugateEquiv ((a f).comp (a gX)) ((a g).comp (a f')) k.hom =
      e₁.hom ≫ eqToHom (congrArg (fun t ↦ schemeDerivedDirectImage t) h) ≫ e₂.inv := by
  let a := fun {A D : Scheme.{u}} (t : A ⟶ D) ↦ schemeHomPullbackAdjunction t
  let p : ∀ {A B C : Scheme.{u}} (s : A ⟶ B) (t : B ⟶ C),
      derivedPullback t ⋙ derivedPullback s ≅ derivedPullback (s ≫ t) :=
    @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
  have hc {A B C : Scheme.{u}} (s : A ⟶ B) (t : B ⟶ C) :
      conjugateEquiv (a (s ≫ t)) ((a t).comp (a s)) (p s t).hom =
        (schemeNormalizedDirectImageCompIso s t).inv := by
    apply (RingedSpace.moduleDirectImage (s ≫ t).toLRSHom.toShHom).rightDerivedFunctor
      |>.rightDerived_ext
        (RingedSpace.moduleDirectImage (s ≫ t).toLRSHom.toShHom).rightDerivedFunctorUnit
        (HomotopyCategory.quasiIso _ (.up ℤ))
    apply NatTrans.ext
    funext K
    exact (derivedPullbackComposition_mate_unit s t K).trans
      ((Classical.choose_spec (RingedSpace.exists_derivedModuleDirectImageComposition
        s.toLRSHom.toShHom t.toLRSHom.toShHom)) K).symm
  have hi {A B C : Scheme.{u}} (s : A ⟶ B) (t : B ⟶ C) :
      conjugateEquiv ((a t).comp (a s)) (a (s ≫ t)) (p s t).inv =
        (schemeNormalizedDirectImageCompIso s t).hom := by
    have he : conjugateIsoEquiv (a (s ≫ t)) ((a t).comp (a s)) (p s t) =
        (schemeNormalizedDirectImageCompIso s t).symm := Iso.ext (hc s t)
    exact congrArg Iso.inv he
  have he {A B : Scheme.{u}} (s t : A ⟶ B) (e : s = t) :
      conjugateEquiv (a s) (a t)
        (eqToHom (congrArg (fun z ↦ derivedPullback z) e.symm)) =
          eqToHom (congrArg (fun z ↦ schemeDerivedDirectImage z) e) := by
    subst t
    simp
  change conjugateEquiv ((a f).comp (a gX)) ((a g).comp (a f'))
    ((p f' g).hom ≫ eqToHom (congrArg (fun t ↦ derivedPullback t) h.symm) ≫
      (p gX f).inv) = _
  rw [← Category.assoc, ← conjugateEquiv_comp _ (a (gX ≫ f))]
  rw [← conjugateEquiv_comp _ (a (f' ≫ g))]
  rw [hi, hc, he _ _ h]

end AlgebraicGeometry
