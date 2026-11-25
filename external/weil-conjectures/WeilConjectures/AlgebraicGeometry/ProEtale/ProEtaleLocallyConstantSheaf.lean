/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleEncoding

/-!
# Locally constant module sheaves on the small pro-etale site

Constant module sheaves are constructed by simultaneous sheafification of the
constant ring and module. On a localized site the ring is the restricted constant
ring sheaf. Two named proof obligations record local bijectivity of the ring unit;
no data is chosen from an existence assertion.

## Main definitions

* `proEtaleConstantModuleSheaf`: the constant module sheaf.
* `proEtaleConstantModuleSheafOver`: its localized-site construction.
* `IsConstantProEtaleModuleSheaf`: global constancy.
* `IsLocallyConstantProEtaleModuleSheaf`: coverwise constancy.

## References

* Bhatt--Scholze, *The pro-etale topology for schemes*, Definition 7.3.1(1)
* Bhatt--Scholze, Lemma 7.3.1(1)
* Bhatt--Scholze 7.3.1(1), module version
-/

universe t v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

@[expose] public section

namespace AlgebraicGeometry.Scheme

/-- The constant module presheaf, with identity restriction maps and the given
scalar multiplication. -/
noncomputable def proEtaleConstantModulePresheaf (C : Type w) [Category.{v} C] (A : Type t)
    [CommRing A] (M : ModuleCat.{t + 1} (ULift.{t + 1, t} A)) :
    _root_.PresheafOfModules.{t + 1}
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, t} A)) ⋙
        forget₂ CommRingCat.{t + 1} RingCat.{t + 1}) where
  obj _ := M
  map _ := 𝟙 M


/-- The constant module sheaf, sheafifying the constant module presheaf together
with the constant coefficient ring. Scalar multiplication is the sheafified original
scalar multiplication. -/
noncomputable def proEtaleConstantModuleSheaf (Y : Scheme.{t}) (A : Type t)
    [CommRing A] (M : ModuleCat.{t + 1} (ULift.{t + 1, t} A)) :
    SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj
          ((constantSheaf (ProEt.topology Y) CommRingCat.{t + 1}).obj
            (CommRingCat.of (ULift.{t + 1, t} A)))) :=
  haveI := (proEtaleConstantRingUnit_locallyBijective Y A).1
  haveI := (proEtaleConstantRingUnit_locallyBijective Y A).2
  (_root_.PresheafOfModules.sheafification
    (Functor.whiskerRight (CategoryTheory.toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, t} A))))
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1}))).obj
    (proEtaleConstantModulePresheaf Y.ProEt A M)

/-- The same ring unit on the localized site is locally bijective. -/
theorem proEtaleConstantRingUnit_over_locallyBijective (Y : Scheme.{t}) (A : Type t)
    [CommRing A] (U : Y.ProEt) :
    Presheaf.IsLocallyInjective ((ProEt.topology Y).over U)
      (Functor.whiskerLeft (Over.forget U).op
        (Functor.whiskerRight (CategoryTheory.toSheafify (ProEt.topology Y)
          ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, t} A))))
          (forget₂ CommRingCat.{t + 1} RingCat.{t + 1}))) ∧
    Presheaf.IsLocallySurjective ((ProEt.topology Y).over U)
      (Functor.whiskerLeft (Over.forget U).op
        (Functor.whiskerRight (CategoryTheory.toSheafify (ProEt.topology Y)
          ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, t} A))))
          (forget₂ CommRingCat.{t + 1} RingCat.{t + 1}))) := by
  have := (proEtaleConstantRingUnit_locallyBijective Y A).1
  have := (proEtaleConstantRingUnit_locallyBijective Y A).2
  exact ⟨Presheaf.isLocallyInjective_whisker ((ProEt.topology Y).over U)
    (ProEt.topology Y) (Over.forget U) _,
    Presheaf.isLocallySurjective_whisker ((ProEt.topology Y).over U)
      (ProEt.topology Y) (Over.forget U) _⟩

/-- The constant module sheaf on the localized site, formed by sheafification over
the restricted coefficient ring. -/
noncomputable def proEtaleConstantModuleSheafOver (Y : Scheme.{t}) (A : Type t)
    [CommRing A] (U : Y.ProEt) (M : ModuleCat.{t + 1} (ULift.{t + 1, t} A)) :
    SheafOfModules.{t + 1}
      (((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj
          ((constantSheaf (ProEt.topology Y) CommRingCat.{t + 1}).obj
            (CommRingCat.of (ULift.{t + 1, t} A)))).over U) :=
  haveI := (proEtaleConstantRingUnit_over_locallyBijective Y A U).1
  haveI := (proEtaleConstantRingUnit_over_locallyBijective Y A U).2
  (_root_.PresheafOfModules.sheafification
    (Functor.whiskerLeft (Over.forget U).op
      (Functor.whiskerRight (CategoryTheory.toSheafify (ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, t} A))))
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})))).obj
    (proEtaleConstantModulePresheaf (Over U) A M)

/-- A module sheaf is locally constant if a covering family trivializes its
restrictions on the localized ringed sites, with arbitrary module values depending
on the cover member. -/
noncomputable def IsLocallyConstantProEtaleModuleSheaf
    (Y : Scheme.{t}) (A : Type t) [CommRing A]
    (F : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj
          ((constantSheaf (ProEt.topology Y) CommRingCat.{t + 1}).obj
            (CommRingCat.of (ULift.{t + 1, t} A))))) : Prop :=
  ∃ (I : Type (t + 1)) (U : I → Y.ProEt)
    (f : ∀ i : I, U i ⟶ ProEt.mk (𝟙 Y)),
    Presieve.ofArrows U f ∈ (ProEt.precoverage Y).coverings _ ∧
      ∀ i : I, ∃ (M : ModuleCat.{t + 1} (ULift.{t + 1, t} A)),
        Nonempty (F.over (U i) ≅ proEtaleConstantModuleSheafOver Y A (U i) M)

end AlgebraicGeometry.Scheme
