/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Locally constant module sheaves on the small pro-etale site

Constant module sheaves are constructed by simultaneous sheafification of the
constant ring and module. On a localized site the ring is the restricted constant
ring sheaf. Two named proof obligations record local bijectivity of the ring unit;
no data is chosen from an existence assertion.

## Main definitions

* `proEtaleConstantModuleSheafOfUniverses`: the constant module sheaf.
* `proEtaleConstantModuleSheafOverOfUniverses`: its localized-site construction.
* `IsConstantProEtaleModuleSheafOfUniverses`: global constancy.
* `IsLocallyConstantProEtaleModuleSheafOfUniverses`: coverwise constancy.

## References

* Bhatt--Scholze, *The pro-etale topology for schemes*, Definition 7.3.1(1)
* Bhatt--Scholze, Lemma 7.3.1(1)
* Bhatt--Scholze 7.3.1(1), module version
* Bhatt--Scholze 7.3.1(1)
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe t u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

@[expose] public section

namespace AlgebraicGeometry.Scheme

-- `hasSheafify_of_essentiallySmall` leaves its universe free and stalls universe unification here.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

/-- The constant module presheaf, with identity restriction maps and the given
scalar multiplication. -/
noncomputable def proEtaleConstantModulePresheafOfUniverses
    (C : Type w) [Category.{v} C] (A : Type u)
    [CommRing A] (M : ModuleCat.{max u (t + 1)} (ULift.{t + 1, u} A)) :
    _root_.PresheafOfModules.{max u (t + 1)}
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, u} A)) ⋙
        forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}) where
  obj _ := M
  map _ := 𝟙 M

/-- Sheafification of the constant ring unit remains locally bijective after
forgetting commutativity. -/
theorem proEtaleConstantRingUnit_locallyBijectiveOfUniverses (Y : Scheme.{t}) (A : Type u)
    [CommRing A] :
    Presheaf.IsLocallyInjective (ProEt.topology Y)
      (Functor.whiskerRight (CategoryTheory.toSheafify (ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, u} A))))
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})) ∧
    Presheaf.IsLocallySurjective (ProEt.topology Y)
      (Functor.whiskerRight (CategoryTheory.toSheafify (ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, u} A))))
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})) := by
  let : EssentiallySmall.{max u (t + 1)} Y.ProEt := essentiallySmallSelf _
  let : (ProEt.topology Y).WEqualsLocallyBijective CommRingCat.{max u (t + 1)} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  constructor
  · apply (Presheaf.isLocallyInjective_forget_iff _ _).mp
    change Presheaf.IsLocallyInjective (ProEt.topology Y)
      (Functor.whiskerRight (CategoryTheory.toSheafify (ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, u} A))))
        (CategoryTheory.forget CommRingCat.{max u (t + 1)}))
    infer_instance
  · apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
    change Presheaf.IsLocallySurjective (ProEt.topology Y)
      (Functor.whiskerRight (CategoryTheory.toSheafify (ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, u} A))))
        (CategoryTheory.forget CommRingCat.{max u (t + 1)}))
    infer_instance

/-- The constant module sheaf, sheafifying the constant module presheaf together
with the constant coefficient ring. Scalar multiplication is the sheafified original
scalar multiplication. -/
noncomputable def proEtaleConstantModuleSheafOfUniverses (Y : Scheme.{t}) (A : Type u)
    [CommRing A] (M : ModuleCat.{max u (t + 1)} (ULift.{t + 1, u} A)) :
    SheafOfModules.{max u (t + 1)}
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          ((constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).obj
            (CommRingCat.of (ULift.{t + 1, u} A)))) :=
  haveI := (proEtaleConstantRingUnit_locallyBijectiveOfUniverses Y A).1
  haveI := (proEtaleConstantRingUnit_locallyBijectiveOfUniverses Y A).2
  (_root_.PresheafOfModules.sheafification
    (Functor.whiskerRight (CategoryTheory.toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, u} A))))
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}))).obj
    (proEtaleConstantModulePresheafOfUniverses Y.ProEt A M)

/-- The same ring unit on the localized site is locally bijective. -/
theorem proEtaleConstantRingUnit_over_locallyBijectiveOfUniverses (Y : Scheme.{t}) (A : Type u)
    [CommRing A] (U : Y.ProEt) :
    Presheaf.IsLocallyInjective ((ProEt.topology Y).over U)
      (Functor.whiskerLeft (Over.forget U).op
        (Functor.whiskerRight (CategoryTheory.toSheafify (ProEt.topology Y)
          ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, u} A))))
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}))) ∧
    Presheaf.IsLocallySurjective ((ProEt.topology Y).over U)
      (Functor.whiskerLeft (Over.forget U).op
        (Functor.whiskerRight (CategoryTheory.toSheafify (ProEt.topology Y)
          ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, u} A))))
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}))) := by
  have := (proEtaleConstantRingUnit_locallyBijectiveOfUniverses Y A).1
  have := (proEtaleConstantRingUnit_locallyBijectiveOfUniverses Y A).2
  exact ⟨Presheaf.isLocallyInjective_whisker ((ProEt.topology Y).over U)
    (ProEt.topology Y) (Over.forget U) _,
    Presheaf.isLocallySurjective_whisker ((ProEt.topology Y).over U)
      (ProEt.topology Y) (Over.forget U) _⟩

/-- The constant module sheaf on the localized site, formed by sheafification over
the restricted coefficient ring. -/
noncomputable def proEtaleConstantModuleSheafOverOfUniverses (Y : Scheme.{t}) (A : Type u)
    [CommRing A] (U : Y.ProEt) (M : ModuleCat.{max u (t + 1)} (ULift.{t + 1, u} A)) :
    SheafOfModules.{max u (t + 1)}
      (((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          ((constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).obj
            (CommRingCat.of (ULift.{t + 1, u} A)))).over U) :=
  letI : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
  letI : HasSheafify ((ProEt.topology Y).over U) AddCommGrpCat.{max u (t + 1)} :=
    hasSheafifyEssentiallySmallSite _ _
  letI : ((ProEt.topology Y).over U).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  haveI := (proEtaleConstantRingUnit_over_locallyBijectiveOfUniverses Y A U).1
  haveI := (proEtaleConstantRingUnit_over_locallyBijectiveOfUniverses Y A U).2
  (_root_.PresheafOfModules.sheafification
    (Functor.whiskerLeft (Over.forget U).op
      (Functor.whiskerRight (CategoryTheory.toSheafify (ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, u} A))))
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})))).obj
    (proEtaleConstantModulePresheafOfUniverses (Over U) A M)

/-- A covering family trivializes the module sheaf on localized ringed sites, with
models satisfying P. Taking P constantly true is ordinary local constancy; taking
finite modules gives its finite-dimensional specialization over a field. Models
may vary with the cover member. -/
noncomputable def IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses
    (Y : Scheme.{t}) (A : Type u) [CommRing A]
    (P : ModuleCat.{max u (t + 1)} (ULift.{t + 1, u} A) → Prop)
    (F : SheafOfModules.{max u (t + 1)}
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          ((constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).obj
            (CommRingCat.of (ULift.{t + 1, u} A))))) : Prop :=
  ∃ (I : Type (t + 1)) (U : I → Y.ProEt)
    (f : ∀ i : I, U i ⟶ ProEt.mk (𝟙 Y)),
    Presieve.ofArrows U f ∈ (ProEt.precoverage Y).coverings _ ∧
      ∀ i : I, ∃ (M : ModuleCat.{max u (t + 1)} (ULift.{t + 1, u} A)),
        P M ∧
          Nonempty (F.over (U i) ≅ proEtaleConstantModuleSheafOverOfUniverses Y A (U i) M)

/-- Locally constant module sheaves with arbitrary varying local models, on the same
small site and with independent coefficient size. -/
noncomputable def IsLocallyConstantProEtaleModuleSheafOfUniverses
    (Y : Scheme.{t}) (A : Type u) [CommRing A]
    (F : SheafOfModules.{max u (t + 1)}
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          ((constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).obj
            (CommRingCat.of (ULift.{t + 1, u} A))))) : Prop :=
  IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses Y A (fun _ ↦ True) F

end AlgebraicGeometry.Scheme
