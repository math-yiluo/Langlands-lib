/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenTensorRestrictionIso
import WeilConjectures.AlgebraicGeometry.OpenPinnedCounitHomotopyRestriction
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # Compatibility of open restriction with the pinned pullback counits

Source: Stacks Project, cohomology.tex, Tags 08HY, 08FE and 0D5S.
(blueprint: lem-pc-single-complex-open-counit-compatibility).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry
open SingleComplexBaseChange
set_option synthInstance.maxSize 2048
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] DerivedCategory HomotopyCategory
  DerivedCategory.Q DerivedCategory.Qh

private theorem cancel_counit_factors
    {C : Type*} [Category C] {A B D E F G : C}
    (a : A ≅ B) (t : A ⟶ D) (e : D ⟶ E) (b : E ≅ F) (c : F ≅ G)
    (d : B ⟶ G) (h : t ≫ e ≫ b.hom ≫ c.hom = a.hom ≫ d) :
    a.inv ≫ t ≫ e = d ≫ c.inv ≫ b.inv := by
  have h' := congrArg (fun k => a.inv ≫ k ≫ c.inv ≫ b.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Category.id_comp, Category.comp_id] using h'

private theorem termwise_exact_factors
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) =
      F.mapDerivedCategoryFactors.app P := by
  apply Iso.ext
  change F.mapDerivedCategoryFactorsh.hom.app
    ((HomotopyCategory.quotient C (.up ℤ)).obj P) = F.mapDerivedCategoryFactors.hom.app P
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  change F.mapDerivedCategory.map (𝟙 _) ≫ F.mapDerivedCategoryFactors.hom.app P ≫
    𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
  erw [F.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id]
  simp only [Category.id_comp]
  exact Category.comp_id _

@[reassoc] private theorem termwise_counit_transport
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    (F : C ⥤ D) [F.Additive] (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex C ℤ) :
    L.map ((DerivedCategory.quotientCompQhIso C).inv.app P) ≫
      ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
      (DerivedCategory.quotientCompQhIso D).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) := by
  change L.map (𝟙 _) ≫ ε.app _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ = _
  erw [L.map_id, DerivedCategory.Qh.map_id]
  change 𝟙 _ ≫ ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) ≫ 𝟙 _ ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

private theorem termwise_homotopy_square_inv
    {C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive B] [Abelian E]
    [HasDerivedCategory.{w} E]
    {F : C ⥤ D} {G : D ⥤ E} {R : C ⥤ B} {J : B ⥤ E}
    [F.Additive] [G.Additive] [R.Additive] [J.Additive]
    (e : F ⋙ G ≅ R ⋙ J) (P : CochainComplex C ℤ) :
    DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso e (.up ℤ) ≪≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ J)) (.up ℤ)).symm).inv.app
          ((HomotopyCategory.quotient C (.up ℤ)).obj P)) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.inv (.up ℤ)).app P) := by
  change DerivedCategory.Qh.map
    ((Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ J)) (.up ℤ)).hom.app _ ≫
      (Functor.mapHomotopyCategoryCompIso e (.up ℤ)).inv.app _) = _
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp]
  rfl

private theorem counit_square_of_normalized
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {A B : C} {S T V₁ V₂ V₃ V₄ : D}
    {a : S ⟶ T} {t : T ⟶ F.obj A} {ε ε₀ : A ⟶ B}
    {d₁ : S ⟶ V₁} {d₂ : V₁ ⟶ V₂} {d₃ : V₂ ⟶ V₃} {d₄ : V₃ ⟶ V₄}
    {δ : S ⟶ V₄} {β : V₄ ⟶ F.obj B}
    (hε : ε = ε₀) (hδ : d₁ ≫ d₂ ≫ d₃ ≫ d₄ = δ)
    (h : a ≫ t ≫ F.map ε₀ = δ ≫ β) :
    a ≫ t ≫ F.map ε = d₁ ≫ d₂ ≫ d₃ ≫ d₄ ≫ β := by
  rw [hε, h, ← hδ]
  simp only [Category.assoc]

-- Normalize the localization factors before specializing to sheaves on schemes.
private theorem termwise_counit_square
    {C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [Abelian C] [Abelian D] [Abelian B] [Abelian E]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} E]
    (F : C ⥤ D) (G : D ⥤ E) (R : C ⥤ B) (J : B ⥤ E)
    [F.Additive] [G.Additive] [R.Additive] [J.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (LJ : DerivedCategory B ⥤ DerivedCategory E)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (δ : DerivedCategory.Qh ⋙ LJ ⟶ J.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (e : F ⋙ G ≅ R ⋙ J) (P : CochainComplex C ℤ)
    (θ : LJ.obj (R.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ⟶
      G.mapDerivedCategory.obj (L.obj (DerivedCategory.Q.obj P)))
    (h : θ ≫ G.mapDerivedCategory.map
          (ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P)) ≫
        G.mapDerivedCategoryFactorsh.hom.app
          ((F.mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient C (.up ℤ)).obj P)) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso e (.up ℤ) ≪≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ J)) (.up ℤ)).symm).hom.app
              ((HomotopyCategory.quotient C (.up ℤ)).obj P)) =
      LJ.map (R.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient C (.up ℤ)).obj P)) ≫
        δ.app ((R.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient C (.up ℤ)).obj P))) :
    LJ.map (R.mapDerivedCategoryFactors.inv.app P) ≫ θ ≫
        G.mapDerivedCategory.map
          (L.map ((DerivedCategory.quotientCompQhIso C).inv.app P) ≫
            ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) ≫
            DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
            (DerivedCategory.quotientCompQhIso D).hom.app
              ((F.mapHomologicalComplex (.up ℤ)).obj P)) =
      LJ.map ((DerivedCategory.quotientCompQhIso B).inv.app
          ((R.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        δ.app ((HomotopyCategory.quotient B (.up ℤ)).obj
          ((R.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        DerivedCategory.Qh.map ((J.mapHomotopyCategoryFactors (.up ℤ)).hom.app
          ((R.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        (DerivedCategory.quotientCompQhIso E).hom.app
          ((J.mapHomologicalComplex (.up ℤ)).obj
            ((R.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.inv (.up ℤ)).app P) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
  refine counit_square_of_normalized (F := G.mapDerivedCategory)
    (termwise_counit_transport F L ε P)
    (termwise_counit_transport J LJ δ ((R.mapHomologicalComplex (.up ℤ)).obj P)) ?_
  have hf := congrArg Iso.hom (termwise_exact_factors R P)
  change R.mapDerivedCategoryFactorsh.hom.app
    ((HomotopyCategory.quotient C (.up ℤ)).obj P) =
      R.mapDerivedCategoryFactors.hom.app P at hf
  rw [hf] at h
  have h' := cancel_counit_factors
    (LJ.mapIso (R.mapDerivedCategoryFactors.app P)) θ
    (G.mapDerivedCategory.map (ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P)))
    (G.mapDerivedCategoryFactorsh.app
      ((F.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient C (.up ℤ)).obj P)))
    (DerivedCategory.Qh.mapIso
      ((Functor.mapHomotopyCategoryCompIso e (.up ℤ) ≪≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ J)) (.up ℤ)).symm).app
          ((HomotopyCategory.quotient C (.up ℤ)).obj P)))
    (δ.app ((HomotopyCategory.quotient B (.up ℤ)).obj
      ((R.mapHomologicalComplex (.up ℤ)).obj P))) h
  have htarget := congrArg Iso.inv
    (termwise_exact_factors G ((F.mapHomologicalComplex (.up ℤ)).obj P))
  exact h'.trans (congrArg₂ (fun x y ↦
    δ.app ((HomotopyCategory.quotient B (.up ℤ)).obj
      ((R.mapHomologicalComplex (.up ℤ)).obj P)) ≫ x ≫ y)
    (termwise_homotopy_square_inv e P) htarget)

/-- The derived open coefficient on an actual restricted complex is compatible
with ordinary tensor pullback and the pinned counits. This is an equality before
stalks and cohomology; it needs neither a base-change square nor K-flatness.

Proof: specialize `open_pinned_counit_homotopy_restriction` to the homotopy
quotient of P. Its source exact-restriction factor is the complex localization
factor: expand `mapDerivedCategoryFactorsh_hom_app` and cancel the identity
quotient comparison maps. Precompose the equation with the inverse of this
factor mapped by Lj*. Postcompose with the inverse localized homotopy tensor
restriction isomorphism, then with the inverse target exact-restriction factor.
Cancel the three pairs of inverse isomorphisms. The resulting target composite
is exactly `singleComplexOpenTensorRestrictionMap`; the source composite uses
the canonical inverse representative factor a. This works for every complex,
before stalks or cohomology, with no inversion of a pullback counit. Empty and
top opens and zero complexes use the same natural-transformation identities.

Source: Stacks Project, cohomology.tex, Tags 08HY, 08FE and 0D5S;
perfect.tex, Tag 0DJ9, first paragraph.
(blueprint: lem-pc-single-complex-open-counit-compatibility). -/
theorem singleComplexOpen_termwise_counit_compatibility
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ g')
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    letI : (schemeOpenRestriction X U).Additive := schemeOpenRestriction_additive X U
    letI : (schemeOpenRestriction X' U').Additive := schemeOpenRestriction_additive X' U'
    let K := DerivedCategory.Q.obj P
    let Q := ((schemeOpenRestriction X U).mapHomologicalComplex (.up ℤ)).obj P
    let a := (schemeOpenRestriction X U).mapDerivedCategoryFactors.symm.app P
    let θ := singleComplexRestrictedCoefficient g' K ((derivedPullback g').obj K) (𝟙 _)
      U U' j hj
    (derivedPullback j).map a.hom ≫ θ ≫
        (schemeOpenRestriction X' U').mapDerivedCategory.map
          ((derivedPullback g').map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
            (counit g').app ((HomotopyCategory.quotient
              (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).obj P) ≫
            DerivedCategory.Qh.map
              (((Scheme.Modules.tensorPullback g').mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
            (DerivedCategory.quotientCompQhIso
              (SheafOfModules.{u} (moduleRings X'.toRingedSpace))).hom.app
              (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)) =
      (derivedPullback j).map ((DerivedCategory.quotientCompQhIso _).inv.app Q) ≫
        (counit j).app ((HomotopyCategory.quotient _ (.up ℤ)).obj Q) ≫
        DerivedCategory.Qh.map
          (((Scheme.Modules.tensorPullback j).mapHomotopyCategoryFactors (.up ℤ)).hom.app Q) ≫
        (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (moduleRings U'.toScheme.toRingedSpace))).hom.app
          (((Scheme.Modules.tensorPullback j).mapHomologicalComplex (.up ℤ)).obj Q) ≫
        singleComplexOpenTensorRestrictionMap g' U U' j hj P := by
  have : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
      (Scheme.Modules.tensorPullback k).Additive := fun k => tensorPullbackAdditive k
  let := schemeOpenRestriction_additive X U
  let := schemeOpenRestriction_additive X' U'
  have : PreservesFiniteLimits (schemeOpenRestriction X U) :=
    schemeOpenRestriction_preservesFiniteLimits X U
  have : PreservesFiniteColimits (schemeOpenRestriction X U) :=
    schemeOpenRestriction_preservesFiniteColimits X U
  have : PreservesFiniteLimits (schemeOpenRestriction X' U') :=
    schemeOpenRestriction_preservesFiniteLimits X' U'
  have : PreservesFiniteColimits (schemeOpenRestriction X' U') :=
    schemeOpenRestriction_preservesFiniteColimits X' U'
  let := tensorPullbackAdditive g'
  let := tensorPullbackAdditive j
  let : (schemeOpenRestriction X U ⋙ Scheme.Modules.tensorPullback j).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  let : (Scheme.Modules.tensorPullback g' ⋙ schemeOpenRestriction X' U').PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  dsimp only [singleComplexOpenTensorRestrictionMap]
  exact termwise_counit_square
    (Scheme.Modules.tensorPullback g') (schemeOpenRestriction X' U')
    (schemeOpenRestriction X U) (Scheme.Modules.tensorPullback j)
    (derivedPullback g') (derivedPullback j) (counit g') (counit j)
    (openPinnedTensorRestrictionIso g' U U' j hj) P _
    (open_pinned_counit_homotopy_restriction g' U U' j hj
      ((HomotopyCategory.quotient
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).obj P))

end AlgebraicGeometry
