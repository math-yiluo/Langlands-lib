/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SmoothPurity.ClosedSupportHom
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.Yoneda
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Finite.BaseChange
import WeilConjectures.SixFunctors.BaseChange.GlobalSections
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-!
# Naturality of the supported Hom identification under base change

Source: literature/stacks-project/etale-cohomology.tex, Tag 0A45,
lemma-cohomology-with-support-triangle;
blueprint sec-smooth-purity/sk-prop-sf-cbc
(blueprint: lem-asd-supported-kummer-support-hom-naturality).
-/

@[expose] public section

set_option autoImplicit false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true

universe w v u v' u' v'' u'' v₀ u₀

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor ZeroObject

attribute [local instance 200000] CategoryTheory.Abelian.toPreadditive
attribute [local instance 200000] CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasSheafify
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasWeakSheafify
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasGlobalSections

/-- The standard resolution functor and its unit, packaged before site specialization.
Source: Stacks, Tag 079P (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
structure SupportedHomResolutionData (C : Type u') [Category.{v'} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] where
  R : CochainComplex C ℤ ⥤ CochainComplex C ℤ
  unit : 𝟭 (CochainComplex C ℤ) ⟶ R
  isKInjective : ∀ K, (R.obj K).IsKInjective
  unitMonoQuasiIso : ∀ K, HomologicalComplex.monoQuasiIso C (.up ℤ) (unit.app K)
  isFibrant : ∀ K, (HomologicalComplex.monoQuasiIso C (.up ℤ)).rlp
    (0 : R.obj K ⟶ (0 : CochainComplex C ℤ))

/-- Package the existing functorial resolution, without changing its chosen objects.
Source: Stacks, Tag 079P (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedHomResolutionData (C : Type u') [Category.{v'} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] : SupportedHomResolutionData C where
  R := CochainComplex.kInjectiveResolutionFunctor C
  unit := CochainComplex.toKInjectiveResolution C
  isKInjective := fun _ ↦ inferInstance
  unitMonoQuasiIso := CochainComplex.monoQuasiIso_toKInjectiveResolution_app C
  isFibrant := by
    intro K
    let d := MorphismProperty.functorialFactorizationData
      (HomologicalComplex.monoQuasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.monoQuasiIso C (ComplexShape.up ℤ)).rlp
    have hp := d.hp ((CochainComplex.toArrowZero C).obj K)
    have he : d.p.app ((CochainComplex.toArrowZero C).obj K) = 0 :=
      (isZero_zero (CochainComplex C ℤ)).eq_of_tgt _ _
    rw [he] at hp
    exact hp

namespace CategoryTheory.Functor

/-- The canonical comparison from a derived functor to its functorial resolution model.
Source: Stacks, Tag 070K (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedHomResolutionMap
    {C : Type u'} [Category.{v'} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    {B : Type u} [Category.{v} B] [Abelian B]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{v} B]
    (F : C ⥤ B) [F.Additive] (K : CochainComplex C ℤ) :
    F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((supportedHomResolutionData C).R.obj K)) := by
  letI := (supportedHomResolutionData C).isKInjective K
  exact F.rightDerivedFunctor.map
      (DerivedCategory.Q.map ((supportedHomResolutionData C).unit.app K)) ≫
    (F.rightDerivedFunctorObjQIso ((supportedHomResolutionData C).R.obj K)).hom

end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance 200000] closedSupportEtaleAbelian
attribute [local instance 200000] closedSupportEtaleLinear

/-- The Grothendieck property for the same fixed abelian structure.
Source: Stacks, Tag 03DA (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
theorem supportedEtaleGrothendieck (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  inferInstance

attribute [local instance 200000] supportedEtaleGrothendieck

/-- The fixed functorial resolution on the etale site.
Source: Stacks, Tag 079P (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedResolutionFunctor (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ ⥤
      CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ :=
  (supportedHomResolutionData (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).R

/-- The resolution unit, with its target functor fixed explicitly.
Source: Stacks, Tag 079P (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedResolutionUnit (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    𝟭 (CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) ⟶
      supportedResolutionFunctor A T :=
  (supportedHomResolutionData (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).unit

/-- Functorial degreewise-injective K-injective replacement, on the specified etale site.
Source: Stacks, Tag 079P (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev supportedResolution (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ :=
  (supportedResolutionFunctor A T).obj K

/-- The functor of complexes of Hom from the closed constant sheaf.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedHomComplexFunctor (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) :=
  (closedSupportHomFunctor A i).mapHomologicalComplex (.up ℤ)

/-- The global-section functor on complexes.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedSectionsComplexFunctor (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) :=
  (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The open-section functor on complexes.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedOpenSectionsComplexFunctor (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (v : V ⟶ T) :=
  (upperStar (ModuleCat.{u + 1} A) v ⋙
    Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Termwise ordinary Hom from the closed constant sheaf. Source: Stacks, Tag 0A45
(blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev supportedHomComplex (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T)
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    CochainComplex (ModuleCat.{u + 1} A) ℤ :=
  (supportedHomComplexFunctor A i).obj I

/-- Termwise inverse image as a fixed functor on complexes.
Source: Stacks, Tag 03Q1 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedPullbackComplexFunctor (A : Type (u + 1)) [CommRing A]
    {T' T : Scheme.{u}} (h : T' ⟶ T) :
    CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ ⥤
      CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ :=
  (upperStar (ModuleCat.{u + 1} A) h).mapHomologicalComplex (.up ℤ)

/-- The inverse image of a complex is taken termwise; exactness makes this derived pullback.
Source: Stacks, Tag 03Q1 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev supportedPullbackComplex (A : Type (u + 1)) [CommRing A]
    {T' T : Scheme.{u}} (h : T' ⟶ T)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ :=
  (supportedPullbackComplexFunctor A h).obj K

/-- The normalized cone model, with its complex functors supplied as parameters.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
structure SupportedHomDiagram (B₀ : Type u) [Category.{v} B₀] [Abelian B₀]
    (D₀ : Type u₀) [Category.{v₀} D₀]
    (Q₀ : CochainComplex B₀ ℤ ⥤ D₀)
    (C : Type u') [Category.{v'} C] where
  R : C ⥤ C
  F : C ⥤ CochainComplex B₀ ℤ
  E : C ⥤ CochainComplex B₀ ℤ
  B : C ⥤ CochainComplex B₀ ℤ
  H : C ⥤ D₀
  modelMap : ∀ K, H.obj K ⟶ Q₀.obj (F.obj (R.obj K))
  restriction : ∀ I n, (E.obj I).X n ⟶ (B.obj I).X n
  normalization : ∀ I, (F.obj I ⟶ E.obj I) → Prop

/-- A normalized cone model of a fixed diagram.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
structure SupportedHomConeModelCore (B₀ : Type u) [Category.{v} B₀] [Abelian B₀]
    (D₀ : Type u₀) [Category.{v₀} D₀]
    (Q₀ : CochainComplex B₀ ℤ ⥤ D₀)
    (C : Type u') [Category.{v'} C]
    (d : SupportedHomDiagram B₀ D₀ Q₀ C) where
  q : d.E ⟶ d.B
  q_spec : ∀ I n, (q.app I).f n = d.restriction I n
  modelIso : ∀ K, d.H.obj K ≅ Q₀.obj (d.F.obj (d.R.obj K))
  modelIso_spec : ∀ K, (modelIso K).hom = d.modelMap K
  toSections : ∀ K, d.F.obj (d.R.obj K) ⟶ d.E.obj (d.R.obj K)
  toSections_spec : ∀ K, d.normalization (d.R.obj K) (toSections K)
  inclusion : ∀ K, d.F.obj (d.R.obj K) ⟶
    (CochainComplex.mappingCone (q.app (d.R.obj K)))⟦(-1 : ℤ)⟧
  inclusion_fst : ∀ K (n m : ℤ) (hm : m = n + (-1 : ℤ)) (hn : m + 1 = n),
    (inclusion K).f n ≫ (CochainComplex.shiftFunctorObjXIso _ (-1) n m hm).hom ≫
      HomologicalComplex.homotopyCofiber.fstX (q.app (d.R.obj K)) m n hn =
        (toSections K).f n
  inclusion_snd : ∀ K (n m : ℤ) (hm : m = n + (-1 : ℤ)),
    (inclusion K).f n ≫ (CochainComplex.shiftFunctorObjXIso _ (-1) n m hm).hom ≫
      HomologicalComplex.homotopyCofiber.sndX (q.app (d.R.obj K)) m = 0
  comparison : ∀ K, d.H.obj K ≅
    Q₀.obj ((CochainComplex.mappingCone (q.app (d.R.obj K)))⟦(-1 : ℤ)⟧)
  comparison_spec : ∀ K, (comparison K).hom =
    (modelIso K).hom ≫ Q₀.map (inclusion K)
  comparison_naturality : ∀ (K L : C) (f : K ⟶ L),
    d.H.map f ≫ (comparison L).hom =
      (comparison K).hom ≫ Q₀.map
        ((shiftFunctor (CochainComplex (B₀) ℤ) (-1 : ℤ)).map
          (CochainComplex.mappingCone.map _ _ (d.E.map (d.R.map f)) (d.B.map (d.R.map f))
            (q.naturality (d.R.map f)).symm))
  projection : ∀ K, (CochainComplex.mappingCone (q.app (d.R.obj K)))⟦(-1 : ℤ)⟧ ⟶ d.E.obj (d.R.obj K)
  projection_spec : ∀ K (n m : ℤ) (hm : m = n + (-1 : ℤ)) (hn : m + 1 = n),
    (projection K).f n = (CochainComplex.shiftFunctorObjXIso _ (-1) n m hm).hom ≫
      HomologicalComplex.homotopyCofiber.fstX (q.app (d.R.obj K)) m n hn

/-- Transport a map through the two fixed derived models.
Source: Stacks, Tag 070K (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev SupportedHomConeModelCore.transport
    {B₀ : Type u} [Category.{v} B₀] [Abelian B₀]
    {D₀ : Type u₀} [Category.{v₀} D₀]
    {Q₀ : CochainComplex B₀ ℤ ⥤ D₀}
    {C : Type u'} [Category.{v'} C]
    {d : SupportedHomDiagram B₀ D₀ Q₀ C}
    {C' : Type u''} [Category.{v''} C']
    {d' : SupportedHomDiagram B₀ D₀ Q₀ C'}
    (M : SupportedHomConeModelCore B₀ D₀ Q₀ C d)
    (M' : SupportedHomConeModelCore B₀ D₀ Q₀ C' d')
    (K : C) (K' : C') (f : d.F.obj (d.R.obj K) ⟶ d'.F.obj (d'.R.obj K')) :
    d.H.obj K ⟶ d'.H.obj K' :=
  (M.modelIso K).hom ≫ Q₀.map f ≫ (M'.modelIso K').inv

/-- Build the resolution and section diagram before specifying a concrete sheaf category.
Source: Stacks, Tags 070K, 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedHomDiagramFactory
    {C : Type u'} [Category.{v'} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    {D : Type u} [Category.{v} D] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{v} D]
    (F E B : C ⥤ D) [F.Additive] [E.PreservesZeroMorphisms] [B.PreservesZeroMorphisms]
    (restriction : ∀ (I : CochainComplex C ℤ) n,
      ((E.mapHomologicalComplex (.up ℤ)).obj I).X n ⟶
        ((B.mapHomologicalComplex (.up ℤ)).obj I).X n)
    (α : F ⟶ E) :
    SupportedHomDiagram D (DerivedCategory.{v} D) DerivedCategory.Q (CochainComplex C ℤ) where
  R := (supportedHomResolutionData C).R
  F := F.mapHomologicalComplex (.up ℤ)
  E := E.mapHomologicalComplex (.up ℤ)
  B := B.mapHomologicalComplex (.up ℤ)
  H := DerivedCategory.Q ⋙ F.rightDerivedFunctor
  modelMap := CategoryTheory.Functor.supportedHomResolutionMap F
  restriction := restriction
  normalization := fun I t ↦
    t = (NatTrans.mapHomologicalComplex α (.up ℤ)).app I

/-- The functors and normalization maps defining the supported-Hom diagram.
Source: Stacks, Tags 070K, 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedHomDiagram (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} (i : D ⟶ T) (v : V ⟶ T) :
    SupportedHomDiagram (ModuleCat.{u + 1} A)
      (DerivedCategory.{u + 1} (ModuleCat.{u + 1} A)) DerivedCategory.Q
      (CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  supportedHomDiagramFactory
    (C := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (D := ModuleCat.{u + 1} A) (closedSupportHomFunctor A i)
    (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (upperStar (ModuleCat.{u + 1} A) v ⋙ Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (fun I n ↦ (closedSupportSectionsPullback A v).app (I.X n))
    (closedSupportHomToSections A i)

/-- The condition that a resolution comparison extends the resolution unit.
Source: Stacks, Tag 079P (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
def supportedResolutionComparisonCondition (A : Type (u + 1)) [CommRing A]
    {T' T : Scheme.{u}} (h : T' ⟶ T)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (a : supportedPullbackComplex A h (supportedResolution A T K) ⟶
      supportedResolution A T' (supportedPullbackComplex A h K)) : Prop :=
  (supportedPullbackComplexFunctor A h).map
    ((supportedResolutionUnit A T).app K) ≫ a =
      (supportedResolutionUnit A T').app (supportedPullbackComplex A h K)

/-- The degreewise formula for pullback of sections along a comparison of complexes.
Source: Stacks, Tag 03Q1 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
def supportedSectionsMapCondition (A : Type (u + 1)) [CommRing A]
    {T' T : Scheme.{u}} (h : T' ⟶ T)
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (J : CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (a : supportedPullbackComplex A h I ⟶ J)
    (s : (supportedSectionsComplexFunctor A T).obj I ⟶
      (supportedSectionsComplexFunctor A T').obj J) : Prop :=
  ∀ n, s.f n = globalSectionsUpperStarMap (ModuleCat.{u + 1} A) h (I.X n) ≫
    (Sheaf.Γ T'.smallEtaleTopology (ModuleCat.{u + 1} A)).map (a.f n)

/-- The degreewise formula for the open part of a pullback square.
Source: Stacks, Tag 03Q1 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
def supportedOpenSectionsMapCondition (A : Type (u + 1)) [CommRing A]
    {T' T V' V : Scheme.{u}} (h : T' ⟶ T) (v : V ⟶ T) (v' : V' ⟶ T')
    (hV : V' ⟶ V) (sqV : IsPullback hV v' v h)
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (J : CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (a : supportedPullbackComplex A h I ⟶ J)
    (b : (supportedOpenSectionsComplexFunctor A v).obj I ⟶
      (supportedOpenSectionsComplexFunctor A v').obj J) : Prop :=
  ∀ n, b.f n = globalSectionsUpperStarMap (ModuleCat.{u + 1} A) hV
    ((upperStar (ModuleCat.{u + 1} A) v).obj (I.X n)) ≫
      (Sheaf.Γ V'.smallEtaleTopology (ModuleCat.{u + 1} A)).map
        ((upperStarComp (ModuleCat.{u + 1} A) hV v).inv.app _ ≫
          (upperStarComp (ModuleCat.{u + 1} A) v' h (hV ≫ v) sqV.w).hom.app _ ≫
          (upperStar (ModuleCat.{u + 1} A) v').map (a.f n))

/-- The degreewise formula for inverse-image and precomposition on Hom complexes.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
def supportedHomMapCondition (A : Type (u + 1)) [CommRing A]
    {T' T D' D : Scheme.{u}} (h : T' ⟶ T) (i : D ⟶ T) (i' : D' ⟶ T')
    (e : (closedSupportHomSource A i') ⟶
      (upperStar (ModuleCat.{u + 1} A) h).obj
        ((closedSupportHomSource A i)))
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (J : CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (a : supportedPullbackComplex A h I ⟶ J)
    (f : supportedHomComplex A i I ⟶ supportedHomComplex A i' J) : Prop :=
  ∀ (n : ℤ) (c : (closedSupportHomSource A i) ⟶ I.X n),
    (f.f n) c = e ≫ (upperStar (ModuleCat.{u + 1} A) h).map c ≫ a.f n

/-- Pullback maps with the source complexes and their functors left abstract.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
structure SupportedHomPullbackDiagram
    (B₀ : Type u) [Category.{v} B₀] [Abelian B₀]
    (D₀ : Type u₀) [Category.{v₀} D₀] (Q₀ : CochainComplex B₀ ℤ ⥤ D₀)
    (C : Type u') [Category.{v'} C] (C' : Type u'') [Category.{v''} C'] where
  source : SupportedHomDiagram B₀ D₀ Q₀ C
  target : SupportedHomDiagram B₀ D₀ Q₀ C'
  P : C ⥤ C'
  unitSpec : ∀ K, (P.obj (source.R.obj K) ⟶ target.R.obj (P.obj K)) → Prop
  sectionsSpec : ∀ I J, (P.obj I ⟶ J) → (source.E.obj I ⟶ target.E.obj J) → Prop
  openSpec : ∀ I J, (P.obj I ⟶ J) → (source.B.obj I ⟶ target.B.obj J) → Prop
  homSpec : ∀ I J, (P.obj I ⟶ J) → (source.F.obj I ⟶ target.F.obj J) → Prop

/-- Normalized representative maps for a fixed pullback diagram.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
structure SupportedHomPullbackMaps
    (B₀ : Type u) [Category.{v} B₀] [Abelian B₀]
    (D₀ : Type u₀) [Category.{v₀} D₀] (Q₀ : CochainComplex B₀ ℤ ⥤ D₀)
    (C : Type u') [Category.{v'} C] (C' : Type u'') [Category.{v''} C']
    (d : SupportedHomPullbackDiagram B₀ D₀ Q₀ C C') where
  sourceModel : SupportedHomConeModelCore B₀ D₀ Q₀ C d.source
  targetModel : SupportedHomConeModelCore B₀ D₀ Q₀ C' d.target
  resolutionComparison : ∀ K, d.P.obj (d.source.R.obj K) ⟶ d.target.R.obj (d.P.obj K)
  resolutionComparison_spec : ∀ K, d.unitSpec K (resolutionComparison K)
  sectionsMap : ∀ K, d.source.E.obj (d.source.R.obj K) ⟶ d.target.E.obj (d.target.R.obj (d.P.obj K))
  sectionsMap_spec : ∀ K, d.sectionsSpec (d.source.R.obj K)
    (d.target.R.obj (d.P.obj K)) (resolutionComparison K) (sectionsMap K)
  openSectionsMap : ∀ K, d.source.B.obj (d.source.R.obj K) ⟶
    d.target.B.obj (d.target.R.obj (d.P.obj K))
  openSectionsMap_spec : ∀ K, d.openSpec (d.source.R.obj K)
    (d.target.R.obj (d.P.obj K)) (resolutionComparison K) (openSectionsMap K)
  restriction_square : ∀ K, sectionsMap K ≫ targetModel.q.app (d.target.R.obj (d.P.obj K)) =
    sourceModel.q.app (d.source.R.obj K) ≫ openSectionsMap K
  homMap : ∀ K, d.source.F.obj (d.source.R.obj K) ⟶ d.target.F.obj (d.target.R.obj (d.P.obj K))
  homMap_spec : ∀ K, d.homSpec (d.source.R.obj K)
    (d.target.R.obj (d.P.obj K)) (resolutionComparison K) (homMap K)

/-- The specialization of the representative-map record to an etale pullback square.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedHomPullbackDiagram (A : Type (u + 1)) [CommRing A]
    {T' T D' D V' V : Scheme.{u}} (h : T' ⟶ T) (i : D ⟶ T) (i' : D' ⟶ T')
    (v : V ⟶ T) (v' : V' ⟶ T') (hV : V' ⟶ V) (sqV : IsPullback hV v' v h)
    (e : (closedSupportHomSource A i') ⟶
      (upperStar (ModuleCat.{u + 1} A) h).obj
        ((closedSupportHomSource A i))) :
  SupportedHomPullbackDiagram (ModuleCat.{u + 1} A)
    (DerivedCategory.{u + 1} (ModuleCat.{u + 1} A)) DerivedCategory.Q
    (CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) where
  source := supportedHomDiagram A i v
  target := supportedHomDiagram A i' v'
  P := supportedPullbackComplexFunctor A h
  unitSpec := supportedResolutionComparisonCondition A h
  sectionsSpec := supportedSectionsMapCondition A h
  openSpec := supportedOpenSectionsMapCondition A h v v' hV sqV
  homSpec := supportedHomMapCondition A h i i' e

/-- The type of normalized maps on the fixed etale pullback diagram.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
abbrev supportedHomPullbackMapsType (A : Type (u + 1)) [CommRing A]
    {T' T D' D V' V : Scheme.{u}} (h : T' ⟶ T) (i : D ⟶ T) (i' : D' ⟶ T')
    (v : V ⟶ T) (v' : V' ⟶ T') (hV : V' ⟶ V) (sqV : IsPullback hV v' v h)
    (e : (closedSupportHomSource A i') ⟶
      (upperStar (ModuleCat.{u + 1} A) h).obj
        ((closedSupportHomSource A i))) :=
  SupportedHomPullbackMaps (ModuleCat.{u + 1} A)
    (DerivedCategory.{u + 1} (ModuleCat.{u + 1} A)) DerivedCategory.Q
    (CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (supportedHomPullbackDiagram A h i i' v v' hV sqV e)

/-- The canonical representative maps for pullback of a closed/open pair. A resolution
comparison must extend the pulled-back resolution unit. Its section maps and Hom map are
specified degreewise; the relative pullback is then the diagonal mapping-cone map.
Source: Stacks, Tag 0A45 and blueprint lemma-cycle-class-cartier-divisor, penultimate paragraph
(blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
structure SupportedKummerSupportHomData (A : Type (u + 1)) [CommRing A]
    {T' T D' D V' V : Scheme.{u}} (h : T' ⟶ T) (i : D ⟶ T)
    (i' : D' ⟶ T') (hD : D' ⟶ D) (v : V ⟶ T) (v' : V' ⟶ T')
    (sqD : IsPullback hD i' i h) (hV : V' ⟶ V) (sqV : IsPullback hV v' v h) where
  exchange_isIso : IsIso (supportedConstantExchange A i i' h hD sqD.toCommSq)
  exchangeInverse : (closedSupportHomSource A i') ⟶
    (upperStar (ModuleCat.{u + 1} A) h).obj
      ((closedSupportHomSource A i))
  exchange_hom_inv : supportedConstantExchange A i i' h hD sqD.toCommSq ≫ exchangeInverse = 𝟙 _
  exchange_inv_hom : exchangeInverse ≫ supportedConstantExchange A i i' h hD sqD.toCommSq = 𝟙 _
  maps : supportedHomPullbackMapsType A h i i' v v' hV sqV exchangeInverse

namespace SupportedKummerSupportHomData

variable {A : Type (u + 1)} [CommRing A]
    {T' T D' D V' V : Scheme.{u}} {h : T' ⟶ T} {i : D ⟶ T} {i' : D' ⟶ T'}
    {hD : D' ⟶ D} {v : V ⟶ T} {v' : V' ⟶ T'} {sqD : IsPullback hD i' i h}
    {hV : V' ⟶ V} {sqV : IsPullback hV v' v h}

/-- The source normalized cone model.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev sourceModel
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) := N.maps.sourceModel

/-- The target normalized cone model.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev targetModel
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) := N.maps.targetModel

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def resolutionComparison
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.resolutionComparison

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
abbrev resolutionComparison_spec
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.resolutionComparison_spec

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def sectionsMap
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.sectionsMap

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
abbrev sectionsMap_spec
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.sectionsMap_spec

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def openSectionsMap
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.openSectionsMap

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
abbrev openSectionsMap_spec
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.openSectionsMap_spec

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
abbrev restriction_square
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.restriction_square

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def homMap
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.homMap

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
abbrev homMap_spec
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.homMap_spec

end SupportedKummerSupportHomData

set_option backward.isDefEq.respectTransparency false

private theorem supportedInclusionProjection
    {B₀ : Type u} [Category.{v} B₀] [Abelian B₀]
    {D₀ : Type u₀} [Category.{v₀} D₀]
    {Q₀ : CochainComplex B₀ ℤ ⥤ D₀}
    {C : Type u'} [Category.{v'} C]
    {d : SupportedHomDiagram B₀ D₀ Q₀ C}
    (M : SupportedHomConeModelCore B₀ D₀ Q₀ C d) (K : C) :
    M.inclusion K ≫ M.projection K = M.toSections K := by
  ext n : 1
  rw [HomologicalComplex.comp_f, M.projection_spec K n (n + (-1)) rfl (by omega)]
  exact M.inclusion_fst K n (n + (-1)) rfl (by omega)

private theorem supportedForget
    {B₀ : Type u} [Category.{v} B₀] [Abelian B₀]
    {D₀ : Type u₀} [Category.{v₀} D₀]
    {Q₀ : CochainComplex B₀ ℤ ⥤ D₀}
    {C : Type u'} [Category.{v'} C]
    {d : SupportedHomDiagram B₀ D₀ Q₀ C}
    {E : Type u''} [Category.{v''} E]
    (M : SupportedHomConeModelCore B₀ D₀ Q₀ C d) (H : D₀ ⥤ E) (K : C) :
    H.map (Q₀.map (M.projection K)) = H.map (M.comparison K).inv ≫
      H.map ((M.modelIso K).hom ≫ Q₀.map (M.toSections K)) := by
  apply (cancel_epi (H.map (M.comparison K).hom)).mp
  rw [← H.map_comp, ← Category.assoc, ← H.map_comp, Iso.hom_inv_id, H.map_id,
    Category.id_comp, M.comparison_spec, Category.assoc, ← Q₀.map_comp,
    supportedInclusionProjection]

private noncomputable def supportedComplexComparison
    {C : Type u} [Category.{v} C] [Preadditive C]
    {D : Type u'} [Category.{v'} D] [Preadditive D]
    {B : Type u''} [Category.{v''} B] [Preadditive B]
    (H : C ⥤ D) [H.PreservesZeroMorphisms]
    (E : C ⥤ B) [E.PreservesZeroMorphisms]
    (E' : D ⥤ B) [E'.PreservesZeroMorphisms] (α : E ⟶ H ⋙ E')
    (I : CochainComplex C ℤ) (J : CochainComplex D ℤ)
    (a : (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J) :
    (E.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶
      (E'.mapHomologicalComplex (ComplexShape.up ℤ)).obj J :=
  (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app I ≫
    (E'.mapHomologicalComplex (ComplexShape.up ℤ)).map a

private theorem supportedConstantComposition (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z) (k : X ⟶ Z) (hk : k = g ≫ f) :
    (upperStarComp (ModuleCat.{u + 1} A) g f k hk).hom.app (ordinaryFiniteConstant A Z) ≫
      (upperStar (ModuleCat.{u + 1} A) g).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).hom.app
          (ModuleCat.of A A)) ≫
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) g).hom.app
        (ModuleCat.of A A) =
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) k).hom.app
        (ModuleCat.of A A) := by
  subst k
  exact Scheme.upperStarConstantSheafIso_comp (ModuleCat.{u + 1} A) g f (ModuleCat.of A A)

private theorem supportedBaseChangeUnit (A : Type (u + 1)) [CommRing A]
    {T' T D' D : Scheme.{u}} (h : T' ⟶ T) (i : D ⟶ T) (i' : D' ⟶ T')
    (hD : D' ⟶ D) (sq : CommSq hD i' i h) :
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) h).app
        (ModuleCat.of A A)).inv ≫
      (upperStar (ModuleCat.{u + 1} A) h).map (supportedConstantUnit A i) ≫
        supportedConstantExchange A i i' h hD sq = supportedConstantUnit A i' := by
  let P := ordinaryFiniteConstant A T
  let H := upperStar (ModuleCat.{u + 1} A) h
  let HD := upperStar (ModuleCat.{u + 1} A) hD
  let L := lowerStar (ModuleCat.{u + 1} A) i'
  let c {X Y : Scheme.{u}} (f : X ⟶ Y) := (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A)
    f).hom.app
    (ModuleCat.of A A)
  have hc : (squareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app P ≫
      HD.map (c i) ≫ c hD = (upperStar (ModuleCat.{u + 1} A) i').map (c h) ≫ c i' := by
    dsimp only [squareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
    simp only [Category.assoc]
    rw [Scheme.upperStarConstantSheafIso_comp]
    apply (cancel_epi ((upperStarComp (ModuleCat.{u + 1} A) i' h (hD ≫ i) sq.w).hom.app P)).mp
    simp only [Iso.hom_inv_id_app_assoc]
    exact (supportedConstantComposition A i' h (hD ≫ i) sq.w).symm
  simp only [supportedConstantUnit, supportedConstantExchange, Adjunction.homEquiv_unit,
    Functor.map_comp, Category.assoc]
  change (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) h).inv.app
      (ModuleCat.of A A) ≫ H.map ((upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} A) i).unit.app P) ≫ H.map ((lowerStar
          (ModuleCat.{u + 1} A) i).map (c i)) ≫
      (baseChangeMap (ModuleCat.{u + 1} A) sq).app (ordinaryFiniteConstant A D) ≫
        L.map (c hD) =
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i').unit.app
      (ordinaryFiniteConstant A T') ≫ L.map (c i')
  rw [reassoc_of% (baseChangeMap_naturality (ModuleCat.{u + 1} A) sq (c i)),
    reassoc_of% (map_unit_baseChangeMap_app (ModuleCat.{u + 1} A) sq P)]
  rw [← L.map_comp, ← L.map_comp, hc]
  simp only [L.map_comp]
  have hn := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i').unit.naturality
    (c h)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  simp [c]

end AlgebraicGeometry.Etale
