import Langlands.AlgebraicGeometry.Modules.CanonicalPushforwardCohomology
import Langlands.Cohomology.AcyclicResolution.Composition
import Langlands.Cohomology.AcyclicResolution.DerivedComparison

/-!
# Canonical cohomology pullback computed on arbitrary right resolutions

For a morphism `h : Y ⟶ X` of schemes over `Spec R`, the canonical cohomology
pullback and the canonical pushforward comparison are defined through derived
categories and Mathlib's chosen injective resolutions. This file shows that both
are computed on arbitrary right resolutions (no acyclicity is assumed): given
right resolutions `KX` of `M` and `KY` of `N`, a coefficient map `a : M ⟶ h_* N`,
and a map `ψ : KX ⟶ h_* KY` compatible with the augmentations over `a`, the map
of section complexes induced by `ψ` agrees, under the canonical comparison maps
`resolutionComparison`, with cohomology of `a` followed by
`canonicalPushforwardCohomologyMap`.

The general part writes the canonical derived comparison of a right resolution
through the unit of the bounded below right derived functor.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open Langlands.Cohomology

namespace Langlands.Cohomology.AcyclicResolution

section General

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

/-- A natural-indexed cochain complex extended by zero to a bounded below
integer-indexed complex. -/
abbrev natPlus (K : CochainComplex C ℕ) : CochainComplex.Plus C :=
  ⟨K.extend ComplexShape.embeddingUpNat, ⟨0, inferInstance⟩⟩

/-- The extension by zero of a map of natural-indexed complexes. -/
abbrev natPlusMap {K L : CochainComplex C ℕ} (g : K ⟶ L) : natPlus K ⟶ natPlus L :=
  ObjectProperty.homMk (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat)

/-- The extended augmentation of a right resolution, as a map of bounded
below complexes. -/
abbrev natPlusAugmentation {A : C} {K : CochainComplex C ℕ}
    (ε : (CochainComplex.single₀ C).obj A ⟶ K) :
    (DerivedPlus.singlePlusFunctor C).obj A ⟶ natPlus K :=
  ObjectProperty.homMk
    ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat A 0 0 rfl).inv ≫
      HomologicalComplex.extendMap ε ComplexShape.embeddingUpNat)

instance isIso_Q_map_natPlusAugmentation [HasDerivedCategory C] {A : C}
    {K : CochainComplex C ℕ} (ε : (CochainComplex.single₀ C).obj A ⟶ K) [QuasiIso ε] :
    IsIso (DerivedCategory.Plus.Q.map (natPlusAugmentation ε)) := by
  apply Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso C)
  change QuasiIso ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat A 0 0
    rfl).inv ≫ HomologicalComplex.extendMap ε ComplexShape.embeddingUpNat)
  infer_instance

lemma natPlusAugmentation_comp_natPlusMap [HasDerivedCategory C] [EnoughInjectives C]
    {A : C} {K : CochainComplex C ℕ}
    (ε : (CochainComplex.single₀ C).obj A ⟶ K) (I : InjectiveResolution A)
    (φ : K ⟶ I.cocomplex) (hφ : ε ≫ φ = I.ι) :
    natPlusAugmentation ε ≫ (natPlusMap φ : natPlus K ⟶ DerivedPlus.resolutionPlus I) =
      DerivedPlus.resolutionPlusι I := by
  apply ObjectProperty.hom_ext
  change ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat A 0 0 rfl).inv ≫
      HomologicalComplex.extendMap ε ComplexShape.embeddingUpNat) ≫
      HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat = I.ι'
  rw [Category.assoc, ← HomologicalComplex.extendMap_comp, hφ]
  rfl

end General

section ExtendComp

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
  [HasZeroObject C] [HasZeroObject D] [HasZeroObject E]
  {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] [H.PreservesZeroMorphisms]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

/-- Degreewise form of `mapExtendIso_compIso`, on the components of the
extension indexed by `Option ι`. -/
lemma extendXMapIso_compIso (α : F ⋙ G ≅ H) (K : HomologicalComplex C c) (i : Option ι) :
    HomologicalComplex.extend.mapX ((Functor.mapHomologicalComplexCompIso α c).app K).hom i ≫
        (DerivedPlus.extendXMapIso H K i).hom =
      (DerivedPlus.extendXMapIso G ((F.mapHomologicalComplex c).obj K) i).hom ≫
        G.map (DerivedPlus.extendXMapIso F K i).hom ≫
          α.hom.app (HomologicalComplex.extend.X K i) :=
  match i with
  | none => (HomologicalComplex.extend.isZero_X _ rfl).eq_of_src _ _
  | some _ => by
      dsimp [DerivedPlus.extendXMapIso, HomologicalComplex.extend.mapX]
      erw [Category.comp_id, Category.id_comp, G.map_id, Category.id_comp]
      rfl

/-- Extension by zero commutes with the comparison of a composite functor. -/
lemma mapExtendIso_compIso (α : F ⋙ G ≅ H) (K : HomologicalComplex C c)
    (e : c.Embedding c') :
    HomologicalComplex.extendMap ((Functor.mapHomologicalComplexCompIso α c).app K).hom e ≫
        (DerivedPlus.mapExtendIso H K e).hom =
      (DerivedPlus.mapExtendIso G ((F.mapHomologicalComplex c).obj K) e).hom ≫
        (G.mapHomologicalComplex c').map (DerivedPlus.mapExtendIso F K e).hom ≫
          ((Functor.mapHomologicalComplexCompIso α c').app (K.extend e)).hom := by
  ext i'
  exact extendXMapIso_compIso α K (e.r i')

end ExtendComp

section AugmentationPlus

variable {C C' : Type*} [Category* C] [Category* C'] [Abelian C] [Abelian C']
  (P : C' ⥤ C) [P.Additive]

/-- A map from a natural-indexed complex into the image of another under `P`,
extended by zero to a map of bounded below complexes. -/
abbrev natPlusMapTo {KX : CochainComplex C ℕ} {KY : CochainComplex C' ℕ}
    (ψ : KX ⟶ (P.mapHomologicalComplex _).obj KY) :
    natPlus KX ⟶ P.mapCochainComplexPlus.obj (natPlus KY) :=
  ObjectProperty.homMk (HomologicalComplex.extendMap ψ ComplexShape.embeddingUpNat ≫
    (DerivedPlus.mapExtendIso P KY ComplexShape.embeddingUpNat).hom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A map of right resolutions into the image of a right resolution under `P`,
extended to bounded below complexes, is compatible with the extended
augmentations. -/
lemma natPlusAugmentation_comp_natPlusMapTo {M : C} {N : C'}
    {KX : CochainComplex C ℕ} {KY : CochainComplex C' ℕ}
    (εX : (CochainComplex.single₀ C).obj M ⟶ KX)
    (εY : (CochainComplex.single₀ C').obj N ⟶ KY) (a : M ⟶ P.obj N)
    (ψ : KX ⟶ (P.mapHomologicalComplex _).obj KY)
    (hψ : εX ≫ ψ = (CochainComplex.single₀ C).map a ≫ mapResolutionAugmentation P εY) :
    natPlusAugmentation εX ≫ natPlusMapTo P ψ =
      (DerivedPlus.singlePlusFunctor C).map a ≫
        (DerivedPlus.singlePlusMapIso P).hom.app N ≫
          P.mapCochainComplexPlus.map (natPlusAugmentation εY) := by
  have h0 := congrArg (fun f => HomologicalComplex.Hom.f f 0) hψ
  simp only [HomologicalComplex.comp_f, mapResolutionAugmentation_f_zero] at h0
  apply (CochainComplex.Plus.ι C).map_injective
  simp only [Functor.map_comp, DerivedPlus.singlePlusMapIso,
    NatIso.ofComponents_hom_app, Functor.preimageIso_hom, Functor.map_preimage,
    Iso.symm_hom]
  change ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M 0 0 rfl).inv ≫
      HomologicalComplex.extendMap εX ComplexShape.embeddingUpNat) ≫
      (HomologicalComplex.extendMap ψ ComplexShape.embeddingUpNat ≫
      (DerivedPlus.mapExtendIso P KY ComplexShape.embeddingUpNat).hom) =
    (CochainComplex.singleFunctor C 0).map a ≫
      (HomologicalComplex.singleMapHomologicalComplex P (.up ℤ) 0).inv.app N ≫
      (P.mapHomologicalComplex _).map
        ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat N 0 0 rfl).inv ≫
          HomologicalComplex.extendMap εY ComplexShape.embeddingUpNat)
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f,
    HomologicalComplex.extendSingleIso_inv_f,
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0)
      (i' := (0 : ℤ)) (by simp),
    CochainComplex.singleFunctor,
    HomologicalComplex.single_map_f_self,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    Functor.mapHomologicalComplex_map_f, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_assoc, DerivedPlus.extendXIso_inv_comp_mapExtendIso_hom]
  rw [reassoc_of% h0]
  dsimp only [CochainComplex.single₀, Functor.id_obj]
  simp only [HomologicalComplex.single_map_f_self, Category.assoc,
    CochainComplex.single₀ObjXSelf, Iso.inv_hom_id_assoc, ← Functor.map_comp]
  simp only [Iso.refl_inv]
  congr 2
  erw [Category.id_comp, Category.id_comp]

end AugmentationPlus

section Derived

universe w w' v v' u u'

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w} C] [EnoughInjectives C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical derived comparison of a right resolution, written through
the unit of the bounded below right derived functor. -/
theorem derivedResolutionComparison_eq_unit {A : C} {K : CochainComplex C ℕ}
    (ε : (CochainComplex.single₀ C).obj A ⟶ K) [QuasiIso ε] :
    derivedResolutionComparison F ε =
      (DerivedCategory.Plus.QCompιIso D).inv.app
          (F.mapCochainComplexPlus.obj (natPlus K)) ≫
        DerivedCategory.Plus.ι.map
          (F.rightDerivedFunctorPlusUnit.app (natPlus K) ≫
            F.rightDerivedFunctorPlus.map
              (inv (DerivedCategory.Plus.Q.map (natPlusAugmentation ε)) ≫
                (DerivedPlus.singlePlusQIso C).inv.app A)) := by
  set I := injectiveResolution A
  set φ := lift ε (𝟙 A) I.ι
  have hφ : ε ≫ φ = I.ι := comp_lift_id ε _
  let g : natPlus K ⟶ DerivedPlus.resolutionPlus I :=
    ObjectProperty.homMk (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)
  have hcomp : natPlusAugmentation ε ≫ g = DerivedPlus.resolutionPlusι I :=
    natPlusAugmentation_comp_natPlusMap ε I φ hφ
  have hs : DerivedCategory.Plus.Q.map g ≫ (DerivedPlus.singleIsoOfResolution I).inv =
      inv (DerivedCategory.Plus.Q.map (natPlusAugmentation ε)) ≫
        (DerivedPlus.singlePlusQIso C).inv.app A := by
    rw [← cancel_mono (DerivedPlus.singleIsoOfResolution I).hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, DerivedPlus.singleIsoOfResolution_hom_eq,
      Category.assoc, Iso.inv_hom_id_app_assoc, IsIso.eq_inv_comp, ← Functor.map_comp,
      hcomp]
  have hu := F.rightDerivedFunctorPlusUnit.naturality g
  have hq := (DerivedCategory.Plus.QCompιIso D).inv.naturality
    (F.mapCochainComplexPlus.map g)
  simp only [Functor.comp_map] at hu hq
  unfold derivedResolutionComparison derivedComparison derivedResolutionIso
    DerivedPlus.derivedComplexIso
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, asIso_hom, Iso.app_inv]
  change DerivedCategory.Q.map ((CochainComplex.Plus.ι D).map
      (F.mapCochainComplexPlus.map g)) ≫ _ = _
  rw [reassoc_of% hq, ← Functor.map_comp, reassoc_of% hu, ← Functor.map_comp, hs]

section Homology

variable {C' : Type*} [Category* C'] [Abelian C'] {G : C' ⥤ D} [G.Additive]

omit [HasDerivedCategory C] [EnoughInjectives C] in
set_option backward.isDefEq.respectTransparency false in
/-- A map of integer-indexed image complexes which is the extension of a map of
natural-indexed image complexes induces that map on the cohomology
identifications of `derivedResolutionHomologyIso`. -/
@[reassoc]
lemma derivedResolutionHomologyIso_hom_naturality_of_extend
    {K : CochainComplex C ℕ} {L : CochainComplex C' ℕ}
    (u : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶
      (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj L)
    (v : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (K.extend ComplexShape.embeddingUpNat) ⟶
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (L.extend ComplexShape.embeddingUpNat))
    (hv : (DerivedPlus.mapExtendIso F K ComplexShape.embeddingUpNat).hom ≫ v =
      HomologicalComplex.extendMap u ComplexShape.embeddingUpNat ≫
        (DerivedPlus.mapExtendIso G L ComplexShape.embeddingUpNat).hom) (n : ℕ) :
    (DerivedCategory.homologyFunctor D (n : ℤ)).map (DerivedCategory.Q.map v) ≫
        (derivedResolutionHomologyIso G L n).hom =
      (derivedResolutionHomologyIso F K n).hom ≫ HomologicalComplex.homologyMap u n := by
  have h₁ := (DerivedCategory.homologyFunctorFactors D (n : ℤ)).hom.naturality v
  have h₃ := HomologicalComplex.extendHomologyIso_hom_naturality u
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl
  have hv' : v ≫ (DerivedPlus.mapExtendIso G L ComplexShape.embeddingUpNat).inv =
      (DerivedPlus.mapExtendIso F K ComplexShape.embeddingUpNat).inv ≫
        HomologicalComplex.extendMap u ComplexShape.embeddingUpNat := by
    rw [Iso.eq_inv_comp, ← Category.assoc, hv, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h₄ : HomologicalComplex.homologyMap v (n : ℤ) ≫
        HomologicalComplex.homologyMap
          (DerivedPlus.mapExtendIso G L ComplexShape.embeddingUpNat).inv (n : ℤ) =
      HomologicalComplex.homologyMap
          (DerivedPlus.mapExtendIso F K ComplexShape.embeddingUpNat).inv (n : ℤ) ≫
        HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap u ComplexShape.embeddingUpNat) (n : ℤ) := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, hv']
  simp only [Functor.comp_map] at h₁
  simp only [derivedResolutionHomologyIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom]
  erw [reassoc_of% h₁, reassoc_of% h₄, h₃]
  simp only [Category.assoc]
  rfl

end Homology

end Derived

end Langlands.Cohomology.AcyclicResolution

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

universe u

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AcyclicResolution

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)}

/-- The derived form of the resolution description: the canonical derived
comparison of a right resolution on `X`, followed by the coefficient map and the
canonical pushforward comparison, is the map of section complexes induced by
`ψ`, followed by the canonical derived comparison of the resolution on `Y`. -/
theorem derivedResolutionComparison_comp_pushforwardSingle (h : Y ⟶ X)
    {M : X.left.Modules} {N : Y.left.Modules}
    (a : M ⟶ (Scheme.Modules.pushforward h.left).obj N)
    {KX : CochainComplex X.left.Modules ℕ} {KY : CochainComplex Y.left.Modules ℕ}
    (εX : (CochainComplex.single₀ X.left.Modules).obj M ⟶ KX) [QuasiIso εX]
    (εY : (CochainComplex.single₀ Y.left.Modules).obj N ⟶ KY) [QuasiIso εY]
    (ψ : KX ⟶ ((Scheme.Modules.pushforward h.left).mapHomologicalComplex _).obj KY)
    (hψ : εX ≫ ψ = (CochainComplex.single₀ X.left.Modules).map a ≫
      mapResolutionAugmentation (Scheme.Modules.pushforward h.left) εY) :
    derivedResolutionComparison (relativeGlobalSections X.hom) εX ≫
        DerivedCategory.Plus.ι.map
          ((DerivedPlus.derivedComplex (relativeGlobalSections X.hom)).map a ≫
            (pushforwardSingleDerivedSectionsComparison h).app N) =
      DerivedCategory.Q.map ((CochainComplex.Plus.ι (ModuleCat.{u} R)).map
          ((relativeGlobalSections X.hom).mapCochainComplexPlus.map
              (natPlusMapTo (Scheme.Modules.pushforward h.left) ψ) ≫
            (pullbackSectionsComplexIso h (natPlus KY)).hom)) ≫
        derivedResolutionComparison (relativeGlobalSections Y.hom) εY := by
  rw [derivedResolutionComparison_eq_unit, derivedResolutionComparison_eq_unit]
  have hq := (DerivedCategory.Plus.QCompιIso (ModuleCat.{u} R)).inv.naturality
    ((relativeGlobalSections X.hom).mapCochainComplexPlus.map
        (natPlusMapTo (Scheme.Modules.pushforward h.left) ψ) ≫
      (pullbackSectionsComplexIso h (natPlus KY)).hom)
  simp only [Functor.comp_map] at hq
  rw [reassoc_of% hq, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  refine congrArg (fun f => _ ≫ DerivedCategory.Plus.ι.map f) ?_
  have hE := natPlusAugmentation_comp_natPlusMapTo (Scheme.Modules.pushforward h.left)
    εX εY a ψ hψ
  have hs := (DerivedPlus.singlePlusQIso X.left.Modules).hom.naturality a
  simp only [Functor.comp_map] at hs
  have hA : inv (DerivedCategory.Plus.Q.map (natPlusAugmentation εX)) ≫
      (DerivedPlus.singlePlusQIso X.left.Modules).inv.app M ≫
      (DerivedCategory.Plus.singleFunctor X.left.Modules 0).map a ≫
      (DerivedPlus.singlePlusQIso X.left.Modules).hom.app
        ((Scheme.Modules.pushforward h.left).obj N) ≫
      DerivedCategory.Plus.Q.map
        ((DerivedPlus.singlePlusMapIso (Scheme.Modules.pushforward h.left)).hom.app N) ≫
      DerivedCategory.Plus.Q.map ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.map
        (natPlusAugmentation εY)) =
      DerivedCategory.Plus.Q.map (natPlusMapTo (Scheme.Modules.pushforward h.left) ψ) := by
    rw [IsIso.inv_comp_eq, reassoc_of% hs, Iso.inv_hom_id_app_assoc]
    simp only [← Functor.map_comp]
    rw [hE]
  have hβ := (pushforwardDerivedSectionsComparison h).naturality (natPlusAugmentation εY)
  simp only [Functor.comp_map] at hβ
  have hβ' : (relativeGlobalSections X.hom).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map ((Scheme.Modules.pushforward h.left).mapCochainComplexPlus.map
          (natPlusAugmentation εY))) ≫
      (pushforwardDerivedSectionsComparison h).app (natPlus KY) ≫
        (relativeGlobalSections Y.hom).rightDerivedFunctorPlus.map
          (inv (DerivedCategory.Plus.Q.map (natPlusAugmentation εY))) =
      (pushforwardDerivedSectionsComparison h).app
        ((DerivedPlus.singlePlusFunctor Y.left.Modules).obj N) := by
    rw [reassoc_of% hβ, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  have hu := (relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit.naturality
    (natPlusMapTo (Scheme.Modules.pushforward h.left) ψ)
  simp only [Functor.comp_map] at hu
  have hf := pushforwardDerivedSectionsComparison_fac h (natPlus KY)
  symm
  rw [Functor.map_comp, Category.assoc, ← reassoc_of% hf, reassoc_of% hu, ← hA]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hβ']
  simp only [pushforwardSingleDerivedSectionsComparison, DerivedPlus.derivedComplex,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_map]

/-- The bounded below section-complex map of the derived identity is the
integer extension of the natural-indexed section-complex map induced by `ψ`. -/
lemma mapExtendIso_hom_comp_sectionsMap (h : Y ⟶ X)
    {KX : CochainComplex X.left.Modules ℕ} {KY : CochainComplex Y.left.Modules ℕ}
    (ψ : KX ⟶ ((Scheme.Modules.pushforward h.left).mapHomologicalComplex _).obj KY) :
    (DerivedPlus.mapExtendIso (relativeGlobalSections X.hom) KX
        ComplexShape.embeddingUpNat).hom ≫
      (CochainComplex.Plus.ι (ModuleCat.{u} R)).map
        ((relativeGlobalSections X.hom).mapCochainComplexPlus.map
            (natPlusMapTo (Scheme.Modules.pushforward h.left) ψ) ≫
          (pullbackSectionsComplexIso h (natPlus KY)).hom) =
    HomologicalComplex.extendMap
        (((relativeGlobalSections X.hom).mapHomologicalComplex _).map ψ ≫
          ((Functor.mapHomologicalComplexCompIso (relativePushforwardSectionsIso h)
            (ComplexShape.up ℕ)).app KY).hom) ComplexShape.embeddingUpNat ≫
      (DerivedPlus.mapExtendIso (relativeGlobalSections Y.hom) KY
        ComplexShape.embeddingUpNat).hom := by
  have h1 := mapExtendIso_compIso (relativePushforwardSectionsIso h) KY
    ComplexShape.embeddingUpNat
  have h2 := extendMapIso_hom_naturality ComplexShape.embeddingUpNat
    (relativeGlobalSections X.hom) ψ
  simp only [extendMapIso, Iso.symm_hom] at h2
  have h2' : (DerivedPlus.mapExtendIso (relativeGlobalSections X.hom) KX
        ComplexShape.embeddingUpNat).hom ≫
      ((relativeGlobalSections X.hom).mapHomologicalComplex _).map
        (HomologicalComplex.extendMap ψ ComplexShape.embeddingUpNat) =
      HomologicalComplex.extendMap
          (((relativeGlobalSections X.hom).mapHomologicalComplex _).map ψ)
          ComplexShape.embeddingUpNat ≫
        (DerivedPlus.mapExtendIso (relativeGlobalSections X.hom)
          (((Scheme.Modules.pushforward h.left).mapHomologicalComplex _).obj KY)
          ComplexShape.embeddingUpNat).hom := by
    rw [← cancel_mono (DerivedPlus.mapExtendIso (relativeGlobalSections X.hom)
        (((Scheme.Modules.pushforward h.left).mapHomologicalComplex _).obj KY)
        ComplexShape.embeddingUpNat).inv, Category.assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, h2, Iso.hom_inv_id_assoc]
  rw [Functor.map_comp]
  simp only [pullbackSectionsComplexIso, Functor.preimageIso_hom, Functor.map_preimage]
  change _ ≫ ((relativeGlobalSections X.hom).mapHomologicalComplex _).map
      (HomologicalComplex.extendMap ψ ComplexShape.embeddingUpNat ≫
        (DerivedPlus.mapExtendIso (Scheme.Modules.pushforward h.left) KY
          ComplexShape.embeddingUpNat).hom) ≫ _ = _
  rw [HomologicalComplex.extendMap_comp, Category.assoc, h1, Functor.map_comp,
    Category.assoc, reassoc_of% h2']

/-- **Resolution description of the canonical pushforward comparison.** Let
`εX` and `εY` be right resolutions of `M` on `X` and `N` on `Y`, let
`a : M ⟶ h_* N`, and let `ψ : KX ⟶ h_* KY` be compatible with the augmentations
over `a`. Then the comparison map of `εX`, followed by cohomology of `a` and the
canonical pushforward comparison, is the map of section complexes induced by
`ψ`, followed by the comparison map of `εY`. -/
theorem resolutionComparison_comp_canonicalPushforwardCohomologyMap (h : Y ⟶ X)
    {M : X.left.Modules} {N : Y.left.Modules}
    (a : M ⟶ (Scheme.Modules.pushforward h.left).obj N)
    {KX : CochainComplex X.left.Modules ℕ} {KY : CochainComplex Y.left.Modules ℕ}
    (εX : (CochainComplex.single₀ X.left.Modules).obj M ⟶ KX) [QuasiIso εX]
    (εY : (CochainComplex.single₀ Y.left.Modules).obj N ⟶ KY) [QuasiIso εY]
    (ψ : KX ⟶ ((Scheme.Modules.pushforward h.left).mapHomologicalComplex _).obj KY)
    (hψ : εX ≫ ψ = (CochainComplex.single₀ X.left.Modules).map a ≫
      mapResolutionAugmentation (Scheme.Modules.pushforward h.left) εY) (n : ℕ) :
    resolutionComparison (relativeGlobalSections X.hom) εX n ≫
        (relativeCohomology X.hom n).map a ≫ canonicalPushforwardCohomologyMap h N n =
      HomologicalComplex.homologyMap
          (((relativeGlobalSections X.hom).mapHomologicalComplex _).map ψ ≫
            ((Functor.mapHomologicalComplexCompIso (relativePushforwardSectionsIso h)
              (ComplexShape.up ℕ)).app KY).hom) n ≫
        resolutionComparison (relativeGlobalSections Y.hom) εY n := by
  have hS := derivedResolutionComparison_comp_pushforwardSingle h a εX εY ψ hψ
  have hX := derivedResolutionComparison_homology (relativeGlobalSections X.hom) εX n
  have hY := derivedResolutionComparison_homology (relativeGlobalSections Y.hom) εY n
  have hN := DerivedPlus.homologyIso_hom_naturality (relativeGlobalSections X.hom) a
    (injectiveResolution M)
    (injectiveResolution ((Scheme.Modules.pushforward h.left).obj N)) n
  have hH := derivedResolutionHomologyIso_hom_naturality_of_extend
    (relativeGlobalSections X.hom) _ _ (mapExtendIso_hom_comp_sectionsMap h ψ) n
  have key := congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map hS
  simp only [Functor.map_comp] at key
  rw [← cancel_epi (derivedResolutionHomologyIso (relativeGlobalSections X.hom) KX n).hom,
    ← reassoc_of% hX, ← reassoc_of% hH, ← hY]
  unfold canonicalPushforwardCohomologyMap
  dsimp only [relativeCohomology]
  rw [← reassoc_of% hN, Iso.hom_inv_id_assoc]
  change _ ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
      (DerivedCategory.Plus.ι.map _) ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} R)
        (n : ℤ)).map (DerivedCategory.Plus.ι.map _) ≫ _ = _
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% key]

/-- **Resolution description of the canonical cohomology pullback.** If `εX`
resolves `M` on `X`, `εY` resolves `h^* M` on `Y`, and `ψ : KX ⟶ h_* KY` is
compatible with the augmentations over the adjunction unit, then the canonical
cohomology pullback is computed by the map of section complexes induced by
`ψ`. -/
theorem resolutionComparison_comp_relativeCohomologyPullback (h : Y ⟶ X)
    {M : X.left.Modules}
    {KX : CochainComplex X.left.Modules ℕ} {KY : CochainComplex Y.left.Modules ℕ}
    (εX : (CochainComplex.single₀ X.left.Modules).obj M ⟶ KX) [QuasiIso εX]
    (εY : (CochainComplex.single₀ Y.left.Modules).obj
      ((Scheme.Modules.pullback h.left).obj M) ⟶ KY) [QuasiIso εY]
    (ψ : KX ⟶ ((Scheme.Modules.pushforward h.left).mapHomologicalComplex _).obj KY)
    (hψ : εX ≫ ψ = (CochainComplex.single₀ X.left.Modules).map
        ((Scheme.Modules.pullbackPushforwardAdjunction h.left).unit.app M) ≫
      mapResolutionAugmentation (Scheme.Modules.pushforward h.left) εY) (n : ℕ) :
    resolutionComparison (relativeGlobalSections X.hom) εX n ≫
        relativeCohomologyPullback h M n =
      HomologicalComplex.homologyMap
          (((relativeGlobalSections X.hom).mapHomologicalComplex _).map ψ ≫
            ((Functor.mapHomologicalComplexCompIso (relativePushforwardSectionsIso h)
              (ComplexShape.up ℕ)).app KY).hom) n ≫
        resolutionComparison (relativeGlobalSections Y.hom) εY n := by
  rw [relativeCohomologyPullback_eq_unit_pushforward]
  exact resolutionComparison_comp_canonicalPushforwardCohomologyMap h _ εX εY ψ hψ n

/-- The resolution description of the canonical cohomology pullback followed by
a coefficient map `b : h^* M ⟶ N`, with `ψ` compatible over the adjoint of `b`. -/
theorem resolutionComparison_comp_relativeCohomologyPullback_coefficient (h : Y ⟶ X)
    {M : X.left.Modules} {N : Y.left.Modules}
    (b : (Scheme.Modules.pullback h.left).obj M ⟶ N)
    {KX : CochainComplex X.left.Modules ℕ} {KY : CochainComplex Y.left.Modules ℕ}
    (εX : (CochainComplex.single₀ X.left.Modules).obj M ⟶ KX) [QuasiIso εX]
    (εY : (CochainComplex.single₀ Y.left.Modules).obj N ⟶ KY) [QuasiIso εY]
    (ψ : KX ⟶ ((Scheme.Modules.pushforward h.left).mapHomologicalComplex _).obj KY)
    (hψ : εX ≫ ψ = (CochainComplex.single₀ X.left.Modules).map
        ((Scheme.Modules.pullbackPushforwardAdjunction h.left).homEquiv _ _ b) ≫
      mapResolutionAugmentation (Scheme.Modules.pushforward h.left) εY) (n : ℕ) :
    resolutionComparison (relativeGlobalSections X.hom) εX n ≫
        relativeCohomologyPullback h M n ≫ (relativeCohomology Y.hom n).map b =
      HomologicalComplex.homologyMap
          (((relativeGlobalSections X.hom).mapHomologicalComplex _).map ψ ≫
            ((Functor.mapHomologicalComplexCompIso (relativePushforwardSectionsIso h)
              (ComplexShape.up ℕ)).app KY).hom) n ≫
        resolutionComparison (relativeGlobalSections Y.hom) εY n := by
  rw [relativeCohomologyPullback_coefficient]
  exact resolutionComparison_comp_canonicalPushforwardCohomologyMap h _ εX εY ψ hψ n

end Langlands.AlgebraicGeometry.Modules.DerivedSections
