/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Data.ZMod.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.Sites.TorsionSheafConstantModule
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.SixFunctors.CokernelAdjointExchange
import WeilConjectures.CategoryTheory.Normalized.NormalizedScalarBoundaryNaturality
public import WeilConjectures.AlgebraicGeometry.DivisibleExtensionDerivedReduction
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Derived reduction of an extension by a divisible sheaf

Source: the Cartier unit proof, paragraphs 4 and 5, in blueprint main-20261015;
Stacks Tags 06YU, 06YV, 06YY, 0152, 09T5 and 0FND
(blueprint: lem-sfb-divisible-extension-derived-reduction).
Kernel and quotient objects are specified by their short exact sequences, including
existence of their residue-coefficient structures. The normalized identifications are
unique, so the definition of the reduced boundary makes no arbitrary choice of map.
The normalized sheaf scalar adjunction is an item helper; the general internal-module
derived extension of scalars remains the recorded dependency interface.
-/

@[expose] public section
set_option autoImplicit false
universe u v r wZ wR u' v' wZ' wR'
open CategoryTheory CategoryTheory.Limits

section GeneralBoundaryNaturality
variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (res : B ⥤ A) [res.Additive]
  [PreservesFiniteLimits res] [PreservesFiniteColimits res]
  (L : DerivedCategory A ⥤ DerivedCategory B) [L.CommShift ℤ]
  (ad : L ⊣ res.mapDerivedCategory) (n : ℕ)

end GeneralBoundaryNaturality

section AbstractCokernel
set_option backward.isDefEq.respectTransparency false
variable {A₀ B₀ : Type*} [Category A₀] [Category B₀] [Abelian A₀]
  (E : A₀ ⥤ B₀) (R : B₀ ⥤ A₀) [R.Full] [R.Faithful]
  (a : E ⊣ R) (A : A₀) (g : A ⟶ A)
  (hz : g ≫ a.unit.app A = 0) (Q : B₀) (eQ : cokernel g ≅ R.obj Q)
private noncomputable def abstractUnitCokernel :
    IsColimit (CokernelCofork.ofπ (a.unit.app A) hz) := by
  let b := (a.homEquiv A Q).symm (cokernel.π g ≫ eQ.hom)
  have hb : a.unit.app A ≫ R.map b = cokernel.π g ≫ eQ.hom := by
    exact (Adjunction.homEquiv_unit a _ _ b).symm.trans (Equiv.apply_symm_apply _ _)
  let k := cokernel.desc g (a.unit.app A) hz
  let c := R.preimage (eQ.inv ≫ k)
  have hc : R.map c = eQ.inv ≫ k := CategoryTheory.Functor.map_preimage _ _
  have hbc : b ≫ c = 𝟙 _ := by
    apply (a.homEquiv A (E.obj A)).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
    rw [← Category.assoc, hb, hc]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    erw [Category.comp_id]
    exact cokernel.π_desc g (a.unit.app A) hz
  have hcb : c ≫ b = 𝟙 _ := by
    apply R.map_injective
    apply (cancel_epi (cokernel.π g ≫ eQ.hom)).1
    simp only [CategoryTheory.Functor.map_comp, Category.assoc,
      CategoryTheory.Functor.map_id, Category.comp_id]
    rw [hc]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, cokernel.π_desc]
    exact hb
  let eb : E.obj A ≅ Q := ⟨b, c, hbc, hcb⟩
  let e := eQ ≪≫ (R.mapIso eb).symm
  have he : cokernel.π g ≫ e.hom = a.unit.app A := by
    change cokernel.π g ≫ eQ.hom ≫ R.map c = _
    rw [← Category.assoc, ← hb, Category.assoc, ← CategoryTheory.Functor.map_comp, hbc,
      CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
  let ei : CokernelCofork.ofπ (cokernel.π g) (cokernel.condition g) ≅
      CokernelCofork.ofπ (a.unit.app A) hz :=
    Cofork.ext e he
  exact IsColimit.ofIsoColimit (cokernelIsCokernel g) ei

end AbstractCokernel

section UnitTriangle
set_option backward.isDefEq.respectTransparency false
open CategoryTheory.Pretriangulated
variable {A B : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  [Category* B] [Abelian B] [HasDerivedCategory B]
  (E : A ⥤ B) [E.Additive] (R : B ⥤ A) [R.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  (a : E ⊣ R) (L : DerivedCategory A ⥤ DerivedCategory B) (ad : L ⊣ R.mapDerivedCategory)
  (ε : DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (n : ℕ) (P K : CochainComplex A ℤ) (p : P ⟶ K) [QuasiIso p] [IsIso (ε.app P)]
  (hz : (n • 𝟙 P) ≫ (a.mapHomologicalComplex (.up ℤ)).unit.app P = 0)
  (hS : (ShortComplex.mk (n • 𝟙 P) ((a.mapHomologicalComplex (.up ℤ)).unit.app P)
    hz).ShortExact)
  (hnormal : ad.unit.app (DerivedCategory.Q.obj P) ≫ R.mapDerivedCategory.map (ε.app P) ≫
    R.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P))
include p hS hnormal in
private theorem unit_triangle :
    ∃ δ, Triangle.mk (n • 𝟙 (DerivedCategory.Q.obj K))
      (ad.unit.app (DerivedCategory.Q.obj K)) δ ∈ distTriang (DerivedCategory A) := by
  let e₁ : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj K :=
    asIso (DerivedCategory.Q.map p)
  let e₃ : DerivedCategory.Q.obj
      ((R.mapHomologicalComplex (.up ℤ)).obj ((E.mapHomologicalComplex (.up ℤ)).obj P)) ≅
      R.mapDerivedCategory.obj (L.obj (DerivedCategory.Q.obj K)) :=
    (R.mapDerivedCategoryFactors.app ((E.mapHomologicalComplex (.up ℤ)).obj P)).symm ≪≫
      R.mapDerivedCategory.mapIso (asIso (ε.app P)).symm ≪≫
      R.mapDerivedCategory.mapIso (L.mapIso e₁)
  let T := DerivedCategory.triangleOfSES hS
  let δ := e₃.inv ≫ T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧'
  let T' := Triangle.mk (n • 𝟙 (DerivedCategory.Q.obj K))
    (ad.unit.app (DerivedCategory.Q.obj K)) δ
  have he₂ : T.mor₂ ≫ e₃.hom = e₁.hom ≫ ad.unit.app (DerivedCategory.Q.obj K) := by
    have hnat := ad.unit.naturality e₁.hom
    change DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      R.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
      R.mapDerivedCategory.map (inv (ε.app P)) ≫
      R.mapDerivedCategory.map (L.map e₁.hom) = _
    erw [← hnormal]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← R.mapDerivedCategory.map_comp_assoc, IsIso.hom_inv_id]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact hnat.symm
  let eT : T ≅ T' := Triangle.isoMk T T' e₁ e₁ e₃ (by
    change DerivedCategory.Q.map (n • 𝟙 P) ≫ e₁.hom = e₁.hom ≫ (n • 𝟙 _)
    rw [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id]
    simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
      Category.id_comp, Category.comp_id]) he₂ (by
    change T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧' =
      e₃.hom ≫ e₃.inv ≫ T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧'
    simp only [Iso.hom_inv_id_assoc])
  exact ⟨δ, isomorphic_distinguished T (DerivedCategory.triangleOfSES_distinguished hS)
    T' eT.symm⟩
end UnitTriangle

section Generic
universe a b c d e f
set_option backward.isDefEq.respectTransparency false
variable {A : Type a} [Category.{b} A] [Abelian A] [HasDerivedCategory.{c} A]
  {B : Type d} [Category.{e} B] [Abelian B] [HasDerivedCategory.{f} B]
  (R : B ⥤ A) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [R.Full] [R.Faithful]

omit [R.Faithful] in
private theorem pure_lift (n : ℤ) (X Y : DerivedCategory B)
    [X.IsGE n] [X.IsLE n] [Y.IsGE n] [Y.IsLE n]
    (t : R.mapDerivedCategory.obj X ⟶ R.mapDerivedCategory.obj Y) :
    ∃ u : X ⟶ Y, R.mapDerivedCategory.map u = t := by
  classical
  obtain ⟨M, ⟨eX⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  obtain ⟨N, ⟨eY⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE Y n
  let c := R.mapDerivedCategorySingleFunctor n
  let eX' := R.mapDerivedCategory.mapIso eX ≪≫ c.app M
  let eY' := R.mapDerivedCategory.mapIso eY ≪≫ c.app N
  let f := (DerivedCategory.singleFunctor A n).preimage (eX'.inv ≫ t ≫ eY'.hom)
  let g := R.preimage f
  refine ⟨eX.hom ≫ (DerivedCategory.singleFunctor B n).map g ≫ eY.inv, ?_⟩
  have hf : (DerivedCategory.singleFunctor A n).map (R.map g) =
      eX'.inv ≫ t ≫ eY'.hom := by
    rw [R.map_preimage]
    exact (DerivedCategory.singleFunctor A n).map_preimage _
  simp only [Functor.map_comp]
  have hnat := c.hom.naturality g
  change R.mapDerivedCategory.map ((DerivedCategory.singleFunctor B n).map g) ≫
      c.hom.app N = c.hom.app M ≫
        (DerivedCategory.singleFunctor A n).map (R.map g) at hnat
  apply (cancel_mono (R.mapDerivedCategory.map eY.hom ≫ c.hom.app N)).1
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [hnat, hf]
  simp [eX', eY', Category.assoc]

omit [R.Full] [R.Faithful] in
private theorem reflect_derived_iso [R.ReflectsIsomorphisms] :
    R.mapDerivedCategory.ReflectsIsomorphisms := by
  refine ⟨fun g _ ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso (R.map ((DerivedCategory.homologyFunctor _ n).map g)) :=
    (NatIso.isIso_map_iff (R.mapDerivedCategoryHomologyFunctorIso n) g).2
      (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ R

private theorem normalized_pure_iso (L : DerivedCategory A ⥤ DerivedCategory B)
    (a : L ⊣ R.mapDerivedCategory) (n : ℤ) (X : DerivedCategory A) (Y : DerivedCategory B)
    [Y.IsGE n] [Y.IsLE n]
    (f : X ⟶ R.mapDerivedCategory.obj Y)
    (e : R.mapDerivedCategory.obj (L.obj X) ≅ R.mapDerivedCategory.obj Y)
    (he : a.unit.app X ≫ e.hom = f) :
    ∃! u : L.obj X ≅ Y, a.unit.app X ≫ R.mapDerivedCategory.map u.hom = f := by
  have : (R.mapDerivedCategory.obj Y).IsGE n := R.isGE_mapDerivedCategory_obj Y n
  have : (R.mapDerivedCategory.obj Y).IsLE n := R.isLE_mapDerivedCategory_obj Y n
  have hge : (R.mapDerivedCategory.obj (L.obj X)).IsGE n :=
    DerivedCategory.TStructure.t.isGE_of_iso e.symm n
  have hle : (R.mapDerivedCategory.obj (L.obj X)).IsLE n :=
    DerivedCategory.TStructure.t.isLE_of_iso e.symm n
  obtain ⟨hge', hle'⟩ :=
    R.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj ⟨hge, hle⟩
  let := hge'
  let := hle'
  obtain ⟨u, hu⟩ := pure_lift R n (L.obj X) Y e.hom
  have : R.ReflectsIsomorphisms := by infer_instance
  have : R.mapDerivedCategory.ReflectsIsomorphisms := reflect_derived_iso R
  have : IsIso (R.mapDerivedCategory.map u) := by rw [hu]; infer_instance
  have : IsIso u := isIso_of_reflects_iso u R.mapDerivedCategory
  refine ⟨asIso u, ?_, ?_⟩
  · simpa only [asIso_hom, hu] using he
  · intro u' hu'
    apply Iso.ext
    apply (a.homEquiv X Y).injective
    simp only [Adjunction.homEquiv_unit]
    exact hu'.trans (by simpa only [asIso_hom, hu] using he.symm)

end Generic

section DerivedSingle
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  (E : A ⥤ B) [E.Additive] (R : B ⥤ A) [R.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : E ⊣ R)
  (L : DerivedCategory A ⥤ DerivedCategory B) (ad : L ⊣ R.mapDerivedCategory)
  (ε : DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (X : A) (Y : B) (b : E.obj X ⟶ Y) [IsIso b] (f : X ⟶ R.obj Y)
  (hb : a.unit.app X ≫ R.map b = f)
  (hε : IsIso (ε.app ((HomologicalComplex.single A (.up ℤ) 0).obj X)))
  (hu : ad.unit.app ((DerivedCategory.singleFunctor A 0).obj X) ≫
    R.mapDerivedCategory.map (ε.app ((HomologicalComplex.single A (.up ℤ) 0).obj X)) ≫
      R.mapDerivedCategoryFactors.hom.app
        ((E.mapHomologicalComplex (.up ℤ)).obj
          ((HomologicalComplex.single A (.up ℤ) 0).obj X)) =
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app
      ((HomologicalComplex.single A (.up ℤ) 0).obj X)))
end DerivedSingle

section ShiftedComposition
variable {A : Type*} [Category* A] [HasShift A ℤ] {X Y Z : A}
end ShiftedComposition

section ShiftedAdjunct
set_option backward.isDefEq.respectTransparency false
variable {A B : Type*} [Category* A] [Category* B]
  [HasShift A ℤ] [HasShift B ℤ] (L : A ⥤ B) (R : B ⥤ A)
  [L.CommShift ℤ] [R.CommShift ℤ] (ad : L ⊣ R) [ad.CommShift ℤ]
  {X Y : A} {H : B} (f : X ⟶ Y⟦(1 : ℤ)⟧)
  (a : L.obj Y ⟶ H⟦(1 : ℤ)⟧) (k : Y ⟶ R.obj (H⟦(1 : ℤ)⟧))
  (ha : ad.unit.app Y ≫ R.map a = k)
end ShiftedAdjunct

namespace SheafOfModules

section UnitKFlat
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  (R : Sheaf J CommRingCat.{r})
private theorem unit_kflat : CochainComplex.IsKFlatIndependentCoefficients (R := R)
    ((HomologicalComplex.single _ (.up ℤ) 0).obj
      (unit (derivedChangeRingIndependentCoefficients J R))) := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro F hF
  exact hF.of_iso (HomologicalComplex.rightUnitor F).symm
end UnitKFlat

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {Z R : Sheaf J CommRingCat.{r}} (q : Z ⟶ R)

omit [EssentiallySmall.{r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] in
private theorem scalarForget_preservesFiniteColimits (A : Sheaf J RingCat.{r}) :
    PreservesFiniteColimits (toSheaf.{r} A) := by
  constructor
  intro K _ _
  constructor
  intro F
  let L := PresheafOfModules.sheafification.{r} (𝟙 A.obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{r} (𝟙 A.obj)
  let G := F ⋙ (SheafOfModules.forget A ⋙ PresheafOfModules.restrictScalars (𝟙 A.obj))
  let e : G ⋙ L ≅ F := Functor.isoWhiskerLeft F (asIso adj.counit) ≪≫ F.rightUnitor
  have : PreservesColimitsOfShape K (presheafToSheaf J AddCommGrpCat.{r}) :=
    (sheafificationAdjunction J AddCommGrpCat.{r}).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have : PreservesColimit G (L ⋙ toSheaf.{r} A) :=
    preservesColimit_of_natIso G (PresheafOfModules.sheafificationCompToSheaf (𝟙 A.obj)).symm
  let hc := colimit.isColimit G
  have : PreservesColimit (G ⋙ L) (toSheaf.{r} A) :=
    preservesColimit_of_preserves_colimit_cocone (isColimitOfPreserves L hc)
      (isColimitOfPreserves (L ⋙ toSheaf.{r} A) hc)
  exact preservesColimit_of_iso_diagram (toSheaf.{r} A) e

set_option linter.unusedSectionVars false in
private noncomputable abbrev sr {D : Type u} [Category.{v} D] (K : GrothendieckTopology D)
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (A : Sheaf K CommRingCat.{r}) := derivedChangeRingIndependentCoefficients K A

private noncomputable abbrev scalarRes
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) :=
  restrictScalars.{r} ((sheafCompose K (forget₂ CommRingCat RingCat)).map c)

open scoped ChangeOfRings
set_option backward.isDefEq.respectTransparency false

private local instance tensorRestrictionTargetModule
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    {A : Sheaf K CommRingCat.{r}} (M : SheafOfModules.{r} (sr K A))
    {X Y : Dᵒᵖ} (i : X ⟶ Y) :
    Module (A.obj.obj Y)
      ((ModuleCat.restrictScalars ((sr K A).obj.map i).hom).obj (M.val.obj Y)) :=
  inferInstanceAs (Module (A.obj.obj Y) (M.val.obj Y))

private theorem tensorRestriction_tmul
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) (M : SheafOfModules.{r} (sr K A))
    {X Y : Dᵒᵖ} (i : X ⟶ Y) (s : S.obj.obj X) (m : M.val.obj X) :
    (changeOfRingsPresheaf.{v, u, r} c M).map i (s ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m) =
      S.obj.map i s ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom] M.val.map i m :=
  Classical.choose_spec (exists_changeOfRingsMap.{v, u, r} c M i) s m

private noncomputable def tensorPresheafFunctor
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) :
    SheafOfModules.{r} (sr K A) ⥤ PresheafOfModules.{r} (sr K S).obj where
  obj M := changeOfRingsPresheaf.{v, u, r} c M
  map {M N} f :=
    show changeOfRingsPresheaf.{v, u, r} c M ⟶
      changeOfRingsPresheaf.{v, u, r} c N from
    { app := fun W ↦ (ModuleCat.extendScalars (c.hom.app W).hom).map (f.val.app W)
      naturality := changeOfRingsHom_naturality.{v, u, r} c _ f }
  map_id M := by
    ext W : 1
    change (ModuleCat.extendScalars (c.hom.app W).hom).map (𝟙 _) = _
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_id _
  map_comp f g := by
    ext W : 1
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_comp _ _

private noncomputable def tensorFunctor
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) :
    SheafOfModules.{r} (sr K A) ⥤ SheafOfModules.{r} (sr K S) :=
  tensorPresheafFunctor c ⋙ PresheafOfModules.sheafification (𝟙 (sr K S).obj)

private noncomputable def tensorToRestriction
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (sr K A)) (H : SheafOfModules.{r} (sr K S))
    (f : changeOfRingsPresheaf.{v, u, r} c M ⟶ H.val) : M ⟶ (scalarRes c).obj H where
  val :=
    { app := fun W ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
        (c.hom.app W).hom (f.app W)
      naturality := by
        intro X Y i
        ext m
        change f.app Y ((1 : S.obj.obj Y) ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom]
          M.val.map i m) = H.val.map i (f.app X
            ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
        have h := PresheafOfModules.naturality_apply f i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)
        rw [tensorRestriction_tmul, map_one] at h
        exact h }

private noncomputable def restrictionToTensor
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (sr K A)) (H : SheafOfModules.{r} (sr K S))
    (g : M ⟶ (scalarRes c).obj H) : changeOfRingsPresheaf.{v, u, r} c M ⟶ H.val where
  app W := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (c.hom.app W).hom (g.val.app W)
  naturality := by
    intro X Y i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have h := PresheafOfModules.naturality_apply g.val i m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (c.hom.app Y).hom (g.val.app Y)
        ((changeOfRingsPresheaf.{v, u, r} c M).map i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)) =
      H.val.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        (c.hom.app X).hom (g.val.app X)
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
    rw [tensorRestriction_tmul, map_one]
    have atOne (W : Dᵒᵖ) (n : M.val.obj W) :
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
          (c.hom.app W).hom (g.val.app W)
            ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n) = g.val.app W n := by
      exact congrArg (fun f : M.val.obj W ⟶
        (ModuleCat.restrictScalars (c.hom.app W).hom).obj (H.val.obj W) ↦ f n)
        ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
          (g.val.app W))
    rw [atOne, atOne]
    exact h

private noncomputable def tensorPresheafHomEquiv
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (sr K A)) (H : SheafOfModules.{r} (sr K S)) :
    (changeOfRingsPresheaf.{v, u, r} c M ⟶ H.val) ≃ (M ⟶ (scalarRes c).obj H) where
  toFun := tensorToRestriction c M H
  invFun := restrictionToTensor c M H
  left_inv f := by
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).symm_apply_apply
      (f.app W)
  right_inv g := by
    apply SheafOfModules.hom_ext
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
      (g.val.app W)

private noncomputable def tensorHomEquiv
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (sr K A)) (H : SheafOfModules.{r} (sr K S)) :
    ((tensorFunctor c).obj M ⟶ H) ≃ (M ⟶ (scalarRes c).obj H) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (sr K S).obj)).homEquiv _ _).trans
    (tensorPresheafHomEquiv c M H)

private theorem tensorHomEquiv_naturality_left
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    {M N : SheafOfModules.{r} (sr K A)} (a : M ⟶ N)
    (H : SheafOfModules.{r} (sr K S)) (f : (tensorFunctor c).obj N ⟶ H) :
    tensorHomEquiv c M H ((tensorFunctor c).map a ≫ f) =
      a ≫ tensorHomEquiv c N H f := by
  change tensorPresheafHomEquiv c M H
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (sr K S).obj)).homEquiv _ _
        ((PresheafOfModules.sheafification (𝟙 (sr K S).obj)).map
          ((tensorPresheafFunctor c).map a) ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  ext W m
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 (sr K S).obj)).homEquiv
    (changeOfRingsPresheaf.{v, u, r} c N) H f).app W
      ((ModuleCat.extendScalars (c.hom.app W).hom).map (a.val.app W)
        ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  rfl

private theorem tensorHomEquiv_naturality_right
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (sr K A))
    {H H' : SheafOfModules.{r} (sr K S)}
    (f : (tensorFunctor c).obj M ⟶ H) (b : H ⟶ H') :
    tensorHomEquiv c M H' (f ≫ b) =
      tensorHomEquiv c M H f ≫ (scalarRes c).map b := by
  change tensorPresheafHomEquiv c M H'
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (sr K S).obj)).homEquiv _ _
        (f ≫ b)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private noncomputable def tensorAdjunction
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) : tensorFunctor c ⊣
      scalarRes c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv c
      homEquiv_naturality_left_symm := by
        intro M N H a g
        apply (tensorHomEquiv c M H).injective
        rw [Equiv.apply_symm_apply, tensorHomEquiv_naturality_left,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f b ↦ tensorHomEquiv_naturality_right c _ f b }

private theorem tensorAdjunction_homEquiv
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (sr K A)) (H : SheafOfModules.{r} (sr K S)) :
    (tensorAdjunction c).homEquiv M H = tensorHomEquiv c M H := by
  unfold tensorAdjunction
  rw [Adjunction.mkOfHomEquiv_homEquiv]

attribute [irreducible] tensorAdjunction

private theorem initial_of_full_essSurj
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B) [F.Full] [F.EssSurj] :
    F.Initial := by
  classical
  constructor
  intro Y
  let e := F.objObjPreimageIso Y
  let Z : CostructuredArrow F Y := CostructuredArrow.mk e.hom
  have lift (X : CostructuredArrow F Y) : Nonempty (X ⟶ Z) := by
    refine ⟨CostructuredArrow.homMk (F.preimage (X.hom ≫ e.inv)) ?_⟩
    simp [Z, e]
  let : Nonempty (CostructuredArrow F Y) := ⟨Z⟩
  apply zigzag_isConnected
  intro X X'
  exact (Zigzag.of_hom (lift X).some).trans (Zigzag.of_inv (lift X').some)

-- The induced functor on structured arrows is also full and essentially
-- surjective, so restricting the defining limit cone preserves its limit.
private noncomputable def pointwise_precomp_full
    {A C D H : Type*} [Category A] [Category C] [Category D] [Category H]
    (P : A ⥤ C) [P.Full] [P.EssSurj] (Q : C ⥤ D) (F : C ⥤ H) (L : D ⥤ H)
    (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      ((Functor.associator P Q L).hom ≫ Functor.whiskerLeft P α)).IsPointwiseRightKanExtension := by
  intro Y
  let p := StructuredArrow.pre Y P Q
  let : p.Initial := initial_of_full_essSurj p
  apply Limits.IsLimit.ofIsoLimit ((Functor.Initial.isLimitWhiskerEquiv p _).symm (h Y))
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, p]
  simp

-- Transport the defining limit cone through an equivalence of structured
-- arrow categories and the prescribed isomorphism of diagram functors.
private noncomputable def pointwise_change_iso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {Q Q' : C ⥤ D} {F F' : C ⥤ H} (L : D ⥤ H)
    (i : Q ≅ Q') (j : F ≅ F') (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      (Functor.whiskerRight i.inv L ≫ α ≫ j.hom)).IsPointwiseRightKanExtension := by
  intro Y
  let Φ : StructuredArrow Y Q' ≌ StructuredArrow Y Q := Comma.mapRightIso _ i.symm
  let k : Φ.functor ⋙ StructuredArrow.proj Y Q ⋙ F ≅
      StructuredArrow.proj Y Q' ⋙ F' :=
    NatIso.ofComponents (fun X ↦ j.app X.right) (by
      intro X X' f
      exact j.hom.naturality f.right)
  apply Limits.IsLimit.ofIsoLimit
    ((Limits.IsLimit.postcomposeHomEquiv k _).symm ((h Y).whiskerEquivalence Φ))
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, Φ, k]
  simp [Category.assoc]

-- Bound unfolding while checking the denominator cone.
private theorem exactRestriction_denominator_constancy
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : HomotopyCategory A (.up ℤ)) :
    ∃ X : DerivedCategory B, IsEssentiallyConstantIndDiagram
      (MorphismProperty.Under.forget (HomotopyCategory.quasiIso A (.up ℤ)) ⊤ K ⋙
        Under.forget K ⋙ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) X := by
  classical
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  let G := F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let H := MorphismProperty.Under.forget W ⊤ K ⋙ Under.forget K ⋙ G
  have hG {X Y : HomotopyCategory A (.up ℤ)} (f : X ⟶ Y) (hf : W f) :
      IsIso (G.map f) := by
    have := Localization.inverts DerivedCategory.Qh W f hf
    let e := F.mapDerivedCategoryFactorsh
    change IsIso ((F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map f)
    rw [← NatIso.naturality_2 e.symm f]
    dsimp
    infer_instance
  let z : W.Under ⊤ K := MorphismProperty.Under.mk ⊤ (𝟙 K) (W.id_mem K)
  let p : H ⟶ (Functor.const _).obj (G.obj K) :=
    { app := fun j ↦ by
        have := hG j.hom j.prop
        exact inv (G.map j.hom)
      naturality := by
        intro i j f
        have := hG i.hom i.prop
        have := hG j.hom j.prop
        change G.map f.right ≫ inv (G.map j.hom) = inv (G.map i.hom) ≫ 𝟙 _
        rw [Category.comp_id]
        apply (cancel_epi (G.map i.hom)).1
        rw [← Category.assoc, ← G.map_comp, MorphismProperty.Under.w f]
        simp }
  have hfiltered : IsFiltered (W.Under ⊤ K) := by
    refine { nonempty := ⟨z⟩, cocone_objs := ?_, cocone_maps := ?_ }
    · intro i j
      obtain ⟨t, ht⟩ :=
        (MorphismProperty.RightFraction.mk i.hom i.prop j.hom).exists_leftFraction
      let k : W.Under ⊤ K := MorphismProperty.Under.mk ⊤
        (j.hom ≫ t.s) (W.comp_mem _ _ j.prop t.hs)
      exact ⟨k, MorphismProperty.Under.homMk t.f ht.symm,
        MorphismProperty.Under.homMk t.s, trivial⟩
    · intro i j f g
      obtain ⟨T, t, ht, hfg⟩ := MorphismProperty.HasLeftCalculusOfFractions.ext
        f.right g.right i.hom i.prop (f.w.symm.trans g.w)
      let k : W.Under ⊤ K := MorphismProperty.Under.mk ⊤
        (j.hom ≫ t) (W.comp_mem _ _ j.prop ht)
      exact ⟨k, MorphismProperty.Under.homMk t,
        MorphismProperty.Under.Hom.ext hfg⟩
  refine ⟨G.obj K, hfiltered, p, z, 𝟙 _, ?_, ?_⟩
  · simp [p, z]
  · intro j
    let f : z ⟶ j := MorphismProperty.Under.homMk j.hom (by simp [z])
    have := hG j.hom j.prop
    refine ⟨j, f, 𝟙 j, ?_⟩
    change G.map (𝟙 j.right) = inv (G.map j.hom) ≫ 𝟙 _ ≫ G.map j.hom
    simp

private theorem quotient_homotopy_iso_hom
    (A : Type*) [Category* A] [Abelian A] [HasDerivedCategory A]
    (K : CochainComplex A ℤ) :
    (DerivedCategory.quotientCompQhIso A).hom.app K = 𝟙 _ := rfl

private theorem map_homotopy_iso_hom
    {A : Type*} [Category* A] [Abelian A]
    {B : Type*} [Category* B] [Abelian B] (F : A ⥤ B) [F.Additive]
    (K : CochainComplex A ℤ) :
    (F.mapHomotopyCategoryFactors (.up ℤ)).hom.app K = 𝟙 _ := rfl

private theorem map_derived_factorsh_component
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex A ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient A (.up ℤ)).obj K) =
      F.mapDerivedCategoryFactors.hom.app K := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  change F.mapDerivedCategory.map (𝟙 (DerivedCategory.Q.obj K)) ≫
    F.mapDerivedCategoryFactors.hom.app K ≫ 𝟙 _ ≫
      DerivedCategory.Qh.map (𝟙 ((HomotopyCategory.quotient B (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj K))) = _
  erw [F.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id]
  erw [Category.id_comp, Category.comp_id, Category.comp_id]

private theorem derived_unit_from_compatibility
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    (E : A ⥤ B) [E.Additive] (R : B ⥤ A) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : E ⊣ R)
    (L : DerivedCategory A ⥤ DerivedCategory B) (ad : L ⊣ R.mapDerivedCategory)
    (α : DerivedCategory.Qh ⋙ L ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hc : ∀ (M : HomotopyCategory A (.up ℤ)) (N : HomotopyCategory B (.up ℤ))
      (f : (E.mapHomotopyCategory (.up ℤ)).obj M ⟶ N),
      ad.homEquiv _ _ (α.app M ≫ DerivedCategory.Qh.map f) =
        DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).homEquiv _ _ f) ≫
          R.mapDerivedCategoryFactorsh.inv.app N)
    (M : HomotopyCategory A (.up ℤ)) :
    ad.unit.app (DerivedCategory.Qh.obj M) ≫ R.mapDerivedCategory.map (α.app M) ≫
      R.mapDerivedCategoryFactorsh.hom.app ((E.mapHomotopyCategory (.up ℤ)).obj M) =
        DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app M) := by
  have hh := hc M ((E.mapHomotopyCategory (.up ℤ)).obj M) (𝟙 _)
  erw [DerivedCategory.Qh.map_id, Category.comp_id, Adjunction.homEquiv_unit,
    Adjunction.homEquiv_id] at hh
  have h := congrArg (fun f ↦ f ≫ R.mapDerivedCategoryFactorsh.hom.app
    ((E.mapHomotopyCategory (.up ℤ)).obj M)) hh
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h
  exact h

set_option backward.isDefEq.respectTransparency true in
private theorem resolving_derived_adjunction
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (E : A ⥤ B) [E.Additive] (res : B ⥤ A) [res.Additive]
    [PreservesFiniteLimits res] [PreservesFiniteColimits res] (a : E ⊣ res)
    (H : CochainComplex A ℤ → Prop)
    (hresolve : ∀ K, ∃ (P : CochainComplex A ℤ) (p : P ⟶ K), H P ∧ QuasiIso p)
    (hpres : ∀ {P Q : CochainComplex A ℤ} (f : P ⟶ Q),
      H P → H Q → QuasiIso f → QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map f))
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (huniv : L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ))) :
    ∃ ad : L ⊣ res.mapDerivedCategory, ∀ K : CochainComplex A ℤ,
      ad.unit.app (DerivedCategory.Q.obj K) ≫ res.mapDerivedCategory.map (ε.app K) ≫
        res.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) := by
  let F := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := B)
  let P : Set (HomotopyCategory A (.up ℤ)) := fun X ↦
    ∃ K : CochainComplex A ℤ,
      H K ∧
        (HomotopyCategory.quotient A (.up ℤ)).obj K = X
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (X' : HomotopyCategory A (.up ℤ)) (s : X' ⟶ X),
        X' ∈ P ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨L, f, hL, hf⟩ := hresolve K
    exact ⟨_, (HomotopyCategory.quotient A (.up ℤ)).map f, ⟨L, hL, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf⟩
  have hinv : ∀ (X X' : HomotopyCategory A (.up ℤ)) (s : X ⟶ X'),
      X ∈ P → X' ∈ P → HomotopyCategory.quasiIso A (.up ℤ) s →
        IsIso (F.map s) := by
    rintro X X' s ⟨K, hK, rfl⟩ ⟨L, hL, rfl⟩ hs
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective s
    have hf := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).1 hs
    have hg := hpres f hK hL hf
    exact Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso B (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hg)
  obtain ⟨hpw, LF, α, hLF, _, _⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory B) F P hres hinv
  have hL (M : HomotopyCategory A (.up ℤ)) :
      ∃ X : DerivedCategory B, IsEssentiallyConstantProDiagram
        (MorphismProperty.Over.forget (HomotopyCategory.quasiIso A (.up ℤ)) ⊤ M ⋙
          Over.forget M ⋙ F) X := by
    obtain ⟨X, _, hX, _⟩ := Functor.resolvingClass_essentialConstancy
      (HomotopyCategory.quasiIso A (.up ℤ)) F P hres hinv M
    exact ⟨X, hX⟩
  have hRF := Functor.isRightDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso B (.up ℤ)) res.mapDerivedCategory
    res.mapDerivedCategoryFactorsh
  obtain ⟨ad, had⟩ := exists_derived_adjunction_compatibility res E a
    (exactRestriction_denominator_constancy res) hL res.mapDerivedCategory LF
    res.mapDerivedCategoryFactorsh.inv α hRF hLF
  let qA := HomotopyCategory.quotient A (.up ℤ)
  let i := DerivedCategory.quotientCompQhIso A
  let j : qA ⋙ F ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  let αc := Functor.whiskerRight i.inv LF ≫
    ((Functor.associator qA DerivedCategory.Qh LF).hom ≫ Functor.whiskerLeft qA α) ≫
      j.hom
  let := hpw
  let := hLF
  have hα := pointwise_precomp_full qA DerivedCategory.Qh F LF α
    (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor LF α
      (HomotopyCategory.quasiIso A (.up ℤ)))
  have hαc := pointwise_change_iso LF i j _ hα
  let : LF.IsLeftDerivedFunctor αc (HomologicalComplex.quasiIso A (.up ℤ)) :=
    ⟨hαc.isRightKanExtension⟩
  let := huniv
  let l : LF ≅ L := Functor.leftDerivedUnique L LF αc ε
    (HomologicalComplex.quasiIso A (.up ℤ))
  have hcomp (K : CochainComplex A ℤ) :
      l.hom.app (DerivedCategory.Q.obj K) ≫ ε.app K = αc.app K := by
    simp only [l, Functor.leftDerivedNatIso,
      Functor.leftDerivedNatTrans_app, Iso.refl_hom, NatTrans.id_app, Category.comp_id]
  clear_value l
  refine ⟨ad.ofNatIsoLeft l, ?_⟩
  intro K
  have hηh := derived_unit_from_compatibility E res a LF ad α had
  simp only [Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app, Functor.whiskerRight_app,
    Category.assoc]
  rw [← res.mapDerivedCategory.map_comp_assoc, hcomp]
  change ad.unit.app (DerivedCategory.Q.obj K) ≫ res.mapDerivedCategory.map (αc.app K) ≫
    res.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj K) = _
  have hi : i.inv.app K = 𝟙 _ := rfl
  have hj : j.hom.app K = 𝟙 _ := by
    simp only [j, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      map_homotopy_iso_hom, quotient_homotopy_iso_hom,
      ]
    erw [DerivedCategory.Qh.map_id]
    repeat' erw [Category.id_comp]
    rfl
  have hαcK : αc.app K = α.app (qA.obj K) := by
    simp only [αc, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, hi, hj]
    change LF.map (𝟙 _) ≫ (𝟙 _ ≫ α.app (qA.obj K)) ≫ 𝟙 _ = _
    rw [LF.map_id]
    simp only [Category.id_comp, Category.comp_id]
  rw [hαcK]
  have hh := hηh (qA.obj K)
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient] at hh
  have hfac := map_derived_factorsh_component res
    ((E.mapHomologicalComplex (.up ℤ)).obj K)
  erw [hfac] at hh
  exact hh

variable [HasDerivedCategory.{wZ} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J Z))]
  [HasDerivedCategory.{wR} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J R))]
  (D : DerivedChangeOfRingsCochainModel q)

private theorem ordinary_scalar_adjunction_exists :
    ∃ a : D.E ⊣ restrictScalars.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map q),
      (∀ (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J Z))
        (U : Cᵒᵖ) (x : M.val.obj U),
        (a.unit.app M).val.app U x =
          (eqToHom (D.obj_eq M).symm).val.app U
            (((PresheafOfModules.sheafificationAdjunction
              (𝟙 (derivedChangeRingIndependentCoefficients J R).obj)).unit.app
                (changeOfRingsPresheaf q M)).app U
                  ((ModuleCat.extendRestrictScalarsAdj (q.hom.app U).hom).unit.app
                    (M.val.obj U) x))) := by
  classical
  let e : D.E ≅ tensorFunctor q := NatIso.ofComponents
    (fun M ↦ eqToIso (D.obj_eq M)) (by
      intro M N f
      change D.E.map f ≫ eqToHom (D.obj_eq N) =
        eqToHom (D.obj_eq M) ≫ changeOfRingsHom q M f
      rw [D.map_eq]
      simp)
  let a := (tensorAdjunction q).ofNatIsoLeft e.symm
  refine ⟨a, ?_⟩
  · intro M U x
    rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoLeft_apply,
      tensorAdjunction_homEquiv]
    change (tensorHomEquiv q M (D.E.obj M) (e.inv.app M ≫ 𝟙 _)).val.app U x = _
    simp only [Category.comp_id]
    rfl

-- Keep normalization comparisons from unfolding the sheafification implementation.
set_option backward.isDefEq.respectTransparency true in
/-- The canonical shift comparison, induced from exact restriction by the normalized
adjunction. This fixes compatibility with its unit, instead of choosing an unrelated
triangulated shift structure. Source: Stacks 06YY and 09T5
(blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable instance sheafScalarModelCommShift : D.T.CommShift ℤ :=
  (sheafScalarDerivedAdjunction q D).leftAdjointCommShift ℤ

private theorem scalar_derived_unit
    (P : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J Z)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := Z) P) :
    (sheafScalarDerivedAdjunction q D).unit.app (DerivedCategory.Q.obj P) ≫
      (scalarRes q).mapDerivedCategory.map (D.ε.app P) ≫
      (scalarRes q).mapDerivedCategoryFactors.hom.app
        ((D.E.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        (((sheafScalarOrdinaryAdjunction q D).mapHomologicalComplex (.up ℤ)).unit.app P) :=
  Classical.choose_spec (Classical.choose_spec
    (sheafDerivedScalarAdjunction_exists q D)).2 P hP

set_option backward.isDefEq.respectTransparency true

end SheafOfModules

namespace SheafOfModules
namespace DivisibleReduction

attribute [local irreducible] sheafScalarOrdinaryAdjunction sheafScalarDerivedAdjunction

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

variable {J} (n : ℕ)

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] coefficientUnit

section PresentationConstruction

open CategoryTheory.Functor

private instance ringLocallyBijective : J.WEqualsLocallyBijective CommRingCat.{r} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, r, u, r+1, r, r, r} J

private noncomputable def ringUnit (A : CommRingCat.{r}) :
    (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        ((constantSheaf J CommRingCat).obj A)).obj :=
  whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj A)) (forget₂ CommRingCat RingCat)

private instance ringUnit_ls (A : CommRingCat.{r}) :
    Presheaf.IsLocallySurjective J (ringUnit (J := J) A) :=
  ⟨fun x ↦ Presheaf.imageSieve_mem J
    (toSheafify J ((Functor.const Cᵒᵖ).obj A)) x⟩

private instance ringUnit_li (A : CommRingCat.{r}) :
    Presheaf.IsLocallyInjective J (ringUnit (J := J) A) :=
  ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J
    (toSheafify J ((Functor.const Cᵒᵖ).obj A)) x y h⟩

private instance integerForget_full :
    (toSheaf (derivedChangeRingIndependentCoefficients J (integers J))).Full where
  map_surjective {M N} f := by
    let α := ringUnit (J := J) (CommRingCat.of (ULift.{r} ℤ))
    let g : (PresheafOfModules.restrictScalars α).obj M.val ⟶
        (PresheafOfModules.restrictScalars α).obj N.val :=
      PresheafOfModules.homMk f.hom (by
        intro U z x
        obtain ⟨z⟩ := z
        change f.hom.app U ((α.app U).hom (z : ULift.{r} ℤ) • (show M.val.obj U from x)) =
          (α.app U).hom (z : ULift.{r} ℤ) • (show N.val.obj U from f.hom.app U x)
        rw [map_intCast, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
        exact map_zsmul (f.hom.app U).hom z x)
    let g' := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      α N.isSheaf).symm g
    refine ⟨⟨g'⟩, ?_⟩
    have h := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      α N.isSheaf).apply_symm_apply g
    ext U x
    exact congrArg (fun k ↦ k.app U x) h

private noncomputable def liftTorsion (n : ℕ) (M : Integral J)
    (hM : ∀ (U : Cᵒᵖ) (x : M.val.obj U), n • x = 0) : Residue J n :=
  PresheafOfModules.sheafify (ringUnit (J := J) (CommRingCat.of (ULift.{r} (ZMod n))))
    (M₀ := CategoryTheory.Sheaf.presheafOfModulesOfNsmul M.val.presheaf hM)
    (A := (toSheaf _).obj M) (𝟙 _)

private noncomputable def liftTorsionIso (n : ℕ) (M : Integral J)
    (hM : ∀ (U : Cᵒᵖ) (x : M.val.obj U), n • x = 0) :
    M ≅ (restriction J n).obj (liftTorsion n M hM) :=
  (toSheaf (derivedChangeRingIndependentCoefficients J (integers J))).preimageIso (Iso.refl _)
attribute [irreducible] liftTorsion liftTorsionIso

omit [EssentiallySmall.{r} C] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] in
private theorem nsmul_sections_of_id (n : ℕ) (M : Integral J)
    (h : n • 𝟙 M = 0) (U : Cᵒᵖ) (x : M.val.obj U) : n • x = 0 := by
  let ev := toSheaf (derivedChangeRingIndependentCoefficients J (integers J)) ⋙
    sheafToPresheaf J AddCommGrpCat ⋙ (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat).obj U
  have he := ev.congr_map h
  rw [ev.map_nsmul, ev.map_id, ev.map_zero] at he
  have hx := ConcreteCategory.congr_hom he x
  simpa using hx

omit [EssentiallySmall.{r} C] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] in
private theorem residue_nsmul_zero (n : ℕ) (M : Residue J n)
    (U : Cᵒᵖ) (x : M.val.obj U) : n • x = 0 := by
  have h : (n : ULift.{r} (ZMod n)) = 0 :=
    ULift.ext (by rw [ULift.down_natCast, ZMod.natCast_self]; rfl)
  let α := ringUnit (J := J) (CommRingCat.of (ULift.{r} (ZMod n)))
  have h' : (α.app U).hom (n : ULift.{r} (ZMod n)) =
      (n : (residues J n).obj.obj U) := map_natCast _ n
  rw [← Nat.cast_smul_eq_nsmul (R := (residues J n).obj.obj U),
    ← h', h, map_zero, zero_smul]

private instance restriction_faithful (n : ℕ) : (restriction J n).Faithful := by
  refine ⟨fun {M N} f g h ↦ ?_⟩
  ext U x
  exact congrArg (fun k ↦ k.val.app U x) h

private instance restriction_full (n : ℕ) [NeZero n] : (restriction J n).Full where
  map_surjective {M N} f := by
    let α := ringUnit (J := J) (CommRingCat.of (ULift.{r} (ZMod n)))
    let g : (PresheafOfModules.restrictScalars α).obj M.val ⟶
        (PresheafOfModules.restrictScalars α).obj N.val :=
      PresheafOfModules.homMk
        ((toSheaf (derivedChangeRingIndependentCoefficients J (integers J))).map f).hom (by
        intro U z x
        obtain ⟨z⟩ := z
        have hz : (⟨z⟩ : ULift.{r} (ZMod n)) = (z.val : ULift.{r} (ZMod n)) :=
          ULift.ext (by rw [ULift.down_natCast, ZMod.natCast_zmod_val])
        change f.val.app U ((α.app U).hom (⟨z⟩ : ULift.{r} (ZMod n)) •
          (show M.val.obj U from x)) =
          (α.app U).hom (⟨z⟩ : ULift.{r} (ZMod n)) •
            (show N.val.obj U from f.val.app U x)
        rw [hz, map_natCast, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
        exact map_nsmul (f.val.app U).hom z.val x)
    let g' := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      α N.isSheaf).symm g
    refine ⟨⟨g'⟩, ?_⟩
    have h := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      α N.isSheaf).apply_symm_apply g
    ext U x
    exact congrArg (fun k ↦ k.app U x) h

omit [EssentiallySmall.{r} C] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] in
private theorem ordinaryUnit_zero (n : ℕ) (E : Integral J ⥤ Residue J n)
    (a : E ⊣ restriction J n) (A : Integral J) :
    (n • 𝟙 A) ≫ a.unit.app A = 0 := by
  ext U x
  change (a.unit.app A).val.app U ((n • 𝟙 A).val.app U x) = 0
  have hx : (n • 𝟙 A).val.app U x = n • x := by
    let ev := toSheaf (derivedChangeRingIndependentCoefficients J (integers J)) ⋙
      sheafToPresheaf J AddCommGrpCat ⋙ (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat).obj U
    have he := ev.map_nsmul (f := 𝟙 A) (n := n)
    rw [ev.map_id] at he
    exact ConcreteCategory.congr_hom he x
  rw [hx]
  rw [_root_.map_nsmul]
  exact residue_nsmul_zero n (E.obj A) U _

private noncomputable def ordinaryUnit_cokernel (n : ℕ) [NeZero n]
    (E : Integral J ⥤ Residue J n) (a : E ⊣ restriction J n) (A : Integral J) :
    IsColimit (CokernelCofork.ofπ (a.unit.app A) (ordinaryUnit_zero n E a A)) := by
  let g := n • 𝟙 A
  have hnQ : n • 𝟙 (cokernel g) = 0 := by
    apply (cancel_epi (cokernel.π g)).1
    simpa only [g, Preadditive.nsmul_comp, Category.id_comp,
      Preadditive.comp_nsmul, Category.comp_id, comp_zero] using cokernel.condition g
  let Q := liftTorsion n (cokernel g) (nsmul_sections_of_id n _ hnQ)
  let eQ : cokernel g ≅ (restriction J n).obj Q :=
    liftTorsionIso n (cokernel g) (nsmul_sections_of_id n _ hnQ)
  exact abstractUnitCokernel E (restriction J n) a A g
    (ordinaryUnit_zero n E a A) Q eQ

private theorem integerUnit_mono (n : ℕ) (hn : n ≠ 0) :
    Mono (n • 𝟙 (integerUnit J)) := by
  let F := toSheaf (derivedChangeRingIndependentCoefficients J (integers J))
  let FF := forget₂ CommRingCat.{r} RingCat.{r} ⋙ forget₂ RingCat.{r} AddCommGrpCat.{r}
  have : J.PreservesSheafification FF := by
    constructor
    intro P Q f hf
    change J.W (CategoryTheory.Functor.whiskerRight f FF)
    rw [J.W_iff_isLocallyBijective] at hf ⊢
    let := hf.1
    let := hf.2
    exact ⟨⟨fun x y h ↦ Presheaf.equalizerSieve_mem J f x y h⟩,
      ⟨fun x ↦ Presheaf.imageSieve_mem J f x⟩⟩
  let e : F.obj (integerUnit J) ≅
      (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of (ULift.{r} ℤ)) :=
    (constantCommuteCompose J
      (forget₂ CommRingCat.{r} RingCat.{r} ⋙ forget₂ RingCat.{r} AddCommGrpCat.{r})).app
      (CommRingCat.of (ULift.{r} ℤ))
  have hm : Mono (n • 𝟙 (AddCommGrpCat.of (ULift.{r} ℤ))) := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro x y h
    change n • x = n • y at h
    exact ULift.ext (nsmul_right_injective hn (congrArg ULift.down h))
  have hm' : Mono (n • 𝟙 ((constantSheaf J AddCommGrpCat).obj
      (AddCommGrpCat.of (ULift.{r} ℤ)))) := by
    have : Mono ((CategoryTheory.Functor.const Cᵒᵖ).map
        (n • 𝟙 (AddCommGrpCat.of (ULift.{r} ℤ)))) := NatTrans.mono_of_mono_app _
    have : Mono ((presheafToSheaf J AddCommGrpCat).map
        ((CategoryTheory.Functor.const Cᵒᵖ).map
          (n • 𝟙 (AddCommGrpCat.of (ULift.{r} ℤ))))) := inferInstance
    simpa only [constantSheaf, CategoryTheory.Functor.comp_obj,
      CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id] using this
  have hm'' : Mono (n • 𝟙 (F.obj (integerUnit J))) := by
    have he : (n • 𝟙 (F.obj (integerUnit J))) ≫ e.hom =
        e.hom ≫ (n • 𝟙 _) := by
      simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
        Category.id_comp, Category.comp_id]
    exact mono_of_mono_fac he
  apply F.mono_of_mono_map
  simpa only [F.map_nsmul, F.map_id] using hm''

private theorem flat_multiplication_mono (n : ℕ) (hn : n ≠ 0) (M : Integral J)
    (hM : letI := SheafOfModules.isMonoidal_W_independentCoefficients (integers J)
      exactFunctor _ _
        (@MonoidalCategory.tensorRight _ _ (monoidalCategory (integers J)) M)) :
    Mono (n • 𝟙 M) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients (integers J)
  let := monoidalCategory (integers J)
  let := symmetricCategory (integers J)
  let F := MonoidalCategory.tensorRight M
  have : PreservesFiniteLimits F := hM.1
  have : Mono (n • 𝟙 (integerUnit J)) := integerUnit_mono n hn
  have : Mono (F.map (n • 𝟙 (integerUnit J))) := inferInstance
  have hm : Mono (n • 𝟙 (F.obj (integerUnit J))) := by
    simpa only [F.map_nsmul, F.map_id] using this
  have he : (n • 𝟙 M) ≫ (MonoidalCategory.leftUnitor M).inv =
      (MonoidalCategory.leftUnitor M).inv ≫ (n • 𝟙 (F.obj (integerUnit J))) := by
    simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
      Category.id_comp]
    erw [Category.comp_id]
  exact mono_of_mono_fac he

private theorem multiplication_resolving (n : ℕ) [NeZero n]
    (K : CochainComplex (Integral J) ℤ) :
    ∃ (P : CochainComplex (Integral J) ℤ) (p : P ⟶ K),
      CochainComplex.IsKFlatIndependentCoefficients (R := integers J) P ∧
        (∀ i : ℤ, Mono (n • 𝟙 (P.X i))) ∧ QuasiIso p := by
  obtain ⟨P, p, hP, hf, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := integers J) K
  exact ⟨P, p, hP, fun i ↦ flat_multiplication_mono n (NeZero.ne n) (P.X i) (hf i), hp⟩

omit [EssentiallySmall.{r} C] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] in
private theorem multiplication_complex_zero (n : ℕ)
    (E : Integral J ⥤ Residue J n) [E.Additive] (a : E ⊣ restriction J n)
    (P : CochainComplex (Integral J) ℤ) :
    (n • 𝟙 P) ≫ (a.mapHomologicalComplex (.up ℤ)).unit.app P = 0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  simp only [HomologicalComplex.comp_f, HomologicalComplex.nsmul_f_apply,
    HomologicalComplex.id_f, HomologicalComplex.zero_f,
    Adjunction.mapHomologicalComplex_unit_app_f]
  exact ordinaryUnit_zero n E a (P.X i)

private theorem multiplication_complex_shortExact (n : ℕ) [NeZero n]
    (E : Integral J ⥤ Residue J n) [E.Additive] (a : E ⊣ restriction J n)
    (P : CochainComplex (Integral J) ℤ)
    (hmono : ∀ i : ℤ, Mono (n • 𝟙 (P.X i))) :
    (ShortComplex.mk (n • 𝟙 P) ((a.mapHomologicalComplex (.up ℤ)).unit.app P)
      (multiplication_complex_zero n E a P)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  let g := n • 𝟙 (P.X i)
  have : Mono g := hmono i
  let hc := ordinaryUnit_cokernel n E a (P.X i)
  have : Epi (a.unit.app (P.X i)) :=
    Cofork.IsColimit.epi hc
  have hs : (ShortComplex.mk g (a.unit.app (P.X i))
      (ordinaryUnit_zero n E a (P.X i))).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ hc }
  convert! hs using 1

end PresentationConstruction

variable [HasDerivedCategory.{wZ} (Integral J)]
  [HasDerivedCategory.{wR} (Residue J n)]
  (D : DerivedChangeOfRingsCochainModel (projection J n))

open CategoryTheory.Pretriangulated

private theorem multiplication_triangle [NeZero n] (A : Integral J) :
    ∃ δ, Triangle.mk (n • 𝟙 ((DerivedCategory.singleFunctor (Integral J) 0).obj A))
      (eta n D A) δ ∈ distTriang (DerivedCategory (Integral J)) := by
  classical
  let R := restriction J n
  let a := sheafScalarOrdinaryAdjunction (projection J n) D
  let ad := sheafScalarDerivedAdjunction (projection J n) D
  let K := (CochainComplex.singleFunctor (Integral J) 0).obj A
  obtain ⟨P, p, hP, hm, hp⟩ := multiplication_resolving n K
  have : QuasiIso p := hp
  have : IsIso (D.ε.app P) := D.computes P hP
  have hnormal := scalar_derived_unit (projection J n) D P hP
  exact unit_triangle D.E R a D.T ad D.ε n P K p
    (multiplication_complex_zero n D.E a P)
    (multiplication_complex_shortExact n D.E a P hm) hnormal

set_option backward.isDefEq.respectTransparency true in
attribute [local irreducible] identifications

section InverseImage

variable {C' : Type u'} [Category.{v'} C'] [EssentiallySmall.{r} C']
  {K : GrothendieckTopology C'}
  [HasSheafify K CommRingCat.{r}]
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
  [HasDerivedCategory.{wZ'} (Integral K)] [HasDerivedCategory.{wR'} (Residue K n)]
  (D' : DerivedChangeOfRingsCochainModel (projection K n))
  (UZ : Integral J ⥤ Integral K) (UR : Residue J n ⥤ Residue K n)
  [UZ.Additive] [PreservesFiniteLimits UZ] [PreservesFiniteColimits UZ]
  [UR.Additive] [PreservesFiniteLimits UR] [PreservesFiniteColimits UR]

end InverseImage

end DivisibleReduction
end SheafOfModules
