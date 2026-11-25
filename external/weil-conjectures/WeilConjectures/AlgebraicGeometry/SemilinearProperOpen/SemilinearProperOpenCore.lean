/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.SixFunctors.Supporting.AdjunctConjugateOpenFactor
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

import Mathlib.Util.AliasIn
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import all WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import all WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
import all WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
import all WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
import all WeilConjectures.Algebra.Homology.DerivedInternalHom
import all WeilConjectures.SixFunctors.Etale.Derived.Hom
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Generator.Basic
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import all WeilConjectures.Algebra.Homology.HomComplex
import all WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import all Mathlib.Algebra.Category.Grp.Abelian
import all WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import all WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import all WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import all WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import all WeilConjectures.Algebra.Homology.HomComplexProjections
import all WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import all Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import all WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import all WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import all Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import all Mathlib.Algebra.Category.Grp.EpiMono
import all WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import all WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import all Mathlib.CategoryTheory.Sites.Abelian
import all Mathlib.Algebra.Homology.Functor
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.CategoryTheory.Limits.Final
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.CategoryTheory.Sites.CoverPreserving
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenArrows
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition

/-! # Core constructions for intrinsic proper/open mates of semilinear systems

This file constructs the ordinary and derived system operations, their canonical compositors,
and the intrinsic beta, clopen projector, alpha and gamma, together with the adjunct
normalization. Their coherence laws are proved in a separate module.

## References

* Stacks Project, Tags 0F7B, 0F7C, 0F7D and 0F7F (open cases)
* Stacks Project, Tags 03D7, 03D8, 03DI, 03DJ, 03EK, 05RU, 079P, 07A4, 07A7, 09A5, 09AE and 0D6D
* Zheng, Construction 4.1 and Lemma 4.10
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option synthInstance.maxSize 32
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections

section ProofEnvironment

-- Compare the canonical constructions through their APIs, without unfolding their data.
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf Functor.mapDerivedCategoryNatIso
  HasDerivedCategory.standard DerivedCategory.Q
  Functor.mapDerivedCategoryFactors

section CategoricalProof
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem map_iso_transport
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {X Y Z W : A} (a : X ≅ Y) (b : Z ≅ W) (f : X ⟶ Z) (g : Y ⟶ W)
    (h : f ≫ b.hom = a.hom ≫ g) {V : B} (c : V ⟶ F.obj Y) :
    c ≫ F.map a.inv ≫ F.map f ≫ F.map b.hom = c ≫ F.map g := by
  rw [← F.map_comp, h, F.map_comp, ← Category.assoc (F.map a.inv),
    ← F.map_comp, a.inv_hom_id, F.map_id, Category.id_comp]

private theorem tower_normalized_transport
    {A I D : Type*} [Category A] [Category I] [Category D]
    {J : GrothendieckTopology D} {S : Sheaf J RingCat}
    {F G H : A ⥤ (I ⥤ SheafOfModules.{u} S)}
    (h : G = H) (d : F ≅ G) (V : A → I → D → Type u)
    (hd : ∀ M n U, HEq (fun x ↦ ((d.hom.app M).app n).val.app (op U) x)
      (fun x : V M n U ↦ x)) :
    ∃ e : F ≅ H, ∀ M n U,
      HEq (fun x ↦ ((e.hom.app M).app n).val.app (op U) x)
        (fun x : V M n U ↦ x) := by
  subst H
  exact ⟨d, hd⟩

private theorem tower_iso_ext_sections
    {A I D : Type*} [Category A] [Category I] [Category D]
    {J : GrothendieckTopology D} {S : Sheaf J RingCat}
    {F G : A ⥤ (I ⥤ SheafOfModules.{u} S)} (e e' : F ≅ G)
    (h : ∀ M n U, HEq (fun x ↦ ((e.hom.app M).app n).val.app U x)
      (fun x ↦ ((e'.hom.app M).app n).val.app U x)) : e = e' := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  ext U x
  exact congrFun (eq_of_heq (h M n U)) x

private theorem normalized_function {A B D : Type u}
    (hA : A = D) (hB : B = D) (f : A → B) (hf : ∀ x, HEq (f x) x) :
    HEq f (fun x : D ↦ x) := by
  subst A B
  exact heq_of_eq (funext fun x ↦ eq_of_heq (hf x))

private theorem isIso_of_heq
    {A B : Type*} [Category A] [Category B] {F G H : A ⥤ B}
    (h : G = H) (f : F ⟶ G) (g : F ⟶ H) (hf : HEq f g) [IsIso g] : IsIso f := by
  subst H
  cases eq_of_heq hf
  infer_instance

private theorem normalized_square
    {A B D E M N : Type u} (hA : A = M) (hB : B = N) (hD : D = M) (hE : E = N)
    (a : A → B) (b : B → E) (c : A → D) (d : D → E) (t : M → N)
    (ha : HEq a t) (hb : HEq b (fun x : N ↦ x))
    (hc : HEq c (fun x : M ↦ x)) (hd : HEq d t) :
    (fun x ↦ b (a x)) = (fun x ↦ d (c x)) := by
  subst A B D E
  rw [eq_of_heq ha, eq_of_heq hb, eq_of_heq hc, eq_of_heq hd]

private theorem chosen_unit_isIso_congr
    {A B : Type*} [Category A] [Category B] (F G : A ⥤ B)
    [F.IsRightAdjoint] [G.IsRightAdjoint] (h : F = G)
    (hi : IsIso (Adjunction.ofIsRightAdjoint G).unit) :
    IsIso (Adjunction.ofIsRightAdjoint F).unit := by
  subst G
  exact hi

private theorem exact_derived_congr
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (h : F = G) :
    F.mapDerivedCategory = G.mapDerivedCategory := by
  subst G
  rfl

private theorem right_derived_congr
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions A]
    {F G : A ⥤ B} [F.Additive] [G.Additive] (h : F = G) :
    F.rightDerivedFunctor = G.rightDerivedFunctor := by
  subst G
  rfl

private def constant_diagram_square
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ E) (I : E ⥤ D)
    (e : F ⋙ G ≅ H ⋙ I) :
    F ⋙ (G ⋙ Functor.const ℕᵒᵖ) ≅
      (H ⋙ Functor.const ℕᵒᵖ) ⋙ (Functor.whiskeringRight ℕᵒᵖ E D).obj I :=
  NatIso.ofComponents
    (fun M ↦ NatIso.ofComponents (fun _ ↦ e.app M) (by intros; simp))
    (by
      intro M N f
      apply NatTrans.ext
      funext n
      exact e.hom.naturality f)

private theorem constant_diagram_square_hom_app
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ E) (I : E ⥤ D)
    (e : F ⋙ G ≅ H ⋙ I) (M : A) (m : ℕᵒᵖ) :
    ((constant_diagram_square F G H I e).hom.app M).app m = e.hom.app M := rfl

private theorem constant_diagram_square_inv_app
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ E) (I : E ⥤ D)
    (e : F ⋙ G ≅ H ⋙ I) (M : A) (m : ℕᵒᵖ) :
    ((constant_diagram_square F G H I e).inv.app M).app m = e.inv.app M := rfl

private theorem mate_of_unit_normalization
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {L : A ⥤ B} {R : B ⥤ A} {l : D ⥤ E} {r : E ⥤ D}
    (a : L ⊣ R) (b : l ⊣ r) (F : A ⥤ D) (G : B ⥤ E)
    (e : L ⋙ G ≅ F ⋙ l) (d : R ⋙ F ≅ G ⋙ r)
    (h : ∀ M : A, F.map (a.unit.app M) ≫ d.hom.app (L.obj M) ≫
      r.map (e.hom.app M) = b.unit.app (F.obj M)) :
    mateEquiv a b e.inv = d.hom := by
  apply mateEquiv_eq_of_unit a b _ _
  intro M
  have hh := congrArg (fun t ↦ t ≫ r.map (e.inv.app M)) (h M)
  simp only [Category.assoc, ← Functor.map_comp] at hh
  rw [e.hom_inv_id_app] at hh
  have hi : r.map (𝟙 ((L ⋙ G).obj M)) = 𝟙 _ := r.map_id _
  rw [hi] at hh
  erw [Category.comp_id] at hh
  exact hh

private theorem constant_diagram_mate
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {L : A ⥤ B} {R : B ⥤ A} {l : D ⥤ E} {r : E ⥤ D}
    (a : L ⊣ R) (b : l ⊣ r) (F : A ⥤ D) (G : B ⥤ E)
    (e : L ⋙ G ≅ F ⋙ l) (d : R ⋙ F ≅ G ⋙ r)
    (h : ∀ M : A, F.map (a.unit.app M) ≫ d.hom.app (L.obj M) ≫
      r.map (e.hom.app M) = b.unit.app (F.obj M)) :
    mateEquiv a (b.whiskerRight ℕᵒᵖ) (constant_diagram_square L G F l e).inv =
      (constant_diagram_square R F G r d).hom := by
  apply mate_of_unit_normalization a (b.whiskerRight ℕᵒᵖ)
    (F ⋙ Functor.const ℕᵒᵖ) (G ⋙ Functor.const ℕᵒᵖ)
    (constant_diagram_square L G F l e) (constant_diagram_square R F G r d)
  intro M
  apply NatTrans.ext
  funext m
  simpa [constant_diagram_square] using h M

private theorem composite_conjugate_inv
    {A B D : Type*} [Category A] [Category B] [Category D]
    {L : A ⥤ D} {R : D ⥤ A} {L₁ : A ⥤ B} {R₁ : B ⥤ A}
    {L₂ : B ⥤ D} {R₂ : D ⥤ B}
    (a : L ⊣ R) (b : L₁ ⊣ R₁) (c : L₂ ⊣ R₂)
    (e : L ≅ L₁ ⋙ L₂) (M : D) :
    b.homEquiv (R.obj M) (R₂.obj M) (c.unit.app (L₁.obj (R.obj M)) ≫
      R₂.map (e.inv.app (R.obj M) ≫ a.counit.app M)) =
        (conjugateIsoEquiv (b.comp c) a e).inv.app M := by
  simp [Adjunction.homEquiv_unit, conjugateIsoEquiv_apply_inv,
    conjugateEquiv, mateEquiv, Adjunction.comp_unit_app, Functor.map_comp,
    Category.assoc]

private def adjunct_comparison
    {A B D E F : Type*}
    [Category A] [Category B] [Category D] [Category E] [Category F]
    {Rr : A ⥤ D} {Lp : E ⥤ B} {Rp : B ⥤ E}
    {Ji : D ⥤ E} {Pi : E ⥤ D} {Jb : F ⥤ B} {Pb : B ⥤ F}
    {Lq : D ⥤ F} {Rq : F ⥤ D} {Rs : A ⥤ F}
    {Js : A ⥤ F} {Jk : A ⥤ B}
    (ap : Lp ⊣ Rp) (ai : Ji ⊣ Pi) (ab : Jb ⊣ Pb) (aq : Lq ⊣ Rq)
    [IsIso ab.unit] (β : Ji ⋙ Lp ≅ Lq ⋙ Jb) (d : Js ⋙ Jb ≅ Jk)
    (t : Js ≅ Rs) (δ : Rs ⋙ Rq ≅ Rr) : (Jk ⋙ Rp) ⋙ Pi ≅ Rr :=
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft Jk (conjugateIsoEquiv (ai.comp ap) (aq.comp ab) β.symm) ≪≫
  (Functor.associator _ _ _).symm ≪≫
  Functor.isoWhiskerRight
    (Functor.isoWhiskerRight d.symm Pb ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft Js (asIso ab.unit).symm ≪≫ Functor.rightUnitor _) Rq ≪≫
  Functor.isoWhiskerRight t Rq ≪≫ δ

private theorem adjunct_comparison_identity
    {A B D E F : Type*}
    [Category A] [Category B] [Category D] [Category E] [Category F]
    {Lr : D ⥤ A} {Rr : A ⥤ D} {Lp : E ⥤ B} {Rp : B ⥤ E}
    {Ji : D ⥤ E} {Pi : E ⥤ D} {Jb : F ⥤ B} {Pb : B ⥤ F}
    {Lq : D ⥤ F} {Rq : F ⥤ D} {Ls : F ⥤ A} {Rs : A ⥤ F}
    {Js : A ⥤ F} {Jk : A ⥤ B}
    (ar : Lr ⊣ Rr) (ap : Lp ⊣ Rp) (ai : Ji ⊣ Pi)
    (ab : Jb ⊣ Pb) (aq : Lq ⊣ Rq) (as_ : Ls ⊣ Rs) [IsIso ab.unit]
    (β : Ji ⋙ Lp ≅ Lq ⋙ Jb) (d : Js ⋙ Jb ≅ Jk)
    (e : Lr ≅ Lq ⋙ Ls) (t : Js ≅ Rs) (δ : Rs ⋙ Rq ≅ Rr)
    (hδ : conjugateIsoEquiv (aq.comp as_) ar e = δ)
    (α : Ji ⋙ Lp ⟶ Lr ⋙ Jk) (M : A)
    (f : Lq.obj (Rr.obj M) ⟶ Js.obj M)
    (hα : β.inv.app (Rr.obj M) ≫ α.app (Rr.obj M) ≫
      Jk.map (ar.counit.app M) = Jb.map f ≫ d.hom.app M)
    (hf : f ≫ t.hom.app M = as_.unit.app (Lq.obj (Rr.obj M)) ≫
      Rs.map (e.inv.app (Rr.obj M) ≫ ar.counit.app M)) :
    ai.homEquiv _ _ ((mateEquiv ar ap α).app M) ≫
      (adjunct_comparison ap ai ab aq β d t δ).hom.app M = 𝟙 _ := by
  have ht := adjunct_transport ar ap ai ab aq β d α M f hα
  have hh := congrArg (fun z ↦ z ≫ Rq.map (t.hom.app M)) ht
  simp only [← Category.assoc] at hh
  rw [← aq.homEquiv_naturality_right, hf,
    composite_conjugate_inv ar aq as_ e M, hδ] at hh
  have hh' := congrArg (fun z ↦ z ≫ δ.hom.app M) hh
  simp only [Iso.inv_hom_id_app] at hh'
  simpa only [adjunct_comparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.rightUnitor_hom_app,
    asIso_inv, NatIso.isIso_inv_app, Functor.id_obj, Functor.comp_obj,
    Category.id_comp, Category.comp_id,
    Category.assoc] using hh'

private theorem homEquiv_iso_inverse
    {A B : Type*} [Category A] [Category B] {J : A ⥤ B} {P : B ⥤ A}
    (a : J ⊣ P) {X : A} {Y : B} (f : J.obj X ⟶ Y) (e : P.obj Y ≅ X)
    (h : a.homEquiv X Y f ≫ e.hom = 𝟙 X) :
    a.homEquiv X Y f = e.inv ∧ a.unit.app X ≫ P.map f ≫ e.hom = 𝟙 X := by
  constructor
  · apply (cancel_mono e.hom).1
    simpa only [Iso.inv_hom_id] using h
  · simpa only [Adjunction.homEquiv_unit, Category.assoc] using h

private def projection_square
    {A B D E F : Type*}
    [Category A] [Category B] [Category D] [Category E] [Category F]
    {Lr : D ⥤ A} {Lp : E ⥤ B} {Ji : D ⥤ E}
    {Jb : F ⥤ B} {Lq : D ⥤ F} {Ls : F ⥤ A}
    {Js : A ⥤ F} {Jk : A ⥤ B}
    (β : Ji ⋙ Lp ≅ Lq ⋙ Jb) (d : Js ⋙ Jb ≅ Jk) (e : Lr ≅ Lq ⋙ Ls)
    (π : 𝟭 F ⟶ Ls ⋙ Js) : Ji ⋙ Lp ⟶ Lr ⋙ Jk :=
  β.hom ≫ Functor.whiskerRight (Functor.whiskerLeft Lq π) Jb ≫
    Functor.whiskerRight (Functor.associator Lq Ls Js).inv Jb ≫
    (Functor.associator (Lq ⋙ Ls) Js Jb).hom ≫
    Functor.whiskerLeft (Lq ⋙ Ls) d.hom ≫ Functor.whiskerRight e.inv Jk

private theorem projection_square_formula
    {A B D E F : Type*}
    [Category A] [Category B] [Category D] [Category E] [Category F]
    {Lr : D ⥤ A} {Lp : E ⥤ B} {Ji : D ⥤ E}
    {Jb : F ⥤ B} {Lq : D ⥤ F} {Ls : F ⥤ A}
    {Js : A ⥤ F} {Jk : A ⥤ B}
    (β : Ji ⋙ Lp ≅ Lq ⋙ Jb) (d : Js ⋙ Jb ≅ Jk) (e : Lr ≅ Lq ⋙ Ls)
    (π : 𝟭 F ⟶ Ls ⋙ Js) (N : D) (M : A) (m : Lr.obj N ⟶ M) :
    β.inv.app N ≫
      (projection_square β d e π).app N ≫
      Jk.map m = Jb.map (π.app (Lq.obj N) ≫ Js.map (e.inv.app N ≫ m)) ≫
        d.hom.app M := by
  have hn := d.hom.naturality (e.inv.app N ≫ m)
  simp only [Functor.comp_map] at hn
  rw [Jb.map_comp, Category.assoc, hn]
  simp only [projection_square, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    CategoryTheory.Functor.map_id, Functor.comp_obj, Category.id_comp,
    Category.assoc, Functor.map_comp, β.inv_hom_id_app_assoc]

private theorem projection_square_formula_of_eq
    {A B D E F : Type*}
    [Category A] [Category B] [Category D] [Category E] [Category F]
    {Lr : D ⥤ A} {Lp : E ⥤ B} {Ji : D ⥤ E}
    {Jb : F ⥤ B} {Lq : D ⥤ F} {Ls : F ⥤ A}
    {Js : A ⥤ F} {Jk : A ⥤ B}
    (β : Ji ⋙ Lp ≅ Lq ⋙ Jb) (d : Js ⋙ Jb ≅ Jk) (e : Lr ≅ Lq ⋙ Ls)
    (π : 𝟭 F ⟶ Ls ⋙ Js) (α : Ji ⋙ Lp ⟶ Lr ⋙ Jk)
    (hα : α = projection_square β d e π)
    (N : D) (M : A) (m : Lr.obj N ⟶ M) :
    β.inv.app N ≫ α.app N ≫ Jk.map m =
      Jb.map (π.app (Lq.obj N) ≫ Js.map (e.inv.app N ≫ m)) ≫ d.hom.app M := by
  subst α
  exact projection_square_formula β d e π N M m

attribute [local implicit_reducible] SemilinearSections.ringPresheaf

private theorem ordinary_restriction_existsUnique
    {D : Type (u + 1)} [Category.{u} D] (K : GrothendieckTopology D)
    (A₀ : ℕ → Sheaf K CommRingCat.{u + 1}) (t : ∀ n, A₀ (n + 1) ⟶ A₀ n)
    (S : Sheaf K CommRingCat.{u + 1}) (α₀ : ∀ n, S ⟶ A₀ n)
    (compatible : ∀ n, α₀ (n + 1) ≫ t n = α₀ n) :
    ∃! F : Systems.{u + 1, u, u + 1} K A₀ t ⥤
        (ℕᵒᵖ ⥤ SemilinearSections.Mod.{u + 1, u, u + 1} K S),
      (∀ n : ℕ, F ⋙ (CategoryTheory.evaluation ℕᵒᵖ
        (SemilinearSections.Mod.{u + 1, u, u + 1} K S)).obj (op n) =
        SemilinearSections.evaluation.{u + 1, u, u + 1} K A₀ t n ⋙
          SemilinearSections.res.{u + 1, u, u + 1} (α₀ n)) ∧
      (∀ (M : Systems.{u + 1, u, u + 1} K A₀ t) (n m : ℕ) (h : n ≤ m) (U : D),
        HEq (fun x ↦ ((((F.obj M).map (homOfLE h).op).val.app (op U)) x))
          (fun x : M.val.obj (op (m, U)) ↦
            M.val.map (Prod.mkHom (homOfLE h) (𝟙 U)).op x)) := by
  let J₀ := K
  let A := S
  let R₀ : Sheaf (coefficientSequenceTopology J₀) RingCat.{u + 1} :=
    SemilinearSections.ring.{u + 1, u, u + 1} (coefficientSequenceTopology J₀)
    (SemilinearSections.systemRing.{u + 1, u, u + 1} K A₀ t)
  let α := α₀
  obtain ⟨a, ha⟩ : ∃ a : (Functor.const ℕᵒᵖ).obj A ⟶
      SemilinearSections.rings.{u + 1, u, u + 1} J₀ A₀ t,
      ∀ n, a.app (op n) = α n := by
    refine ⟨NatTrans.ofOpSequence α (fun n ↦ ?_), fun _ ↦ rfl⟩
    simp only [Functor.const_obj_map, SemilinearSections.rings,
      Functor.ofOpSequence_map_homOfLE_succ]
    exact (Category.id_comp (α n)).trans (compatible n).symm
  let p (n : ℕ) := (sheafCompose J₀ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (α n)
  let ψ (n : ℕ) := eqToHom
    (SemilinearSections.evaluation_ring.{u + 1, u, u + 1} J₀ A₀ t n).symm
  let ρ (n : ℕ) := p n ≫ ψ n
  have hρ {m n : ℕ} (h : n ≤ m) :
      ρ m ≫ (Functor.sheafPushforwardContinuousNatTrans
        (WeilConjectures.verticalNat h) RingCat J₀ (coefficientSequenceTopology J₀)).app
          R₀ = ρ n := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    have hm : (ψ m).hom.app U = 𝟙 _ := by
      dsimp only [ψ]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    have hn : (ψ n).hom.app U = 𝟙 _ := by
      dsimp only [ψ]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    dsimp only [ρ, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
    simp only [hm, hn]
    change (p m).hom.app U ≫ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      ((SemilinearSections.ringPresheaf.{u + 1, u, u + 1} J₀ A₀ t).map
        (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op) = _
    dsimp only [SemilinearSections.ringPresheaf]
    rw [SemilinearSections.horizontal_map']
    have hh := congrArg (fun t ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      (t.hom.app U)) (a.naturality (homOfLE h).op)
    change (p m).hom.app U ≫ _ = (p n).hom.app U ≫ 𝟙 _
    rw [Category.comp_id]
    change (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      ((α m).hom.app U) ≫ _ =
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map ((α n).hom.app U)
    simp only [Functor.const_obj_map, ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.FullSubcategory.id_hom, NatTrans.comp_app, NatTrans.id_app,
      Functor.map_comp] at hh
    rw [ha m, ha n] at hh
    have hi : (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        (𝟙 (A.obj.obj U)) = 𝟙 _ := (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map_id _
    rw [hi] at hh
    erw [Category.id_comp] at hh
    exact hh.symm
  obtain ⟨F, hF⟩ := WeilConjectures.towers_generic J₀ R₀
    (SemilinearSections.ring.{u + 1, u, u + 1} J₀ A) ρ (fun h ↦ hρ h)
  have hobj (M : Systems.{u + 1, u, u + 1} K A₀ t) (n : ℕ) :
      (F.obj M).obj (op n) =
      (SemilinearSections.res.{u + 1, u, u + 1} (α n)).obj
        ((SemilinearSections.evaluation.{u + 1, u, u + 1} J₀ A₀ t n).obj M) :=
    (hF.1 M n).trans (WeilConjectures.pushforward_restrict_obj J₀ R₀ n (p n) (ψ n) M)
  have he (n : ℕ) :
      F ⋙ (CategoryTheory.evaluation ℕᵒᵖ
        (SemilinearSections.Mod.{u + 1, u, u + 1} K S)).obj (op n) =
      SemilinearSections.evaluation.{u + 1, u, u + 1} J₀ A₀ t n ⋙
        SemilinearSections.res.{u + 1, u, u + 1} (α n) := by
    refine CategoryTheory.Functor.ext (fun M ↦ hobj M n) ?_
    intro M N f
    apply WeilConjectures.moduleSheaf_hom_eq_of_heq (hobj M n) (hobj N n)
    intro U
    exact hF.2.2 f n U
  refine ⟨F, ⟨he, fun M n m h U ↦ hF.2.1 M m n h (op U)⟩, ?_⟩
  intro G hG
  have hGF (n : ℕ) := (hG.1 n).trans (he n).symm
  have hobjGF (M : Systems.{u + 1, u, u + 1} K A₀ t) : G.obj M = F.obj M := by
    refine CategoryTheory.Functor.ext (fun n ↦ Functor.congr_obj (hGF n.unop) M) ?_
    intro m n f
    apply WeilConjectures.moduleSheaf_hom_eq_of_heq
      (Functor.congr_obj (hGF m.unop) M) (Functor.congr_obj (hGF n.unop) M)
    intro U
    exact (hG.2 M n.unop m.unop (leOfHom f.unop) U.unop).trans
      (hF.2.1 M m.unop n.unop (leOfHom f.unop) U).symm
  refine CategoryTheory.Functor.ext hobjGF ?_
  intro M N f
  apply NatTrans.ext
  funext n
  simpa only [NatTrans.comp_app, eqToHom_app, Functor.comp_obj, Functor.comp_map,
    CategoryTheory.evaluation_obj_obj, CategoryTheory.evaluation_obj_map, op_unop] using
      Functor.congr_hom (hGF n.unop) f

end CategoricalProof

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section DerivedSquareConjugation
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
  [Abelian A] [Abelian B] [Abelian D] [Abelian E]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory D] [HasDerivedCategory E]
  {L : A ⥤ B} {l : D ⥤ E} {G G' : A ⥤ D} {H H' : B ⥤ E}
  [L.Additive] [l.Additive] [G.Additive] [G'.Additive] [H.Additive] [H'.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits l] [PreservesFiniteColimits l]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
private theorem derived_square_conjugate (a : G' ≅ G) (b : G ⋙ l ≅ L ⋙ H) (c : H ≅ H') :
    (Functor.mapDerivedCategorySquareIso
      (Functor.isoWhiskerRight a l ≪≫ b ≪≫ Functor.isoWhiskerLeft L c)).hom =
    Functor.whiskerRight (Functor.mapDerivedCategoryNatIso a).hom l.mapDerivedCategory ≫
      (Functor.mapDerivedCategorySquareIso b).hom ≫
      Functor.whiskerLeft L.mapDerivedCategory (Functor.mapDerivedCategoryNatIso c).hom := by
  simp only [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_trans,
    Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc (Functor.mapDerivedCategoryNatIso
    (Functor.isoWhiskerRight a l)).hom]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryNatIso_isoWhiskerLeft]
  have h := Functor.mapDerivedCategoryNatIso_isoWhiskerRight a l
  have h' : (Functor.mapDerivedCategoryCompIso G' l).hom ≫
      (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerRight a l)).hom =
      Functor.whiskerRight (Functor.mapDerivedCategoryNatIso a).hom l.mapDerivedCategory ≫
        (Functor.mapDerivedCategoryCompIso G l).hom := by
    apply (cancel_mono (Functor.mapDerivedCategoryCompIso G l).inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [h, Iso.hom_inv_id_assoc]
  rw [reassoc_of% h']

private theorem derived_iso_symm_inv (a : G' ≅ G) :
    (Functor.mapDerivedCategoryNatIso a.symm).inv =
      (Functor.mapDerivedCategoryNatIso a).hom := by
  simpa only [Iso.symm_symm_eq] using (Functor.mapDerivedCategoryNatIso_symm a.symm).symm

end DerivedSquareConjugation

section DerivedConstantSquare
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
  [Abelian A] [Abelian B] [Abelian D] [Abelian E]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory D] [HasDerivedCategory E]
  [HasDerivedCategory (ℕᵒᵖ ⥤ D)] [HasDerivedCategory (ℕᵒᵖ ⥤ E)]
  (L : A ⥤ B) (G : B ⥤ D) (F : A ⥤ E) (l : E ⥤ D)
  [L.Additive] [G.Additive] [F.Additive] [l.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits l] [PreservesFiniteColimits l]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ E D).obj l)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ E D).obj l)]

private theorem derived_constant_square_comp (e : L ⋙ G ≅ F ⋙ l) :
    Functor.whiskerRight (Functor.mapDerivedCategoryNatIso (Iso.refl (F ⋙ Functor.const ℕᵒᵖ)) ≪≫
          (Functor.mapDerivedCategoryCompIso F (Functor.const ℕᵒᵖ)).symm).hom
        ((Functor.whiskeringRight ℕᵒᵖ E D).obj l).mapDerivedCategory ≫
      ((TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso e.symm).hom).hComp
        (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso
          (Functor.compConstIso ℕᵒᵖ l).symm).hom)) =
    (Functor.mapDerivedCategorySquareIso (constant_diagram_square L G F l e).symm).hom ≫
      Functor.whiskerLeft L.mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso (Iso.refl (G ⋙ Functor.const ℕᵒᵖ)) ≪≫
          (Functor.mapDerivedCategoryCompIso G (Functor.const ℕᵒᵖ)).symm).hom := by
  have h := Functor.mapDerivedCategorySquareIso_comp
    F (Functor.const ℕᵒᵖ) (F ⋙ Functor.const ℕᵒᵖ)
    G (Functor.const ℕᵒᵖ) (G ⋙ Functor.const ℕᵒᵖ)
    L l ((Functor.whiskeringRight ℕᵒᵖ E D).obj l)
    e.symm (Functor.compConstIso ℕᵒᵖ l).symm
    (constant_diagram_square L G F l e).symm (Iso.refl _) (Iso.refl _) (by
      intro M
      apply NatTrans.ext
      funext m
      simp only [Iso.symm_hom, NatTrans.comp_app, constant_diagram_square_inv_app]
      simp only [Functor.comp_obj, Functor.const_obj_obj,
        Iso.refl_hom, NatTrans.id_app, Functor.whiskeringRight_obj_map,
        Functor.whiskerRight_app, Functor.compConstIso_inv_app_app,
        Functor.const_map_app, CategoryTheory.Functor.map_id,
        Category.comp_id]
      erw [Category.id_comp, Category.id_comp])
  simpa only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Iso.symm_hom, TwoSquare.hComp, TwoSquare.mk,
    Category.id_comp, Category.assoc]
    using congrArg Iso.hom h

private theorem derived_constant_square_inverse (e : L ⋙ G ≅ F ⋙ l) :
    Functor.whiskerLeft L.mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso (Iso.refl (G ⋙ Functor.const ℕᵒᵖ)) ≪≫
          (Functor.mapDerivedCategoryCompIso G (Functor.const ℕᵒᵖ)).symm).hom ≫
      ((TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso e).hom).vComp
        (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso
          (Functor.compConstIso ℕᵒᵖ l)).hom)) =
    (Functor.mapDerivedCategorySquareIso (constant_diagram_square L G F l e)).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategoryNatIso (Iso.refl (F ⋙ Functor.const ℕᵒᵖ)) ≪≫
          (Functor.mapDerivedCategoryCompIso F (Functor.const ℕᵒᵖ)).symm).hom
        ((Functor.whiskeringRight ℕᵒᵖ E D).obj l).mapDerivedCategory := by
  apply NatTrans.ext
  funext K
  have h := Functor.exactSquare_comp_inverse
    F (Functor.const ℕᵒᵖ) (F ⋙ Functor.const ℕᵒᵖ)
    G (Functor.const ℕᵒᵖ) (G ⋙ Functor.const ℕᵒᵖ)
    L l ((Functor.whiskeringRight ℕᵒᵖ E D).obj l)
    e (Functor.compConstIso ℕᵒᵖ l) (constant_diagram_square L G F l e)
    (Iso.refl _) (Iso.refl _) (by
      intro M
      apply NatTrans.ext
      funext m
      simp only [NatTrans.comp_app, constant_diagram_square_hom_app]
      simp only [Functor.comp_obj, Functor.const_obj_obj,
        Iso.refl_hom, NatTrans.id_app, Functor.whiskeringRight_obj_map,
        Functor.whiskerRight_app, Functor.compConstIso_hom_app_app,
        Functor.const_map_app, CategoryTheory.Functor.map_id,
        Category.id_comp, Category.comp_id]
      erw [Category.comp_id]) K
  simpa only [Iso.trans_hom, NatTrans.comp_app, NatTrans.id_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    TwoSquare.vComp, TwoSquare.mk,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc] using h.symm

end DerivedConstantSquare

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen

/-- The original site is essentially small in the coefficient universe. -/
instance proEtSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)

/-- The coefficient sheaves are the existing constant sheaves, at every level. -/
abbrev coefficients (X : Scheme.{u}) (n : ℕ) :
    Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  (constantSheaf.{u, u + 1, u + 1, u + 2} (ProEt.topology X) CommRingCat.{u + 1}).obj (C n)

/-- The given ring transitions, with no flatness condition. -/
abbrev transition (X : Scheme.{u}) (n : ℕ) :
    coefficients C X (n + 1) ⟶ coefficients C X n :=
  (constantSheaf.{u, u + 1, u + 1, u + 2} (ProEt.topology X) CommRingCat.{u + 1}).map (τ n)

/-- The actual ring on the vertical sequence site from the recorded section model. -/
abbrev ringSystem (X : Scheme.{u}) :=
  systemRing.{u + 1, u, u + 1} (ProEt.topology X) (coefficients C X) (transition C τ X)

/-- Strict semilinear module systems, using the recorded ringed-site model. -/
abbrev Modules (X : Scheme.{u}) :=
  Systems.{u + 1, u, u + 1} (ProEt.topology X) (coefficients C X) (transition C τ X)

/-- The standard derived-category instance at its specified localization size. -/
instance derived (X : Scheme.{u}) : HasDerivedCategory.{u + 2} (Modules C τ X) :=
  HasDerivedCategory.standard _

/-- Ordinary unbounded derived systems; this is not a diagram of derived categories. -/
abbrev Derived (X : Scheme.{u}) :=
  DerivedCategory (Modules C τ X)

/-- Base change acts at the same index on the existing sequence site. -/
abbrev siteMap {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (𝟭 ℕ).prod (proEtaleBaseChange f)

/-- Continuity on the vertical topology. -/
theorem siteMap_continuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (siteMap f).IsContinuous (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceTopology (ProEt.topology X)) := by
  exact VaryingRing.baseChange_continuous f

attribute [instance] siteMap_continuous

/-- The system coefficient map is uniquely fixed by the constant-section maps. -/
theorem coefficientMap_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! a : ringSystem C τ Y ⟶ ((siteMap f).sheafPushforwardContinuous
      CommRingCat.{u + 1} (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceTopology (ProEt.topology X))).obj (ringSystem C τ X),
      ∀ (n : ℕ) (U : Y.ProEt), HEq (a.hom.app (op (n, U)))
        ((proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (C n)).hom.app (op U)) := by
  let a : ringSystem C τ Y ⟶ ((siteMap f).sheafPushforwardContinuous
      CommRingCat.{u + 1} (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceTopology (ProEt.topology X))).obj (ringSystem C τ X) :=
    ⟨{ app := fun U ↦
        (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (C U.unop.1)).hom.app
          (op U.unop.2)
       naturality := fun U V h ↦ by
        apply (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map_injective
        exact VaryingRing.ringMapApp_naturality C τ f h }⟩
  refine ⟨a, fun n U ↦ HEq.rfl, ?_⟩
  intro b hb
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact eq_of_heq (hb U.unop.1 U.unop.2)

/-- The unique componentwise constant-section structural ring map. -/
def coefficientMap {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (coefficientMap_existsUnique C τ f).choose

set_option synthInstance.maxSize 64 in
private theorem coefficientMap_forget_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (coefficientMap C τ f) = VaryingRing.ringMap C τ f := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact congrArg (fun a ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map a)
    (eq_of_heq ((coefficientMap_existsUnique C τ f).choose_spec.1 U.unop.1 U.unop.2))

attribute [local irreducible] SemilinearSections.systemRing
  coefficientMap VaryingRing.ringMap

set_option synthInstance.maxSize 64 in
/-- Actual module direct image on the ringed sequence site, including transitions. -/
def push {X Y : Scheme.{u}} (f : X ⟶ Y) : Modules C τ X ⥤ Modules C τ Y :=
  SheafOfModules.pushforward (F := siteMap f)
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (coefficientMap C τ f))

private theorem push_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    push C τ f = VaryingRing.push C τ f := by
  unfold push VaryingRing.push
  rw [coefficientMap_forget_eq]

/-- Sectionwise direct image is additive. -/
theorem push_additive {X Y : Scheme.{u}} (f : X ⟶ Y) : (push C τ f).Additive := by
  constructor
  intros M N f g
  ext U x
  rfl

attribute [instance] push_additive

/-- Inverse image is the left adjoint to the actual system direct image. -/
theorem push_isRightAdjoint {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (push C τ f).IsRightAdjoint := by
  rw [push_eq]
  exact VaryingRing.push_isRightAdjoint C τ f

attribute [instance] push_isRightAdjoint

/-- The inverse image specified by its module-sheaf adjunction universal property. -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) := (push C τ f).leftAdjoint

/-- The ordinary system adjunction; its unit and counit fix the mate normalization. -/
def ordinaryAdj {X Y : Scheme.{u}} (f : X ⟶ Y) : pull C τ f ⊣ push C τ f :=
  Adjunction.ofIsRightAdjoint _

private theorem pull_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pull C τ f = VaryingRing.pull C τ f := by
  unfold pull VaryingRing.pull
  congr 1
  exact push_eq C τ f

/-- Inverse image is exact, since its coefficients are identified constant sheaves. -/
theorem pull_exact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pull C τ f).Additive ∧ PreservesFiniteLimits (pull C τ f) ∧
      PreservesFiniteColimits (pull C τ f) := by
  rw [pull_eq]
  exact VaryingRing.pull_exact C τ f

/-- Exact inverse-image additivity. -/
instance pull_additive {X Y : Scheme.{u}} (f : X ⟶ Y) : (pull C τ f).Additive :=
  (pull_exact C τ f).1

/-- Left exact inverse image. -/
instance pull_limits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (pull C τ f) := (pull_exact C τ f).2.1

/-- Right exact inverse image. -/
instance pull_colimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (pull C τ f) := (pull_exact C τ f).2.2

/-- Simultaneous K-injectives exist on the ringed sequence site. -/
theorem systems_kInjective (X : Scheme.{u}) :
    Abelian.HasKInjectiveResolutions (Modules C τ X) := by
  have := (Classical.choice (semilinearDerivedSections.{u + 1, u, u + 1}
    (ProEt.topology X) (coefficients C X) (transition C τ X))).systems.grothendieck
  exact Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian

attribute [instance] systems_kInjective

/-- Exact termwise inverse image on the ordinary derived category of systems. -/
def P {X Y : Scheme.{u}} (f : X ⟶ Y) : Derived C τ Y ⥤ Derived C τ X :=
  (pull C τ f).mapDerivedCategory

/-- Total derived direct image on systems. -/
def R {X Y : Scheme.{u}} (f : X ⟶ Y) : Derived C τ X ⥤ Derived C τ Y :=
  (push C τ f).rightDerivedFunctor

/-- The canonical derived adjunction of the actual ordinary system adjunction. -/
def adj {X Y : Scheme.{u}} (f : X ⟶ Y) : P C τ f ⊣ R C τ f :=
  (ordinaryAdj C τ f).mapDerivedCategoryRightDerivedAdjunction

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The direct-image compositor is determined by restriction along fibre-product pasting. -/
theorem pushComp_existsUnique {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃! d : push C τ f ⋙ push C τ g ≅ push C τ (f ≫ g),
      ∀ (N : Modules C τ X) (n : ℕ) (U : Z.ProEt)
        (x : ((push C τ f ⋙ push C τ g).obj N).val.obj (op (n, U))),
        (d.hom.app N).val.app (op (n, U)) x =
          N.val.map (Prod.mkHom (𝟙 n)
            ((MorphismProperty.Over.pullbackComp
              (P := @WeaklyEtale.{u}) (Q := ⊤) f g).hom.app U)).op x := by
  unfold push
  rw [coefficientMap_forget_eq, coefficientMap_forget_eq, coefficientMap_forget_eq]
  exact VaryingRing.modulePComp_existsUnique C τ f g

/-- The uniquely section-normalized ordinary direct-image compositor. -/
def pushComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (pushComp_existsUnique C τ f g).choose

/-- Inverse-image composition, conjugate to the specified sectionwise compositor. -/
def pullComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull C τ (f ≫ g) ≅ pull C τ g ⋙ pull C τ f :=
  (Adjunction.leftAdjointCompIso (ordinaryAdj C τ g) (ordinaryAdj C τ f)
    (ordinaryAdj C τ (f ≫ g)) (pushComp C τ f g)).symm

/-- Derived pullback composition is the localization of the ordinary compositor. -/
def pComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    P C τ (f ≫ g) ≅ P C τ g ⋙ P C τ f :=
  Functor.mapDerivedCategoryNatIso (pullComp C τ f g) ≪≫
    (Functor.mapDerivedCategoryCompIso (pull C τ g) (pull C τ f)).symm

/-- Direct-image composition is precisely the mate of inverse-image composition. -/
def sComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    R C τ f ⋙ R C τ g ≅ R C τ (f ≫ g) :=
  conjugateIsoEquiv ((adj C τ g).comp (adj C τ f)) (adj C τ (f ≫ g)) (pComp C τ f g)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The direct-image identity is fixed by restriction along the pullback identity. -/
theorem pushId_existsUnique (X : Scheme.{u}) :
    ∃! e : push C τ (𝟙 X) ≅ 𝟭 (Modules C τ X),
      ∀ (M : Modules C τ X) (n : ℕ) (U : X.ProEt)
        (x : ((push C τ (𝟙 X)).obj M).val.obj (op (n, U))),
        (e.hom.app M).val.app (op (n, U)) x =
          M.val.map (Prod.mkHom (𝟙 n)
            ((MorphismProperty.Over.pullbackId @WeaklyEtale.{u} ⊤ X).inv.app U)).op x := by
  unfold push
  rw [coefficientMap_forget_eq]
  exact VaryingRing.modulePId_existsUnique C τ X

/-- The unit-normalized inverse-image identity, localized from ordinary modules. -/
def pId (X : Scheme.{u}) : P C τ (𝟙 X) ≅ 𝟭 (Derived C τ X) :=
  Functor.mapDerivedCategoryNatIso (Adjunction.leftAdjointIdIso
    (ordinaryAdj C τ (𝟙 X)) (pushId_existsUnique C τ X).choose) ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- The derived direct-image identity is its adjunction conjugate. -/
def sId (X : Scheme.{u}) : R C τ (𝟙 X) ≅ 𝟭 (Derived C τ X) :=
  (conjugateIsoEquiv Adjunction.id (adj C τ (𝟙 X)) (pId C τ X)).symm

/-- Open inverse image is a right adjoint by localized-site extension by zero. -/
theorem openPull_isRightAdjoint {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (pull C τ j).IsRightAdjoint := by
  rw [pull_eq]
  exact VaryingRing.pull_isRightAdjoint C τ j

attribute [instance] openPull_isRightAdjoint

/-- Ordinary extension by zero, specified by its localization universal property. -/
abbrev extension {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (pull C τ j).leftAdjoint

/-- The ordinary open adjunction, retaining its actual unit and counit. -/
def ordinaryOpenAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    extension C τ j ⊣ pull C τ j := Adjunction.ofIsRightAdjoint _

private theorem extension_eq {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    extension C τ j = VaryingRing.extension C τ j := by
  unfold extension VaryingRing.extension
  congr 1
  exact pull_eq C τ j

/-- Open extension is exact, also for the empty open. -/
theorem extension_exact {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (extension C τ j).Additive ∧ PreservesFiniteLimits (extension C τ j) ∧
      PreservesFiniteColimits (extension C τ j) := by
  rw [extension_eq]
  exact VaryingRing.extension_exact C τ j

/-- Additivity of open extension. -/
instance extension_additive {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (extension C τ j).Additive := (extension_exact C τ j).1

/-- Left exactness of open extension. -/
instance extension_limits {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    PreservesFiniteLimits (extension C τ j) := (extension_exact C τ j).2.1

/-- Right exactness of open extension. -/
instance extension_colimits {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    PreservesFiniteColimits (extension C τ j) := (extension_exact C τ j).2.2

/-- Exact extension by zero on ordinary derived systems. -/
def J {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Derived C τ U ⥤ Derived C τ X :=
  (extension C τ j).mapDerivedCategory

/-- The open adjunction is the exact localization of the ordinary open adjunction. -/
def jAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    J C τ j ⊣ P C τ j :=
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction (ordinaryOpenAdj C τ j)

/-- Canonical open-extension composition is adjoint to pullback composition. -/
def jComp {U V X : Scheme.{u}} (j : U ⟶ V) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] : J C τ j ⋙ J C τ k ≅ J C τ (j ≫ k) :=
  Adjunction.leftAdjointCompIso (jAdj C τ j) (jAdj C τ k) (jAdj C τ (j ≫ k))
    (pComp C τ j k).symm

/-- Equal open immersions have equal open-extension functors `J`. -/
theorem J_congr {U X : Scheme.{u}} {f g : U ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) : J C τ f = J C τ g := by
  subst g
  rfl

/-- Open-extension transport along an equality of arrows. -/
def jCongr {U X : Scheme.{u}} {f g : U ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) : J C τ f ≅ J C τ g :=
  eqToIso (J_congr C τ h)

/-- The canonical open-extension identity, adjoint to inverse-image identity. -/
def jId (X : Scheme.{u}) : J C τ (𝟙 X) ≅ 𝟭 (Derived C τ X) :=
  Adjunction.leftAdjointIdIso (jAdj C τ (𝟙 X)) (pId C τ X)

/-- Canonical comparison of the two iterated inverse images around any commutative square. -/
noncomputable def squareP {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    P C τ i ⋙ P C τ r ≅ P C τ p ⋙ P C τ k :=
  (pComp C τ r i).symm ≪≫ eqToIso (congrArg (P C τ) h.symm) ≪≫ pComp C τ k p

/-- The inverse cartesian open comparison is defined by precisely the open-unit transpose. -/
noncomputable def betaInvApp {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (M : Derived C τ U) :
    (J C τ j').obj ((P C τ gU).obj M) ⟶ (P C τ g).obj ((J C τ j).obj M) :=
  ((jAdj C τ j').homEquiv _ _).symm
    ((P C τ gU).map ((jAdj C τ j).unit.app M) ≫
      (squareP C τ gU j' j g h).inv.app ((J C τ j).obj M))

/-- Naturality of the specified open-unit transpose. -/
theorem betaInvApp_naturality {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (M N : Derived C τ U) (f : M ⟶ N) :
    (P C τ gU ⋙ J C τ j').map f ≫ betaInvApp C τ gU j' j g h N =
      betaInvApp C τ gU j' j g h M ≫ (J C τ j ⋙ P C τ g).map f := by
  dsimp only [betaInvApp, Functor.comp_map]
  let t := Functor.whiskerRight (jAdj C τ j).unit (P C τ gU) ≫
    Functor.whiskerLeft (J C τ j) (squareP C τ gU j' j g h).inv
  exact (jAdj C τ j').homEquiv_naturality_right_square
    ((P C τ gU).map f) (t.app N) (t.app M)
    ((J C τ j ⋙ P C τ g).map f) (t.naturality f)

/-- The inverse comparison as a natural transformation with the specified transpose. -/
noncomputable def betaInv {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g) :
    P C τ gU ⋙ J C τ j' ⟶ J C τ j ⋙ P C τ g where
  app := betaInvApp C τ gU j' j g h
  naturality := betaInvApp_naturality C τ gU j' j g h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem P_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P C τ f = VaryingRing.G C τ f := by
  have ha := VaryingRing.pullAdditive C τ f
  have hl := VaryingRing.pullLimits C τ f
  have hc := VaryingRing.pullColimits C τ f
  exact exact_derived_congr (pull_eq C τ f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem J_eq {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    J C τ j = VaryingRing.J C τ j := by
  have ha := VaryingRing.extensionAdditive C τ j
  have hl := VaryingRing.extensionLimits C τ j
  have hc := VaryingRing.extensionColimits C τ j
  exact exact_derived_congr (extension_eq C τ j)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem R_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R C τ f = VaryingRing.P C τ f := by
  have ha := VaryingRing.push_additive C τ f
  exact right_derived_congr (push_eq C τ f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The open-extension unit is invertible. -/
theorem jAdj_unit_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (jAdj C τ j).unit := by
  have : (VaryingRing.pull C τ j).IsRightAdjoint :=
    VaryingRing.pull_isRightAdjoint C τ j
  have hu : IsIso (ordinaryOpenAdj C τ j).unit :=
    chosen_unit_isIso_congr (pull C τ j) (VaryingRing.pull C τ j)
      (pull_eq C τ j) (VaryingRing.moduleJAdj_unit_isIso C τ j)
  have hf := (jAdj C τ j).fullyFaithfulLOfCompIsoId
    (Functor.mapDerivedCategoryCompIso (extension C τ j) (pull C τ j) ≪≫
      Functor.mapDerivedCategoryNatIso (asIso (ordinaryOpenAdj C τ j).unit).symm ≪≫
        Functor.mapDerivedCategoryIdIso _)
  have := hf.full
  have := hf.faithful
  infer_instance

/-- The unit-normalized comparison is invertible for a cartesian open square and
arbitrary B. -/
theorem betaInv_isIso {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (hsq : IsPullback gU j' j g) : IsIso (betaInv C τ gU j' j g h) := by
  have hu : IsIso (jAdj C τ j).unit := jAdj_unit_isIso C τ j
  have := jAdj_unit_isIso C τ j'
  let ff := (jAdj C τ j').fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have hi (M : Derived C τ U) : IsIso ((betaInv C τ gU j' j g h).app M) := by
    have := VaryingRing.derived_basechange_counit C τ gU j' j g h hsq M
    have hm := (VaryingRing.jAdj C τ j').mem_essImage_of_counit_isIso
      ((VaryingRing.G C τ g).obj ((VaryingRing.J C τ j).obj M))
    have hm' : (J C τ j').essImage ((P C τ g).obj ((J C τ j).obj M)) := by
      rw [P_eq, J_eq, J_eq]
      exact hm
    have := (jAdj C τ j').isIso_counit_app_iff_mem_essImage.mpr hm'
    change IsIso (betaInvApp C τ gU j' j g h M)
    unfold betaInvApp
    rw [Adjunction.homEquiv_counit]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- Cartesian open base change, oriented as G_g j_! → j'_! G_gU. -/
noncomputable def beta {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (hsq : IsPullback gU j' j g) : J C τ j ⋙ P C τ g ≅ P C τ gU ⋙ J C τ j' :=
  (@asIso _ _ _ _ (betaInv C τ gU j' j g h)
    (betaInv_isIso C τ gU j' j g h hsq)).symm

/-- The canonical map from open extension to direct image is the counit mate of the
inverse open unit. -/
noncomputable def openToS {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    J C τ j ⟶ R C τ j :=
  (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft (J C τ j) (adj C τ j).unit ≫
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (@inv _ _ _ _ (jAdj C τ j).unit (jAdj_unit_isIso C τ j)) (R C τ j) ≫
          (Functor.leftUnitor _).hom

/-- For a clopen immersion the canonical open-to-direct-image comparison is invertible. -/
theorem openToS_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [IsClosedImmersion j] : IsIso (openToS C τ j) := by
  obtain ⟨e⟩ := VaryingRing.derived_clopen_iso C τ j
  have he : Nonempty (J C τ j ≅ R C τ j) := by
    rw [J_eq, R_eq]
    exact ⟨e⟩
  obtain ⟨e⟩ := he
  have hu : IsIso (jAdj C τ j).unit := jAdj_unit_isIso C τ j
  let ff := (jAdj C τ j).fullyFaithfulLOfIsIsoUnit
  let fp := ff.ofIso e
  have := fp.full
  have := fp.faithful
  have hi (M : Derived C τ U) : IsIso ((openToS C τ j).app M) := by
    have hunit : IsIso ((adj C τ j).unit.app ((J C τ j).obj M)) :=
      (adj C τ j).isIso_unit_app_of_iso (e.app M)
    have hinv : IsIso ((inv (jAdj C τ j).unit).app M) := by infer_instance
    have himap : IsIso ((R C τ j).map ((inv (jAdj C τ j).unit).app M)) := by
      infer_instance
    let e' := asIso ((adj C τ j).unit.app ((J C τ j).obj M)) ≪≫
      (R C τ j).mapIso (asIso ((inv (jAdj C τ j).unit).app M))
    have he' : (openToS C τ j).app M = e'.hom := by
      simp only [openToS, NatTrans.comp_app, Functor.rightUnitor_inv_app,
        Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
        Functor.leftUnitor_hom_app, Category.id_comp, e',
        Iso.trans_hom, asIso_hom, Functor.mapIso_hom]
      erw [Category.comp_id]
    rw [he']
    exact e'.isIso_hom
  exact NatIso.isIso_of_isIso_app _

/-- The intrinsic clopen component projection, with no arbitrary splitting choice. -/
noncomputable def pi {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s]
    [IsClosedImmersion s] : 𝟭 (Derived C τ X) ⟶ P C τ s ⋙ J C τ s :=
  (adj C τ s).unit ≫ Functor.whiskerLeft (P C τ s)
    (@inv _ _ _ _ (openToS C τ s) (openToS_isIso C τ s))

/-- The normalized non-cartesian open comparison uses beta and the intrinsic clopen
projection, followed by the open and pullback compositors. -/
noncomputable def alpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : J C τ i ⋙ P C τ p ⟶ P C τ r ⋙ J C τ k :=
  (beta C τ (pullback.snd p i) (pullback.fst p i) i p
    (pullback.condition.symm) (IsPullback.of_hasPullback p i).flip).hom ≫
  Functor.whiskerRight (Functor.whiskerLeft (P C τ (pullback.snd p i))
    (pi C τ (StrictTower.squareLift k r p i h))) (J C τ (pullback.fst p i)) ≫
  Functor.whiskerRight
    (Functor.associator (P C τ (pullback.snd p i)) (P C τ (StrictTower.squareLift k r p i h))
      (J C τ (StrictTower.squareLift k r p i h))).inv (J C τ (pullback.fst p i)) ≫
  (Functor.associator (P C τ (pullback.snd p i) ⋙ P C τ (StrictTower.squareLift k r p i h))
    (J C τ (StrictTower.squareLift k r p i h)) (J C τ (pullback.fst p i))).hom ≫
  Functor.whiskerLeft (P C τ (pullback.snd p i) ⋙ P C τ (StrictTower.squareLift k r p i h))
    ((jComp C τ (StrictTower.squareLift k r p i h) (pullback.fst p i)).hom ≫
      (jCongr C τ (pullback.lift_fst k r h)).hom) ≫
  Functor.whiskerRight
    ((pComp C τ (StrictTower.squareLift k r p i h) (pullback.snd p i)).inv ≫
      (eqToIso (congrArg (P C τ) (pullback.lift_snd k r h))).hom) (J C τ k)

/-- The proper/open comparison is exactly the proper-adjunction mate of alpha. -/
noncomputable def gamma {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : R C τ r ⋙ J C τ i ⟶ J C τ k ⋙ R C τ p :=
  mateEquiv (adj C τ r) (adj C τ p) (alpha C τ k r p i h)

/-- The base-change arrow is the mate of the canonical pullback-square isomorphism. -/
noncomputable def exchange {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    R C τ p ⋙ P C τ i ⟶ P C τ k ⋙ R C τ r :=
  mateEquiv (adj C τ p) (adj C τ r) (squareP C τ k r p i h).hom

/-- The cartesian open comparison conjugated as an isomorphism of right adjoints. -/
def cartesianConjugate {W S T : Scheme.{u}} (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion i] :
    R C τ p ⋙ P C τ i ≅ P C τ (pullback.fst p i) ⋙ R C τ (pullback.snd p i) :=
  conjugateIsoEquiv ((jAdj C τ i).comp (adj C τ p))
    ((adj C τ (pullback.snd p i)).comp (jAdj C τ (pullback.fst p i)))
    (beta C τ (pullback.snd p i) (pullback.fst p i) i p
      pullback.condition.symm (IsPullback.of_hasPullback p i).flip).symm

/-- Restricting k-extension to the pulled-back open leaves s-extension. -/
def restrictFactor {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    J C τ k ⋙ P C τ (pullback.fst p i) ≅ J C τ (StrictTower.squareLift k r p i h) :=
  Functor.isoWhiskerRight
    ((jComp C τ (StrictTower.squareLift k r p i h) (pullback.fst p i)) ≪≫
      jCongr C τ (pullback.lift_fst k r h)).symm (P C τ (pullback.fst p i)) ≪≫
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft (J C τ (StrictTower.squareLift k r p i h))
    (@asIso _ _ _ _ (jAdj C τ (pullback.fst p i)).unit
      (jAdj_unit_isIso C τ (pullback.fst p i))).symm ≪≫
  Functor.rightUnitor _

/-- The specified lambda isomorphism: conjugate beta, inverse open unit, the clopen
section comparison, and direct-image composition. No isomorphism is chosen after
coefficient evaluation. -/
def lambda {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : (J C τ k ⋙ R C τ p) ⋙ P C τ i ≅ R C τ r :=
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft (J C τ k) (cartesianConjugate C τ p i) ≪≫
  (Functor.associator _ _ _).symm ≪≫
  Functor.isoWhiskerRight (restrictFactor C τ k r p i h) (R C τ (pullback.snd p i)) ≪≫
  Functor.isoWhiskerRight
    (@asIso _ _ _ _ (openToS C τ (StrictTower.squareLift k r p i h))
      (openToS_isIso C τ (StrictTower.squareLift k r p i h))) (R C τ (pullback.snd p i)) ≪≫
  sComp C τ (StrictTower.squareLift k r p i h) (pullback.snd p i) ≪≫
  eqToIso (congrArg (R C τ) (pullback.lift_snd k r h))

private theorem conjugate_transport
    {A B I : Type*} [Category A] [Category B]
    (L : I → A ⥤ B) (R₀ : I → B ⥤ A) (a : ∀ i, L i ⊣ R₀ i)
    {L' : A ⥤ B} {R' : B ⥤ A} (a' : L' ⊣ R')
    {i j : I} (e : i = j) (d : L i ≅ L') :
    conjugateIsoEquiv a' (a j) (eqToIso (congrArg L e.symm) ≪≫ d) =
      conjugateIsoEquiv a' (a i) d ≪≫ eqToIso (congrArg R₀ e) := by
  cases e
  simp

private theorem conjugate_transport_inverse
    {A B I : Type*} [Category A] [Category B]
    (L : I → A ⥤ B) (R₀ : I → B ⥤ A) (a : ∀ i, L i ⊣ R₀ i)
    {L' : A ⥤ B} {R' : B ⥤ A} (a' : L' ⊣ R')
    {i j : I} (e : i = j) (d : L i ≅ L') :
    conjugateIsoEquiv a' (a j) (d.symm ≪≫ eqToIso (congrArg L e)).symm =
      conjugateIsoEquiv a' (a i) d ≪≫ eqToIso (congrArg R₀ e) := by
  cases e
  simp

private theorem sComp_congr {V X S : Scheme.{u}} (s : V ⟶ X) (q : X ⟶ S)
    (r : V ⟶ S) (h : s ≫ q = r) :
    conjugateIsoEquiv ((adj C τ q).comp (adj C τ s)) (adj C τ r)
        ((pComp C τ s q).symm ≪≫ eqToIso (congrArg (P C τ) h)).symm =
      sComp C τ s q ≪≫ eqToIso (congrArg (R C τ) h) := by
  simpa only [sComp] using
    conjugate_transport_inverse (P C τ) (R C τ) (fun f ↦ adj C τ f)
      ((adj C τ q).comp (adj C τ s)) h (pComp C τ s q)

private theorem alpha_eq_projection_square {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    alpha C τ k r p i h = projection_square
      (beta C τ (pullback.snd p i) (pullback.fst p i) i p pullback.condition.symm
        (IsPullback.of_hasPullback p i).flip)
      (jComp C τ (StrictTower.squareLift k r p i h) (pullback.fst p i) ≪≫
        jCongr C τ (pullback.lift_fst k r h))
      (((pComp C τ (StrictTower.squareLift k r p i h) (pullback.snd p i)).symm ≪≫
        eqToIso (congrArg (P C τ) (pullback.lift_snd k r h))).symm)
      (pi C τ (StrictTower.squareLift k r p i h)) := by
  rfl

/-- Gamma is the open adjunct of inverse lambda, and its restriction is inverse lambda
under the open unit. -/
theorem gamma_adjunct {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : Derived C τ V) :
    (jAdj C τ i).homEquiv _ _ ((gamma C τ k r p i h).app M) =
      (lambda C τ k r p i h).inv.app M ∧
    (jAdj C τ i).unit.app ((R C τ r).obj M) ≫
      (P C τ i).map ((gamma C τ k r p i h).app M) ≫
        (lambda C τ k r p i h).hom.app M = 𝟙 _ := by
  let s := StrictTower.squareLift k r p i h
  let b := pullback.fst p i
  let q := pullback.snd p i
  let d : J C τ s ⋙ J C τ b ≅ J C τ k :=
    jComp C τ s b ≪≫ jCongr C τ (pullback.lift_fst k r h)
  let e : P C τ r ≅ P C τ q ⋙ P C τ s :=
    ((pComp C τ s q).symm ≪≫
      eqToIso (congrArg (P C τ) (pullback.lift_snd k r h))).symm
  let β := beta C τ q b i p pullback.condition.symm
    (IsPullback.of_hasPullback p i).flip
  let t : J C τ s ≅ R C τ s :=
    @asIso _ _ _ _ (openToS C τ s) (openToS_isIso C τ s)
  let f : (P C τ q).obj ((R C τ r).obj M) ⟶ (J C τ s).obj M :=
    (pi C τ s).app _ ≫ (J C τ s).map
      (e.inv.app ((R C τ r).obj M) ≫ (adj C τ r).counit.app M)
  have := jAdj_unit_isIso C τ b
  have hα : β.inv.app ((R C τ r).obj M) ≫
      (alpha C τ k r p i h).app ((R C τ r).obj M) ≫
      (J C τ k).map ((adj C τ r).counit.app M) =
        (J C τ b).map f ≫ d.hom.app M := by
    exact projection_square_formula_of_eq β d e (pi C τ s) (alpha C τ k r p i h)
      (alpha_eq_projection_square C τ k r p i h) ((R C τ r).obj M) M
      ((adj C τ r).counit.app M)
  have hf : f ≫ t.hom.app M =
      (adj C τ s).unit.app _ ≫ (R C τ s).map
        (e.inv.app ((R C τ r).obj M) ≫ (adj C τ r).counit.app M) := by
    have hn := t.hom.naturality
      (e.inv.app ((R C τ r).obj M) ≫ (adj C τ r).counit.app M)
    simp only [Functor.id_obj] at hn
    dsimp only [f, pi, NatTrans.comp_app, Functor.whiskerLeft_app]
    simp only [Category.assoc]
    change (adj C τ s).unit.app _ ≫ t.inv.app _ ≫
      (J C τ s).map _ ≫ t.hom.app M = _
    simp only [Functor.comp_obj] at hn ⊢
    rw [hn, ← Category.assoc (t.inv.app _), t.inv_hom_id_app, Category.id_comp]
  have hcomp : conjugateIsoEquiv ((adj C τ q).comp (adj C τ s)) (adj C τ r) e =
      sComp C τ s q ≪≫ eqToIso (congrArg (R C τ) (pullback.lift_snd k r h)) := by
    exact sComp_congr C τ s q r (pullback.lift_snd k r h)
  have hComparison : lambda C τ k r p i h = adjunct_comparison (adj C τ p) (jAdj C τ i)
      (jAdj C τ b) (adj C τ q) β d t
      (sComp C τ s q ≪≫ eqToIso (congrArg (R C τ) (pullback.lift_snd k r h))) := by
    rfl
  have hmain : (jAdj C τ i).homEquiv _ _ ((gamma C τ k r p i h).app M) ≫
      (lambda C τ k r p i h).hom.app M = 𝟙 _ := by
    rw [hComparison]
    exact adjunct_comparison_identity (adj C τ r) (adj C τ p) (jAdj C τ i)
      (jAdj C τ b) (adj C τ q) (adj C τ s) β d e t
      (sComp C τ s q ≪≫ eqToIso (congrArg (R C τ) (pullback.lift_snd k r h)))
      hcomp (alpha C τ k r p i h) M f hα hf
  exact homEquiv_iso_inverse (jAdj C τ i) ((gamma C τ k r p i h).app M)
    ((lambda C τ k r p i h).app M) hmain

-- Coherence statements use the types of these comparisons, not their constructions.
attribute [local irreducible] alpha gamma

end AlgebraicGeometry.ProEtale.SemilinearProperOpen

namespace SemilinearProperOpenCoreAliases
private alias map_iso_transport :=
  _root_.map_iso_transport
private alias tower_normalized_transport :=
  _root_.tower_normalized_transport
private alias tower_iso_ext_sections :=
  _root_.tower_iso_ext_sections
private alias normalized_function :=
  _root_.normalized_function
private alias isIso_of_heq :=
  _root_.isIso_of_heq
private alias normalized_square :=
  _root_.normalized_square
private alias chosen_unit_isIso_congr :=
  _root_.chosen_unit_isIso_congr
private alias exact_derived_congr :=
  _root_.exact_derived_congr
private alias right_derived_congr :=
  _root_.right_derived_congr
private alias constant_diagram_square :=
  _root_.constant_diagram_square
private alias constant_diagram_square_hom_app :=
  _root_.constant_diagram_square_hom_app
private alias constant_diagram_square_inv_app :=
  _root_.constant_diagram_square_inv_app
private alias mate_of_unit_normalization :=
  _root_.mate_of_unit_normalization
private alias constant_diagram_mate :=
  _root_.constant_diagram_mate
private alias composite_conjugate_inv :=
  _root_.composite_conjugate_inv
private alias adjunct_comparison :=
  _root_.adjunct_comparison
private alias adjunct_comparison_identity :=
  _root_.adjunct_comparison_identity
private alias homEquiv_iso_inverse :=
  _root_.homEquiv_iso_inverse
private alias projection_square :=
  _root_.projection_square
private alias projection_square_formula :=
  _root_.projection_square_formula
private alias projection_square_formula_of_eq :=
  _root_.projection_square_formula_of_eq
private alias ordinary_restriction_existsUnique :=
  _root_.ordinary_restriction_existsUnique
private alias derived_square_conjugate :=
  _root_.derived_square_conjugate
private alias derived_iso_symm_inv :=
  _root_.derived_iso_symm_inv
private alias derived_constant_square_comp :=
  _root_.derived_constant_square_comp
private alias derived_constant_square_inverse :=
  _root_.derived_constant_square_inverse
private alias coefficientMap_forget_eq :=
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.coefficientMap_forget_eq
private alias push_eq :=
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.push_eq
private alias pull_eq :=
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.pull_eq
private alias extension_eq :=
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.extension_eq
private alias P_eq :=
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.P_eq
private alias J_eq :=
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.J_eq
private alias R_eq :=
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.R_eq
private alias conjugate_transport :=
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.conjugate_transport
private alias conjugate_transport_inverse :=
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.conjugate_transport_inverse
private alias sComp_congr :=
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.sComp_congr
private alias alpha_eq_projection_square :=
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.alpha_eq_projection_square
end SemilinearProperOpenCoreAliases

end ProofEnvironment
