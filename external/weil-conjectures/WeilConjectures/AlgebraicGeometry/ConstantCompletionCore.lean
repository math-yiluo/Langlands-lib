/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotients
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback

/-!
# Constant coefficient completion: Core

Scalar changes, finite and derived comparisons, quotient-tower completion and Koszul
presentations.

Part of the split of `Sheaf.Paper.ConstantCompletionEquivalence`.
Source: Stacks Project, Tags 093M, 099I, 099L, 099M, 0A0E, 06YY and 0940
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)

attribute [local irreducible] completed
variable {J A I}

section CoefficientIdeal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem extension_eq_of_span {R B : Sheaf J CommRingCat.{u}}
    (φ : R ⟶ B) (K : RingedSiteIdeal R) (L : RingedSiteIdeal B)
    (h : ∀ U, L.sections U =
      Ideal.span (Set.range (fun a : K.sections U ↦ φ.hom.app (op U) a))) :
    K.extension φ = L := by
  apply ((K.existsUnique_extension φ).unique ?_ ?_)
  · exact (K.existsUnique_extension φ).exists.choose_spec
  · intro U b
    constructor
    · intro hb
      refine ⟨⊤, J.top_mem _, ?_⟩
      intro V g _
      rw [← h V]
      exact L.restriction g b hb
    · rintro ⟨S, hS, hb⟩
      exact L.local_mem U b S hS (fun V g hg ↦ by rw [h V]; exact hb V g hg)

private theorem coefficientKernel_extension (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    (kernelIdeal (quotient J A I 0)).extension (coefficientMap J A I) =
      kernelIdeal (projection J A I 0) := by
  let φ := coefficientMap J A I
  let K := kernelIdeal (quotient J A I 0)
  let L := kernelIdeal (projection J A I 0)
  apply extension_eq_of_span φ K L
  intro U
  have hK : K.sections U = RingHom.ker ((quotient J A I 0).hom.app (op U)).hom :=
    (kernelIdeal_existsUnique (quotient J A I 0)).exists.choose_spec U
  have hL : L.sections U = RingHom.ker ((projection J A I 0).hom.app (op U)).hom :=
    (kernelIdeal_existsUnique (projection J A I 0)).exists.choose_spec U
  rw [hL, ((flat_and_quotients J A I).2.1 0 U).2]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    apply Ideal.subset_span
    refine ⟨⟨(constantSection (J := J) a.val).val (op U), ?_⟩, rfl⟩
    rw [hK, ((flat_and_quotients J A I).2.2 0 U).2]
    exact Ideal.subset_span ⟨a, rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    have ha : a.val ∈ Ideal.span (Set.range (fun b : ↥(I ^ (0 + 1)) ↦
        (constantSection (J := J) (b : A)).val (op U))) := by
      rw [← ((flat_and_quotients J A I).2.2 0 U).2, ← hK]
      exact a.property
    change φ.hom.app (op U) a.val ∈ _
    have hle : Ideal.span (Set.range (fun b : ↥(I ^ (0 + 1)) ↦
        (constantSection (J := J) (b : A)).val (op U))) ≤
        Ideal.comap (φ.hom.app (op U)).hom
          (Ideal.span (Set.range (fun b : ↥(I ^ (0 + 1)) ↦
            (algebraSection φ b).val (op U)))) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨b, rfl⟩
      exact Ideal.subset_span ⟨b, rfl⟩
    exact hle ha

private theorem coefficientKernel_quotient (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) :
    (kernelIdeal (quotient J A I 0)).IsQuotientIso (coefficientMap J A I) := by
  let φ := coefficientMap J A I
  let K := kernelIdeal (quotient J A I 0)
  have he := coefficientKernel_extension (J := J) A I
  have hk (U : C) : K.sections U =
      RingHom.ker ((quotient J A I 0).hom.app (op U)).hom :=
    (kernelIdeal_existsUnique (quotient J A I 0)).exists.choose_spec U
  have hl (U : C) : (K.extension φ).sections U =
      RingHom.ker ((projection J A I 0).hom.app (op U)).hom := by
    rw [he]
    exact (kernelIdeal_existsUnique (projection J A I 0)).exists.choose_spec U
  have hc (U : C) (a : (constant J A).obj.obj (op U)) :
      (projection J A I 0).hom.app (op U) (φ.hom.app (op U) a) =
        (quotient J A I 0).hom.app (op U) a := by
    exact congrArg (fun f ↦ f.hom.app (op U) a)
      (limit.lift_π (quotientCone J A I) (op 0))
  constructor
  · intro U a
    rw [hl, hk]
    change (projection J A I 0).hom.app (op U) (φ.hom.app (op U) a) = 0 ↔
      (quotient J A I 0).hom.app (op U) a = 0
    rw [hc]
  · intro U b
    refine ⟨⊤, J.top_mem _, ?_⟩
    intro V g _
    obtain ⟨a, ha⟩ := ((flat_and_quotients J A I).2.2 0 V).1
      ((projection J A I 0).hom.app (op V) ((completed J A I).obj.map g.op b))
    refine ⟨a, ?_⟩
    rw [hl]
    change (projection J A I 0).hom.app (op V)
      ((completed J A I).obj.map g.op b - φ.hom.app (op V) a) = 0
    rw [map_sub, hc, ha, sub_self]
private theorem ideal_generated_global_sections
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R)
    (r : ℕ) (b : Fin r → (R.obj ⋙ CategoryTheory.forget CommRingCat).sections)
    (hs : ∀ U : C, I.sections U =
      Ideal.span (Set.range (fun i ↦ (b i).val (op U)))) :
    ∃ σ : I.module.GeneratingSections, ∃ e : σ.I ≃ Fin r,
      ∀ i : σ.I, SheafOfModules.sectionsMap I.inclusion (σ.s i) = b (e i) := by
  classical
  let s (i : ULift.{u} (Fin r)) : I.module.sections :=
    { val := fun U ↦ ⟨(b i.down).val U, by
        rw [hs]
        exact Ideal.subset_span ⟨i.down, rfl⟩⟩
      property := by
        intro U V f
        apply Subtype.ext
        exact (b i.down).property f }
  let π := I.module.freeHomEquiv.symm s
  have hπ : Epi π := by
    constructor
    intro M f g hfg
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let x' : I.sections U.unop := x
    have hx : (x' : R.obj.obj U) ∈
        Ideal.span (Set.range (fun i ↦ (b i).val U)) := by
      rw [← hs]
      exact x'.property
    have hgen (i : ULift.{u} (Fin r)) :
        f.val.app U (s i |>.val U) = g.val.app U (s i |>.val U) := by
      have h := congrArg (fun k ↦
        (SheafOfModules.sectionsMap k (SheafOfModules.freeSection i)).val U) hfg
      dsimp only [π] at h
      have h' := h
      simp only [SheafOfModules.sectionsMap_comp,
        SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection] at h
      exact h
    have hind : ∀ (y : R.obj.obj U),
        y ∈ Ideal.span (Set.range (fun i ↦ (b i).val U)) →
        ∀ hy : y ∈ I.sections U.unop,
          f.val.app U ⟨y, hy⟩ = g.val.app U ⟨y, hy⟩ := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
          rcases hy with ⟨i, rfl⟩
          intro hi
          exact hgen ⟨i⟩
      | zero =>
          intro hzero
          change f.val.app U 0 = g.val.app U 0
          simp only [map_zero]
      | add y z hy hz ihy ihz =>
          intro hsum
          change f.val.app U (⟨y, by rw [hs]; exact hy⟩ +
              ⟨z, by rw [hs]; exact hz⟩) = _
          rw [map_add, ihy, ihz]
          exact (map_add (g.val.app U).hom _ _).symm
      | smul c y hy ih =>
          intro hprod
          change f.val.app U (c • ⟨y, by rw [hs]; exact hy⟩) = _
          rw [map_smul, ih]
          exact (map_smul (g.val.app U).hom c _).symm
    exact hind x'.val hx x'.property
  refine ⟨{ I := ULift.{u} (Fin r), s := s, epi := hπ }, Equiv.ulift, ?_⟩
  intro i
  rfl

private def overIdeal {R : Sheaf J CommRingCat.{u}} (K : RingedSiteIdeal R) (U : C) :
    RingedSiteIdeal (R.over U) where
  sections V := K.sections V.left
  restriction g a ha := K.restriction g.left a ha
  local_mem V a S hS ha :=
    K.local_mem V.left a (Sieve.overEquiv V S) ((J.mem_over_iff S).mp hS)
      (fun W g hg ↦ ha (Over.mk (g ≫ V.hom)) (Over.homMk g)
        ((Sieve.overEquiv_iff S g).mp hg))

private theorem ideal_finiteType_of_span {R : Sheaf J CommRingCat.{u}}
    (K : RingedSiteIdeal R) (r : ℕ)
    (b : Fin r → (R.obj ⋙ CategoryTheory.forget CommRingCat).sections)
    (hs : ∀ U : C, K.sections U = Ideal.span (Set.range (fun i ↦ (b i).val (op U)))) :
    SheafOfModules.IsFiniteType.{u, u, u} K.module := by
  let bs (U : C) (i : Fin r) :
      ((R.over U).obj ⋙ CategoryTheory.forget CommRingCat).sections :=
    { val := fun V ↦ (b i).val (op V.unop.left)
      property := fun f ↦ (b i).property ((Over.forget U).op.map f) }
  have hg (U : C) := ideal_generated_global_sections (R.over U) (overIdeal K U)
    r (bs U) (fun V ↦ hs V.left)
  let σ (U : C) : (K.module.over U).GeneratingSections := (hg U).choose
  have hσ (U : C) : (σ U).IsFiniteType := by
    obtain ⟨e, _⟩ := (hg U).choose_spec
    exact ⟨Finite.of_equiv (Fin r) e.symm⟩
  let q : SheafOfModules.LocalGeneratorsData.{u} K.module :=
    { I := C
      X := id
      coversTop := fun _ ↦ GrothendieckTopology.covering_of_eq_top J (by simp)
      generators := σ }
  constructor
  refine ⟨q, ?_⟩
  exact { isFiniteType := hσ }

private theorem span_subtype_images
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (I : Ideal A) {ι : Type*} (a : ι → A) (ha : Ideal.span (Set.range a) = I) :
    Ideal.span (Set.range (fun x : I ↦ f x)) =
      Ideal.span (Set.range (fun i ↦ f (a i))) := by
  have h : Ideal.span (Set.range (fun x : I ↦ f x)) = Ideal.map f I := by
    unfold Ideal.map
    congr 1
    ext x
    simp only [Set.mem_range, Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  rw [h, ← ha, Ideal.map_span]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨a i, ⟨i, rfl⟩, rfl⟩

private theorem coefficientKernel_finiteType (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) :
    SheafOfModules.IsFiniteType.{u, u, u} (kernelIdeal (quotient J A I 0)).module := by
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    I.fg_of_isNoetherianRing
  apply ideal_finiteType_of_span (kernelIdeal (quotient J A I 0)) r
    (fun i ↦ constantSection (J := J) (a i))
  intro U
  have hk : (kernelIdeal (quotient J A I 0)).sections U =
      RingHom.ker ((quotient J A I 0).hom.app (op U)).hom :=
    (kernelIdeal_existsUnique (quotient J A I 0)).exists.choose_spec U
  rw [hk, ((flat_and_quotients J A I).2.2 0 U).2]
  let f : A →+* (constant J A).obj.obj (op U) :=
    ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app (op U)).hom
  exact span_subtype_images f (I ^ (0 + 1)) a
    (by simpa only [Nat.zero_add, pow_one] using ha)

end CoefficientIdeal

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction along the canonical completion map gives the asserted equivalence.
Source: Stacks 099I and the opening of 099L
(auxiliary; not a blueprint node).
Proof: flat_and_quotients gives flatness and the quotient isomorphism modulo I. The
constant ideal is finite type since A is Noetherian. Apply the general flat ringed-ideal
complete equivalence. The kernel ideals in IsComplete are exactly I and I times the
completed ring by the preceding sections formulas. Its ambient functor is dres. -/
theorem equivalence (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    ∃ e : ObjectProperty.FullSubcategory (IsComplete (projection J A I 0)) ≌
        ObjectProperty.FullSubcategory (IsComplete (quotient J A I 0)),
      Nonempty (e.functor ⋙ ObjectProperty.ι (IsComplete (quotient J A I 0)) ≅
        ObjectProperty.ι (IsComplete (projection J A I 0)) ⋙ dres (coefficientMap J A I)) := by
  let := HasDerivedCategory.standard (Mod (constant J A))
  let := HasDerivedCategory.standard (Mod (completed J A I))
  let (U : C) := HasDerivedCategory.standard (Mod ((constant J A).over U))
  let (U : C) := HasDerivedCategory.standard (Mod ((completed J A I).over U))
  have h := flat_ringed_ideal_complete_equivalence
    (coefficientMap J A I) (kernelIdeal (quotient J A I 0))
    (coefficientKernel_finiteType (J := J) A I) (flat_and_quotients J A I).1
    (coefficientKernel_quotient (J := J) A I)
  rw [coefficientKernel_extension (J := J) A I] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Sectionwise scalar extension before sheafification, with the standard module maps. -/
private def scalarPresheaf {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) :
    Mod R ⥤ PresheafOfModules.{u} (siteModuleRings S).obj where
  obj := SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ
  map f :=
    { app := fun U ↦ (ModuleCat.extendScalars (φ.hom.app U).hom).map (f.val.app U)
      naturality := SheafOfModules.changeOfRingsHom_naturality φ _ f }
  map_id M := by
    ext U : 1
    exact (ModuleCat.extendScalars (φ.hom.app U).hom).map_id _
  map_comp f g := by
    ext U : 1
    exact (ModuleCat.extendScalars (φ.hom.app U).hom).map_comp _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ordinary scalar-extension map respects identities and composition.
Source: Stacks 06YY (auxiliary; not a blueprint node).
Proof: before sheafification these are the identity and composition laws of the
sectionwise extension-of-scalars functors. Sheafification preserves those equations. -/
theorem change_laws {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) :
    (∀ M : Mod R, SheafOfModules.changeOfRingsHom.{u, u, u} φ M (𝟙 M) = 𝟙 _) ∧
    (∀ (M N L : Mod R) (f : M ⟶ N) (g : N ⟶ L),
      SheafOfModules.changeOfRingsHom.{u, u, u} φ M (f ≫ g) =
        SheafOfModules.changeOfRingsHom.{u, u, u} φ M f ≫
          SheafOfModules.changeOfRingsHom.{u, u, u} φ N g) := by
  let F := scalarPresheaf φ ⋙
    PresheafOfModules.sheafification (𝟙 (siteModuleRings S).obj)
  exact ⟨fun M ↦ F.map_id M, fun _ _ _ f g ↦ F.map_comp f g⟩

/-- The additive ordinary scalar extension, with the recorded objects and maps.
Source: Stacks 06YY (auxiliary; not a blueprint node). -/
def change {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) : Mod R ⥤ Mod S where
  obj := SheafOfModules.changeOfRings.{u, u, u} φ
  map := SheafOfModules.changeOfRingsHom.{u, u, u} φ _
  map_id := (change_laws φ).1
  map_comp f g := (change_laws φ).2 _ _ _ f g

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Ordinary scalar extension is additive.
Source: Stacks 06YY (auxiliary; not a blueprint node).
Proof: sectionwise scalar extension is additive by its ordinary module adjunction.
Module sheafification is additive by its adjunction to additive restriction and forgetful
functors. Their composite has exactly the objects and maps defining change. -/
theorem change_additive {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) :
    (change φ).Additive := by
  have (U : Cᵒᵖ) : (ModuleCat.extendScalars (φ.hom.app U).hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).left_adjoint_additive
  have : (scalarPresheaf φ).Additive := by
    constructor
    intro M N f g
    ext U : 1
    exact (ModuleCat.extendScalars (φ.hom.app U).hom).map_add
  have : (PresheafOfModules.sheafification (𝟙 (siteModuleRings S).obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings S).obj)).left_adjoint_additive
  let F := scalarPresheaf φ ⋙
    PresheafOfModules.sheafification (𝟙 (siteModuleRings S).obj)
  constructor
  intro M N f g
  exact F.map_add

attribute [instance] change_additive

set_option genSizeOf false in
set_option genInjectivity false in
/-- The derived scalar-extension universal property and K-flat computation.
This packages an existing notion, with its universal comparison retained.
Source: Stacks 06YY (auxiliary; not a blueprint node). -/
structure DerivedExtension {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) where
  functor : D R ⥤ D S
  comparison : Q R ⋙ functor ⟶
    (change φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q S
  universal : functor.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (Mod R) (ComplexShape.up ℤ))
  computation : ∀ P : Cx R, P.IsKFlatTensor → IsIso (comparison.app P)

/-- The recorded derived change-of-rings theorem supplies this universally specified pair.
Source: Stacks 06YY (auxiliary; not a blueprint node).
Proof: use derivedChangeOfRingsIndependentCoefficients with the standard localizations.
Identify its ordinary tensor witness with change on objects and maps. Compose its
homotopy counit with quotientCompQhIso and mapHomotopyCategoryFactors. The composite
localization universal property gives the complex-level universal property, and its
K-flat computation transports across those factorization isomorphisms. -/
theorem derivedExtension_exists {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) :
    Nonempty (DerivedExtension φ) := by
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod S)
  obtain ⟨E, hobj, hmap, hpres, T, hpw, ε, huniv, htri, hcomp⟩ :=
    (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel φ).some
  have hE : E = change φ := Functor.ext hobj (fun _ _ f ↦ hmap f)
  subst E
  exact ⟨{ functor := T
           comparison := ε
           universal := huniv
           computation := fun P hP ↦ hcomp P
             ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP) }⟩

/-- Select the universal derived pair, which is determined up to its unique normalized
natural isomorphism; no arbitrary tensor functor is chosen. Source: Stacks 06YY
(auxiliary; not a blueprint node). -/
def derivedExtension {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) : DerivedExtension φ :=
  Classical.choice (derivedExtension_exists φ)

attribute [local irreducible] derivedExtension

/-- The specified derived extension of scalars. Source: Stacks 06YY
(auxiliary; not a blueprint node). -/
def extend {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) : D R ⥤ D S :=
  (derivedExtension φ).functor

/-- Its universal computation comparison on complexes. Source: Stacks 06YY
(auxiliary; not a blueprint node). -/
def extendComparison {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) :
    Q R ⋙ extend φ ⟶ (change φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q S :=
  (derivedExtension φ).comparison

/-- The scalar-extension insertion on sections, including the sheafification unit.
The target is the sheafification defining the actual scalar-extension tensor functor.
Source: Stacks 06YY (auxiliary; not a blueprint node). -/
def tensorSection {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) (M : Mod R)
    (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) : ((change φ).obj M).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings S).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M)).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)

section ScalarTransitions
variable {R S T : Sheaf J CommRingCat.{u}}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def resCompIso (φ : R ⟶ S) (τ : S ⟶ T) (ψ : R ⟶ T) (h : φ ≫ τ = ψ) :
    res τ ⋙ res φ ≅ res ψ := by
  subst ψ
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine { hom := { val := { app := fun U ↦ ?_, naturality := ?_ } }
             inv := { val := { app := fun U ↦ ?_, naturality := ?_ } }
             hom_inv_id := ?_
             inv_hom_id := ?_ }
    · exact ModuleCat.ofHom
        (X := ((res φ).obj ((res τ).obj M)).val.obj U)
        (Y := ((res (φ ≫ τ)).obj M).val.obj U)
        { toFun := fun m ↦ m
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
    · intros; ext; rfl
    · exact ModuleCat.ofHom
        (X := ((res (φ ≫ τ)).obj M).val.obj U)
        (Y := ((res φ).obj ((res τ).obj M)).val.obj U)
        { toFun := fun m ↦ m
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
    · intros; ext; rfl
    · ext; rfl
    · ext; rfl
  · intros; ext; rfl

private def transitionLift (φ : R ⟶ S) (τ : S ⟶ T) (ψ : R ⟶ T) (h : φ ≫ τ = ψ)
    (M : Mod R) : (change φ).obj M ⟶ (res τ).obj ((change ψ).obj M) :=
  (SheafOfModules.RingedTensor.tensorHomEquiv φ _ _).symm
    (SheafOfModules.RingedTensor.tensorHomEquiv ψ M _ (𝟙 _) ≫
      (resCompIso φ τ ψ h).inv.app ((change ψ).obj M))

private theorem transitionLift_one (φ : R ⟶ S) (τ : S ⟶ T) (ψ : R ⟶ T) (h : φ ≫ τ = ψ)
    (M : Mod R) (U : Cᵒᵖ) (m : M.val.obj U) :
    (transitionLift φ τ ψ h M).val.app U (tensorSection φ M U 1 m) =
      tensorSection ψ M U 1 m := by
  have hh := (SheafOfModules.RingedTensor.tensorHomEquiv φ _ _).apply_symm_apply
    (SheafOfModules.RingedTensor.tensorHomEquiv ψ M _ (𝟙 _) ≫
      (resCompIso φ τ ψ h).inv.app ((change ψ).obj M))
  subst ψ
  change (transitionLift φ τ (φ ≫ τ) rfl M).val.app U (tensorSection φ M U 1 m) = _
  exact congrArg (fun k ↦ k.val.app U m) hh

private theorem tensorSection_smul (φ : R ⟶ S) (M : Mod R)
    (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    tensorSection φ M U s m = s • tensorSection φ M U 1 m := by
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings S).obj)).unit.app
    (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M)
  have h := (η.app U).hom.map_smul s
    ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)
  change η.app U ((s * 1) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m) = _ at h
  rw [mul_one] at h
  exact h

private theorem transitionLift_tmul (φ : R ⟶ S) (τ : S ⟶ T) (ψ : R ⟶ T)
    (h : φ ≫ τ = ψ) (M : Mod R) (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    (transitionLift φ τ ψ h M).val.app U (tensorSection φ M U s m) =
      tensorSection ψ M U (τ.hom.app U s) m := by
  rw [tensorSection_smul φ, map_smul, transitionLift_one,
    tensorSection_smul ψ M U (τ.hom.app U s)]
  rfl

private theorem tensorSection_map (φ : R ⟶ S) {M N : Mod R} (f : M ⟶ N)
    (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    ((change φ).map f).val.app U (tensorSection φ M U s m) =
      tensorSection φ N U s (f.val.app U m) := by
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings S).obj)).unit
  let k : SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M ⟶
      SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ N :=
    { app := fun V ↦ (ModuleCat.extendScalars (φ.hom.app V).hom).map (f.val.app V)
      naturality := SheafOfModules.changeOfRingsHom_naturality φ M f }
  have h := congrArg (fun t ↦ t.app U
    (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)) (η.naturality k)
  change tensorSection φ N U s (f.val.app U m) =
    ((change φ).map f).val.app U (tensorSection φ M U s m) at h
  exact h.symm

private theorem restrictedTensor_hom_ext (φ : R ⟶ S) (M : Mod R) (N : Mod R)
    (f g : (res φ).obj ((change φ).obj M) ⟶ N)
    (h : ∀ U s m, f.val.app U (tensorSection φ M U s m) =
      g.val.app U (tensorSection φ M U s m)) : f = g := by
  apply (SheafOfModules.toSheaf (siteModuleRings R)).map_injective
  apply ((sheafificationAdjunction J AddCommGrpCat).homEquiv
    (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M).presheaf
    ((SheafOfModules.toSheaf (siteModuleRings R)).obj N)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext U z
  induction z using TensorProduct.inductionOn with
  | tmul s m => exact h U s m
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw

private def scalarTransition (φ : R ⟶ S) (τ : S ⟶ T) (ψ : R ⟶ T) (h : φ ≫ τ = ψ) :
    change φ ⋙ res φ ⟶ change ψ ⋙ res ψ where
  app M := (res φ).map (transitionLift φ τ ψ h M) ≫
    (resCompIso φ τ ψ h).hom.app ((change ψ).obj M)
  naturality M N f := by
    apply restrictedTensor_hom_ext φ M
    intro U s m
    subst ψ
    change (transitionLift φ τ (φ ≫ τ) rfl N).val.app U
        (((change φ).map f).val.app U (tensorSection φ M U s m)) =
      ((change (φ ≫ τ)).map f).val.app U
        ((transitionLift φ τ (φ ≫ τ) rfl M).val.app U (tensorSection φ M U s m))
    rw [tensorSection_map, transitionLift_tmul, transitionLift_tmul, tensorSection_map]

private theorem scalarTransition_tmul (φ : R ⟶ S) (τ : S ⟶ T) (ψ : R ⟶ T)
    (h : φ ≫ τ = ψ) (M : Mod R) (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    ((scalarTransition φ τ ψ h).app M).val.app U (tensorSection φ M U s m) =
      tensorSection ψ M U (τ.hom.app U s) m := by
  subst ψ
  exact transitionLift_tmul φ τ (φ ≫ τ) rfl M U s m

private theorem resCompIso_hom_apply (φ : R ⟶ S) (τ : S ⟶ T) (ψ : R ⟶ T)
    (h : φ ≫ τ = ψ) (M : Mod T) (U : Cᵒᵖ) (m : M.val.obj U) :
    ((resCompIso φ τ ψ h).hom.app M).val.app U m = m := by
  subst ψ
  rfl

private theorem resCompIso_inv_apply (φ : R ⟶ S) (τ : S ⟶ T) (ψ : R ⟶ T)
    (h : φ ≫ τ = ψ) (M : Mod T) (U : Cᵒᵖ) (m : M.val.obj U) :
    ((resCompIso φ τ ψ h).inv.app M).val.app U m = m := by
  subst ψ
  rfl

end ScalarTransitions

section FiniteComparisons

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R B S : Sheaf J CommRingCat.{u}}

private theorem scalarLinear_of_kernel_span
    {R B S : Type u} [CommRing R] [CommRing B] [CommRing S]
    (φ : R →+* B) (q : R →+* S) (p : B →+* S)
    (h : p.comp φ = q) (hq : Function.Surjective q)
    (hk : RingHom.ker p = Ideal.span (φ '' (RingHom.ker q : Set R)))
    (M : ModuleCat B) (N : ModuleCat S)
    (f : (ModuleCat.restrictScalars φ).obj M ⟶ (ModuleCat.restrictScalars q).obj N)
    (b : B) (m : M) : f (b • m) = p b • f m := by
  have hz (d : B) (hd : d ∈ RingHom.ker p) : ∀ m : M, f (d • m) = 0 := by
    rw [hk] at hd
    change d ∈ Submodule.span B (φ '' (RingHom.ker q : Set R)) at hd
    induction hd using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨a, ha, rfl⟩ := hd
      intro m
      have hf := f.hom.map_smul a m
      change f (φ a • m) = q a • f m at hf
      rw [show q a = 0 from ha, zero_smul] at hf
      exact hf
    | zero => intro m; simp only [zero_smul, map_zero]
    | add d e hd he ihd ihe =>
      intro m
      rw [add_smul, map_add, ihd, ihe, add_zero]
    | smul a d hd ih =>
      intro m
      change f ((a * d) • m) = 0
      rw [mul_comm a d, mul_smul]
      exact ih (a • m)
  obtain ⟨a, ha⟩ := hq (p b)
  have hφ (a : R) : p (φ a) = q a := congrArg (fun f : R →+* S ↦ f a) h
  have hd : b - φ a ∈ RingHom.ker p := by
    change p (b - φ a) = 0
    rw [map_sub, hφ, ha, sub_self]
  have he := hz (b - φ a) hd m
  rw [sub_smul, map_sub] at he
  rw [sub_eq_zero] at he
  rw [he]
  have hf := f.hom.map_smul a m
  change f (φ a • m) = q a • f m at hf
  exact hf.trans (congrArg (fun s : S ↦ s • f m) ha)

private def quotientRestrictionHomEquiv (φ : R ⟶ B) (q : R ⟶ S) (p : B ⟶ S)
    (h : φ ≫ p = q)
    (hq : ∀ U : Cᵒᵖ, Function.Surjective (q.hom.app U))
    (hk : ∀ U : Cᵒᵖ, RingHom.ker (p.hom.app U).hom =
      Ideal.span ((φ.hom.app U).hom '' (RingHom.ker (q.hom.app U).hom : Set _)))
    (M : Mod B) (N : Mod S) :
    ((res φ).obj M ⟶ (res q).obj N) ≃ (M ⟶ (res p).obj N) where
  toFun f :=
    { val :=
        { app := fun U ↦ ModuleCat.ofHom
            (X := M.val.obj U) (Y := ((res p).obj N).val.obj U)
            { toFun := fun m ↦ f.val.app U m
              map_add' := fun x y ↦ (f.val.app U).hom.map_add x y
              map_smul' := fun b m ↦ scalarLinear_of_kernel_span
                (φ.hom.app U).hom (q.hom.app U).hom (p.hom.app U).hom
                (congrArg (fun t : R ⟶ S ↦ (t.hom.app U).hom) h)
                (hq U) (hk U) (M.val.obj U) (N.val.obj U) (f.val.app U) b m }
          naturality := by
            intro U V i
            ext m
            exact congrArg (fun t ↦ t m) (f.val.naturality i) } }
  invFun g := (res φ).map g ≫ (resCompIso φ p q h).hom.app N
  left_inv f := by subst q; ext U m; rfl
  right_inv f := by subst q; ext U m; rfl

private def quotientTensorAdjunction (φ : R ⟶ B) (q : R ⟶ S) (p : B ⟶ S)
    (h : φ ≫ p = q)
    (hq : ∀ U : Cᵒᵖ, Function.Surjective (q.hom.app U))
    (hk : ∀ U : Cᵒᵖ, RingHom.ker (p.hom.app U).hom =
      Ideal.span ((φ.hom.app U).hom '' (RingHom.ker (q.hom.app U).hom : Set _))) :
    res φ ⋙ change q ⊣ res p :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N ↦ (SheafOfModules.RingedTensor.tensorHomEquiv q _ _).trans
        (quotientRestrictionHomEquiv φ q p h hq hk M N)
      homEquiv_naturality_left_symm := by
        intro M M' N f g
        change (SheafOfModules.RingedTensor.tensorHomEquiv q _ _).symm
          ((quotientRestrictionHomEquiv φ q p h hq hk M N).symm (f ≫ g)) = _
        have hh : (quotientRestrictionHomEquiv φ q p h hq hk M N).symm (f ≫ g) =
            (res φ).map f ≫ (quotientRestrictionHomEquiv φ q p h hq hk M' N).symm g := by
          subst q
          ext U m
          rfl
        rw [hh]
        have hn := (SheafOfModules.RingedTensor.tensorAdjunction q)
          |>.homEquiv_naturality_left_symm ((res φ).map f)
            ((quotientRestrictionHomEquiv φ q p h hq hk M' N).symm g)
        simp only [SheafOfModules.RingedTensor.tensorAdjunction,
          Adjunction.mkOfHomEquiv_homEquiv] at hn
        exact hn
      homEquiv_naturality_right := by
        intro M N N' f g
        change (quotientRestrictionHomEquiv φ q p h hq hk M N')
          (SheafOfModules.RingedTensor.tensorHomEquiv q _ _ (f ≫ g)) = _
        have hn := (SheafOfModules.RingedTensor.tensorAdjunction q).homEquiv_naturality_right f g
        simp only [SheafOfModules.RingedTensor.tensorAdjunction,
          Adjunction.mkOfHomEquiv_homEquiv] at hn
        rw [hn]
        rfl }

private theorem quotientTensorIso_exists (φ : R ⟶ B) (q : R ⟶ S) (p : B ⟶ S)
    (h : φ ≫ p = q)
    (hq : ∀ U : Cᵒᵖ, Function.Surjective (q.hom.app U))
    (hk : ∀ U : Cᵒᵖ, RingHom.ker (p.hom.app U).hom =
      Ideal.span ((φ.hom.app U).hom '' (RingHom.ker (q.hom.app U).hom : Set _))) :
    ∃! e : res φ ⋙ change q ≅ change p,
      ∀ (M : Mod B) (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U),
        (e.hom.app M).val.app U (tensorSection q ((res φ).obj M) U s m) =
          tensorSection p M U s m := by
  let adj₁ := quotientTensorAdjunction φ q p h hq hk
  let adj₂ := SheafOfModules.RingedTensor.tensorAdjunction p
  let e := Adjunction.leftAdjointUniq adj₁ adj₂
  have he (M : Mod B) (U : Cᵒᵖ) (m : M.val.obj U) :
      (e.hom.app M).val.app U (tensorSection q ((res φ).obj M) U 1 m) =
        tensorSection p M U 1 m := by
    have he := congrArg (fun t : M ⟶ (res p).obj ((change p).obj M) ↦ t.val.app U m)
      (Adjunction.homEquiv_leftAdjointUniq_hom_app adj₁ adj₂ M)
    change ((quotientRestrictionHomEquiv φ q p h hq hk M ((change p).obj M))
      (SheafOfModules.RingedTensor.tensorHomEquiv q ((res φ).obj M) _ (e.hom.app M))).val.app
        U m = _ at he
    change (e.hom.app M).val.app U (tensorSection q ((res φ).obj M) U 1 m) =
      tensorSection p M U 1 m at he
    exact he
  have ht (M : Mod B) (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
      (e.hom.app M).val.app U (tensorSection q ((res φ).obj M) U s m) =
        tensorSection p M U s m := by
    rw [tensorSection_smul q, map_smul, he, tensorSection_smul p M U s m]
  refine ⟨e, ht, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (SheafOfModules.RingedTensor.tensorHomEquiv q ((res φ).obj M) _).injective
  ext U m
  exact (he' M U 1 m).trans (ht M U 1 m).symm

end FiniteComparisons

-- Subsequent proofs use the section formulas instead of reducing these constructions.
attribute [irreducible] resCompIso transitionLift scalarTransition
  quotientRestrictionHomEquiv quotientTensorAdjunction

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The finite comparison before localization, uniquely fixed on sheafified pure tensors.
Source: Stacks 099L, 06YY (auxiliary; not a blueprint node).
Proof: the finite quotients have the same kernel after extending the constant ideal.
Consequently restriction-linear maps to a finite-quotient module are completion-linear.
The two tensor functors are therefore left adjoints to the same restriction functor.
Uniqueness of left adjoints gives the comparison, and the adjunction unit gives its
pure-tensor formula. The formula on tensors with first factor one determines it uniquely. -/
theorem finiteComparison_existsUnique (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    ∃! e : res (coefficientMap J A I) ⋙ change (quotient J A I n) ≅
        change (projection J A I n),
      ∀ (M : Mod (completed J A I)) (U : Cᵒᵖ)
        (s : (finite J A I n).obj.obj U) (m : M.val.obj U),
        (e.hom.app M).val.app U
          (tensorSection (quotient J A I n) ((res (coefficientMap J A I)).obj M) U s m) =
            tensorSection (projection J A I n) M U s m := by
  apply quotientTensorIso_exists (coefficientMap J A I) (quotient J A I n)
    (projection J A I n)
  · exact limit.lift_π (quotientCone J A I) (op n)
  · intro U
    exact ((flat_and_quotients J A I).2.2 n U.unop).1
  · intro U
    rw [← Ideal.map_span, Ideal.span_eq,
      ((flat_and_quotients J A I).2.2 n U.unop).2, Ideal.map_span, ← Set.range_comp']
    exact ((flat_and_quotients J A I).2.1 n U.unop).2

/-- The canonical finite comparison, with its pure-tensor normalization fixed uniquely.
Source: Stacks 099L (auxiliary; not a blueprint node). -/
def finiteComparison (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    res (coefficientMap J A I) ⋙ change (quotient J A I n) ≅
      change (projection J A I n) :=
  (finiteComparison_existsUnique J A I n).exists.choose

/-- The standard computation square for exact restriction of scalars.
Source: Stacks 099I (auxiliary; not a blueprint node). -/
def resFactors {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    (res φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q R ≅ Q B ⋙ dres φ :=
  letI := HasDerivedCategory.standard (Mod R)
  letI := HasDerivedCategory.standard (Mod B)
  letI := (siteRestrictScalars_exact φ).1
  letI := (siteRestrictScalars_exact φ).2
  (res φ).mapDerivedCategoryFactors.symm

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory CochainComplex.IsKFlatTensor
  CochainComplex.IsKFlatIndependentCoefficients

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Extend a natural comparison from a cochain resolving class. -/
private theorem resolving_nat
    {M H : Type*} [Category M] [Abelian M] [HasDerivedCategory M] [Category H]
    (F G : DerivedCategory M ⥤ H) (P : CochainComplex M ℤ → Prop)
    (hres : ∀ X : CochainComplex M ℤ,
      ∃ (K : CochainComplex M ℤ) (s : K ⟶ X), P K ∧ QuasiIso s)
    (α : ∀ X : CochainComplex M ℤ, P X →
      (F.obj (DerivedCategory.Q.obj X) ⟶ G.obj (DerivedCategory.Q.obj X)))
    (hα : ∀ (X Y : CochainComplex M ℤ) (hX : P X) (hY : P Y) (f : X ⟶ Y),
      F.map (DerivedCategory.Q.map f) ≫ α Y hY =
        α X hX ≫ G.map (DerivedCategory.Q.map f)) :
    ∃ e : F ⟶ G, ∀ (X : CochainComplex M ℤ) (hX : P X),
      e.app (DerivedCategory.Q.obj X) = α X hX := by
  let q := HomotopyCategory.quotient M (.up ℤ)
  let Q := DerivedCategory.Qh (C := M)
  let W := HomotopyCategory.quasiIso M (.up ℤ)
  let S (X : HomotopyCategory M (.up ℤ)) := P X.as
  have : W.HasRightCalculusOfFractions :=
    (HomotopyCategory.quasiIso_saturated_triangulated M).2.1
  have hres' (X : HomotopyCategory M (.up ℤ)) :
      ∃ (K : HomotopyCategory M (.up ℤ)) (s : K ⟶ X), S K ∧ W s := by
    obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨K, s, hK, hs⟩ := hres X
    exact ⟨q.obj K, q.map s, hK,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  let i := DerivedCategory.quotientCompQhIso M
  let α' (X : HomotopyCategory M (.up ℤ)) (hX : S X) :
      (Q ⋙ F).obj X ⟶ (Q ⋙ G).obj X :=
    F.map (i.hom.app X.as) ≫ α X.as hX ≫ G.map (i.inv.app X.as)
  have hα' (X Y : HomotopyCategory M (.up ℤ)) (hX : S X) (hY : S Y)
      (f : X ⟶ Y) :
      (Q ⋙ F).map f ≫ α' Y hY = α' X hX ≫ (Q ⋙ G).map f := by
    obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨Y, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
    obtain ⟨f, rfl⟩ := q.map_surjective f
    change P X at hX
    change P Y at hY
    have hi : Q.map (q.map f) ≫ i.hom.app Y =
        i.hom.app X ≫ DerivedCategory.Q.map f := i.hom.naturality f
    have hi' : DerivedCategory.Q.map f ≫ i.inv.app Y =
        i.inv.app X ≫ Q.map (q.map f) := i.inv.naturality f
    change F.map (Q.map (q.map f)) ≫
        (F.map (i.hom.app Y) ≫ α Y hY ≫ G.map (i.inv.app Y)) =
      (F.map (i.hom.app X) ≫ α X hX ≫ G.map (i.inv.app X)) ≫ G.map (Q.map (q.map f))
    rw [← F.map_comp_assoc, hi, F.map_comp_assoc,
      reassoc_of% hα X Y hX hY f]
    simp only [Category.assoc]
    rw [← G.map_comp, hi', G.map_comp]
  obtain ⟨β, hβ⟩ := exists_natTrans_from_resolvingClass W S hres' (Q ⋙ F) (Q ⋙ G)
    (fun X Y s hs ↦ by
      have : IsIso (Q.map s) := Localization.inverts Q W s hs
      exact inferInstanceAs (IsIso (F.map (Q.map s))))
    (fun X hX ↦ α' X hX) hα'
  let K := (Functor.whiskeringLeft _ _ H).obj Q
  have : K.Full := Localization.full_whiskeringLeft Q W H
  have : K.Faithful := Localization.faithful_whiskeringLeft Q W H
  let e : F ⟶ G := K.preimage β
  have he (X : HomotopyCategory M (.up ℤ)) : e.app (Q.obj X) = β.app X :=
    congrArg (fun t ↦ t.app X) (K.map_preimage β)
  refine ⟨e, ?_⟩
  intro X hX
  have hn := e.naturality (i.hom.app X)
  change F.map (i.hom.app X) ≫ e.app (DerivedCategory.Q.obj X) =
    e.app (Q.obj (q.obj X)) ≫ G.map (i.hom.app X) at hn
  rw [he, hβ (q.obj X) hX] at hn
  change F.map (i.hom.app X) ≫ e.app (DerivedCategory.Q.obj X) =
    (F.map (i.hom.app X) ≫ α X hX ≫ G.map (i.inv.app X)) ≫ G.map (i.hom.app X) at hn
  apply (cancel_epi (F.map (i.hom.app X))).1
  rw [hn]
  simp only [Category.assoc, ← G.map_comp, i.inv_hom_id_app, G.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Equality of derived natural maps can be checked on a cochain resolving class. -/
private theorem resolving_nat_ext
    {M H : Type*} [Category M] [Abelian M] [HasDerivedCategory M] [Category H]
    {F G : DerivedCategory M ⥤ H} (P : CochainComplex M ℤ → Prop)
    (hres : ∀ X : CochainComplex M ℤ,
      ∃ (K : CochainComplex M ℤ) (s : K ⟶ X), P K ∧ QuasiIso s)
    (α β : F ⟶ G)
    (h : ∀ X, P X → α.app (DerivedCategory.Q.obj X) =
      β.app (DerivedCategory.Q.obj X)) : α = β := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso M (.up ℤ))
  intro X
  obtain ⟨K, f, hK, hf⟩ := hres X
  have : QuasiIso f := hf
  have : IsIso (F.map (DerivedCategory.Q.map f)) := inferInstance
  apply (cancel_epi (F.map (DerivedCategory.Q.map f))).1
  rw [α.naturality, β.naturality, h K hK]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A resolving computation map determines a comparison, including its uniqueness. -/
private theorem resolving_comparison
    {M H : Type*} [Category M] [Abelian M] [HasDerivedCategory M] [Category H]
    (F G : DerivedCategory M ⥤ H) (T : CochainComplex M ℤ ⥤ H)
    (P : CochainComplex M ℤ → Prop)
    (hres : ∀ X : CochainComplex M ℤ,
      ∃ (K : CochainComplex M ℤ) (s : K ⟶ X), P K ∧ QuasiIso s)
    (α : DerivedCategory.Q ⋙ F ⟶ T) (β : DerivedCategory.Q ⋙ G ⟶ T)
    (hβ : ∀ X, P X → IsIso (β.app X)) :
    ∃! e : F ⟶ G, ∀ X, P X → e.app (DerivedCategory.Q.obj X) ≫ β.app X =
      α.app X := by
  let a (X : CochainComplex M ℤ) (hX : P X) :=
    let := hβ X hX
    α.app X ≫ inv (β.app X)
  obtain ⟨e, he⟩ := resolving_nat F G P hres a (by
    intro X Y hX hY f
    let := hβ X hX
    let := hβ Y hY
    apply (cancel_mono (β.app Y)).1
    dsimp only [a]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have ha : F.map (DerivedCategory.Q.map f) ≫ α.app Y = α.app X ≫ T.map f :=
      α.naturality f
    have hb : G.map (DerivedCategory.Q.map f) ≫ β.app Y = β.app X ≫ T.map f :=
      β.naturality f
    rw [ha, hb]
    simp only [IsIso.inv_hom_id_assoc])
  have he' : ∀ X, P X → e.app (DerivedCategory.Q.obj X) ≫ β.app X = α.app X := by
    intro X hX
    let := hβ X hX
    rw [he X hX]
    simp only [a, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  refine ⟨e, he', ?_⟩
  intro e' he''
  apply resolving_nat_ext P hres
  intro X hX
  let := hβ X hX
  apply (cancel_mono (β.app X)).1
  rw [he'' X hX, he' X hX]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Extend an invertible comparison from a cochain resolving class. -/
private theorem resolving_iso
    {M H : Type*} [Category M] [Abelian M] [HasDerivedCategory M] [Category H]
    (F G : DerivedCategory M ⥤ H) (P : CochainComplex M ℤ → Prop)
    (hres : ∀ X : CochainComplex M ℤ,
      ∃ (K : CochainComplex M ℤ) (s : K ⟶ X), P K ∧ QuasiIso s)
    (α : ∀ X : CochainComplex M ℤ, P X →
      (F.obj (DerivedCategory.Q.obj X) ≅ G.obj (DerivedCategory.Q.obj X)))
    (hα : ∀ (X Y : CochainComplex M ℤ) (hX : P X) (hY : P Y) (f : X ⟶ Y),
      F.map (DerivedCategory.Q.map f) ≫ (α Y hY).hom =
        (α X hX).hom ≫ G.map (DerivedCategory.Q.map f)) :
    ∃ e : F ≅ G, ∀ (X : CochainComplex M ℤ) (hX : P X),
      e.hom.app (DerivedCategory.Q.obj X) = (α X hX).hom := by
  obtain ⟨β, hβ⟩ := resolving_nat F G P hres (fun X hX ↦ (α X hX).hom) hα
  have hβiso (X : CochainComplex M ℤ) : IsIso (β.app (DerivedCategory.Q.obj X)) := by
    obtain ⟨K, f, hK, hf⟩ := hres X
    have : QuasiIso f := hf
    have : IsIso (F.map (DerivedCategory.Q.map f)) := inferInstance
    have : IsIso (G.map (DerivedCategory.Q.map f)) := inferInstance
    have : IsIso (β.app (DerivedCategory.Q.obj K)) := by rw [hβ K hK]; infer_instance
    have hn := β.naturality (DerivedCategory.Q.map f)
    have : IsIso (F.map (DerivedCategory.Q.map f) ≫ β.app (DerivedCategory.Q.obj X)) := by
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_left (F.map (DerivedCategory.Q.map f)) _
  let L := (Functor.whiskeringLeft _ _ H).obj (DerivedCategory.Q (C := M))
  let W := HomologicalComplex.quasiIso M (.up ℤ)
  have : L.Full := Localization.full_whiskeringLeft DerivedCategory.Q W H
  have : L.Faithful := Localization.faithful_whiskeringLeft DerivedCategory.Q W H
  have : ∀ X, IsIso ((L.map β).app X) := fun X ↦ hβiso X
  have : IsIso (L.map β) := NatIso.isIso_of_isIso_app _
  have : IsIso β := isIso_of_reflects_iso β L
  exact ⟨asIso β, hβ⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem resolving_comparison_iso
    {M H : Type*} [Category M] [Abelian M] [HasDerivedCategory M] [Category H]
    (F G : DerivedCategory M ⥤ H) (T : CochainComplex M ℤ ⥤ H)
    (P : CochainComplex M ℤ → Prop)
    (hres : ∀ X : CochainComplex M ℤ,
      ∃ (K : CochainComplex M ℤ) (s : K ⟶ X), P K ∧ QuasiIso s)
    (α : DerivedCategory.Q ⋙ F ⟶ T) (β : DerivedCategory.Q ⋙ G ⟶ T)
    (hα : ∀ X, P X → IsIso (α.app X)) (hβ : ∀ X, P X → IsIso (β.app X)) :
    ∃ e : F ≅ G, ∀ X, P X → e.hom.app (DerivedCategory.Q.obj X) ≫ β.app X =
      α.app X := by
  let a (X : CochainComplex M ℤ) (hX : P X) :=
    let := hα X hX
    let := hβ X hX
    asIso (α.app X) ≪≫ (asIso (β.app X)).symm
  obtain ⟨e, he⟩ := resolving_iso F G P hres a (by
    intro X Y hX hY f
    let := hα X hX
    let := hα Y hY
    let := hβ X hX
    let := hβ Y hY
    apply (cancel_mono (β.app Y)).1
    dsimp only [a, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have ha : F.map (DerivedCategory.Q.map f) ≫ α.app Y = α.app X ≫ T.map f :=
      α.naturality f
    have hb : G.map (DerivedCategory.Q.map f) ≫ β.app Y = β.app X ≫ T.map f :=
      β.naturality f
    rw [ha, hb]
    simp only [IsIso.inv_hom_id_assoc])
  refine ⟨e, ?_⟩
  intro X hX
  let := hα X hX
  let := hβ X hX
  rw [he X hX]
  simp only [a, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    Category.assoc, IsIso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Descend a square whose second computation is invertible on a resolving class. -/
private theorem resolving_square
    {M H₁ H₂ H₃ D₁ D₂ D₃ : Type*}
    [Category M] [Abelian M] [HasDerivedCategory M]
    [Category H₁] [Category H₂] [Category H₃]
    [Category D₁] [Category D₂] [Category D₃]
    (q₁ : H₁ ⥤ D₁) (q₂ : H₂ ⥤ D₂) (q₃ : H₃ ⥤ D₃)
    (r : CochainComplex M ℤ ⥤ H₁) (b : CochainComplex M ℤ ⥤ H₂)
    (p : H₁ ⥤ H₃) (s : H₂ ⥤ H₃)
    (dr : DerivedCategory M ⥤ D₁) (db : DerivedCategory M ⥤ D₂)
    (dp : D₁ ⥤ D₃) (ds : D₂ ⥤ D₃)
    (α : r ⋙ q₁ ≅ DerivedCategory.Q ⋙ dr)
    (β : q₁ ⋙ dp ⟶ p ⋙ q₃) (γ : r ⋙ p ⟶ b ⋙ s)
    (δ : DerivedCategory.Q ⋙ db ⟶ b ⋙ q₂) (ε : s ⋙ q₃ ≅ q₂ ⋙ ds)
    (P : CochainComplex M ℤ → Prop)
    (hres : ∀ X : CochainComplex M ℤ,
      ∃ (K : CochainComplex M ℤ) (f : K ⟶ X), P K ∧ QuasiIso f)
    (hδ : ∀ X, P X → IsIso (δ.app X)) :
    ∃! e : dr ⋙ dp ⟶ db ⋙ ds, ∀ X, P X →
      dp.map (α.inv.app X) ≫ β.app (r.obj X) ≫ q₃.map (γ.app X) =
        e.app (DerivedCategory.Q.obj X) ≫ ds.map (δ.app X) ≫ ε.inv.app (b.obj X) := by
  let T := b ⋙ s ⋙ q₃
  let a : DerivedCategory.Q ⋙ (dr ⋙ dp) ⟶ T :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight α.inv _ ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft r β ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight γ _ ≫
      (Functor.associator _ _ _).hom
  let z : DerivedCategory.Q ⋙ (db ⋙ ds) ⟶ T :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight δ _ ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft b ε.inv
  have hz X (hX : P X) : IsIso (z.app X) := by
    have := hδ X hX
    dsimp only [z, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  obtain ⟨e, he, hu⟩ := resolving_comparison (dr ⋙ dp) (db ⋙ ds) T P hres a z hz
  have hf (t : dr ⋙ dp ⟶ db ⋙ ds) :
      (∀ X, P X → t.app (DerivedCategory.Q.obj X) ≫ z.app X = a.app X) ↔
      (∀ X, P X → dp.map (α.inv.app X) ≫ β.app (r.obj X) ≫ q₃.map (γ.app X) =
        t.app (DerivedCategory.Q.obj X) ≫ ds.map (δ.app X) ≫ ε.inv.app (b.obj X)) := by
    dsimp only [a, z, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    simp only [Category.id_comp, Category.comp_id]
    exact ⟨fun h X hX ↦ (h X hX).symm, fun h X hX ↦ (h X hX).symm⟩
  exact ⟨e, (hf e).1 he, fun t ht ↦ hu t ((hf t).2 ht)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Descend a square whose two iterated computations are invertible. -/
private theorem resolving_square_iso
    {M H₁ H₂ H₃ D₁ D₂ D₃ : Type*}
    [Category M] [Abelian M] [HasDerivedCategory M]
    [Category H₁] [Category H₂] [Category H₃]
    [Category D₁] [Category D₂] [Category D₃]
    (q₁ : H₁ ⥤ D₁) (q₂ : H₂ ⥤ D₂) (q₃ : H₃ ⥤ D₃)
    (r : CochainComplex M ℤ ⥤ H₁) (b : CochainComplex M ℤ ⥤ H₂)
    (p : H₁ ⥤ H₃) (s : H₂ ⥤ H₃)
    (dr : DerivedCategory M ⥤ D₁) (db : DerivedCategory M ⥤ D₂)
    (dp : D₁ ⥤ D₃) (ds : D₂ ⥤ D₃)
    (α : DerivedCategory.Q ⋙ dr ⟶ r ⋙ q₁)
    (β : q₁ ⋙ dp ⟶ p ⋙ q₃) (γ : r ⋙ p ≅ b ⋙ s)
    (δ : DerivedCategory.Q ⋙ db ⟶ b ⋙ q₂) (ε : q₂ ⋙ ds ⟶ s ⋙ q₃)
    (P : CochainComplex M ℤ → Prop)
    (hres : ∀ X : CochainComplex M ℤ,
      ∃ (K : CochainComplex M ℤ) (f : K ⟶ X), P K ∧ QuasiIso f)
    (hα : ∀ X, P X → IsIso (α.app X))
    (hβ : ∀ X, P X → IsIso (β.app (r.obj X)))
    (hδ : ∀ X, P X → IsIso (δ.app X))
    (hε : ∀ X, P X → IsIso (ε.app (b.obj X))) :
    ∃! e : dr ⋙ dp ≅ db ⋙ ds, ∀ X, P X →
      dp.map (α.app X) ≫ β.app (r.obj X) ≫ q₃.map (γ.hom.app X) =
        e.hom.app (DerivedCategory.Q.obj X) ≫ ds.map (δ.app X) ≫ ε.app (b.obj X) := by
  let T := b ⋙ s ⋙ q₃
  let a : DerivedCategory.Q ⋙ (dr ⋙ dp) ⟶ T :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight α _ ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft r β ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight γ.hom _ ≫
      (Functor.associator _ _ _).hom
  let z : DerivedCategory.Q ⋙ (db ⋙ ds) ⟶ T :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight δ _ ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft b ε
  have ha X (hX : P X) : IsIso (a.app X) := by
    have := hα X hX
    have := hβ X hX
    dsimp only [a, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  have hz X (hX : P X) : IsIso (z.app X) := by
    have := hδ X hX
    have := hε X hX
    dsimp only [z, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  obtain ⟨e, he⟩ := resolving_comparison_iso (dr ⋙ dp) (db ⋙ ds) T P hres a z ha hz
  have hf (t : dr ⋙ dp ≅ db ⋙ ds) :
      (∀ X, P X → t.hom.app (DerivedCategory.Q.obj X) ≫ z.app X = a.app X) ↔
      (∀ X, P X → dp.map (α.app X) ≫ β.app (r.obj X) ≫ q₃.map (γ.hom.app X) =
        t.hom.app (DerivedCategory.Q.obj X) ≫ ds.map (δ.app X) ≫ ε.app (b.obj X)) := by
    dsimp only [a, z, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    simp only [Category.id_comp, Category.comp_id]
    exact ⟨fun h X hX ↦ (h X hX).symm, fun h X hX ↦ (h X hX).symm⟩
  refine ⟨e, (hf e).1 he, ?_⟩
  intro t ht
  apply Iso.ext
  apply resolving_nat_ext P hres
  intro X hX
  have := hz X hX
  apply (cancel_mono (z.app X)).1
  rw [(hf t).2 ht X hX, he X hX]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Derive an ordinary finite scalar comparison before specializing module functors. -/
private theorem resolving_finite_comparison
    {M N H DN DH : Type*}
    [Category M] [Abelian M] [HasDerivedCategory M]
    [Category N] [Preadditive N] [Category H] [Preadditive H] [Category DN] [Category DH]
    (qN : CochainComplex N ℤ ⥤ DN) (qH : CochainComplex H ℤ ⥤ DH)
    (r : M ⥤ N) (f : N ⥤ H) (g : M ⥤ H)
    [r.PreservesZeroMorphisms] [f.PreservesZeroMorphisms] [g.PreservesZeroMorphisms]
    (dr : DerivedCategory M ⥤ DN) (df : DN ⥤ DH) (dg : DerivedCategory M ⥤ DH)
    (α : r.mapHomologicalComplex (.up ℤ) ⋙ qN ≅ DerivedCategory.Q ⋙ dr)
    (β : qN ⋙ df ⟶ f.mapHomologicalComplex (.up ℤ) ⋙ qH)
    (γ : r ⋙ f ≅ g)
    (δ : DerivedCategory.Q ⋙ dg ⟶ g.mapHomologicalComplex (.up ℤ) ⋙ qH)
    (P : CochainComplex M ℤ → Prop)
    (hres : ∀ X : CochainComplex M ℤ,
      ∃ (K : CochainComplex M ℤ) (s : K ⟶ X), P K ∧ QuasiIso s)
    (hβ : ∀ X, P X → IsIso (β.app ((r.mapHomologicalComplex (.up ℤ)).obj X)))
    (hδ : ∀ X, P X → IsIso (δ.app X)) :
    ∃ e : dr ⋙ df ≅ dg, ∀ X, P X →
      df.map (α.inv.app X) ≫ β.app ((r.mapHomologicalComplex (.up ℤ)).obj X) ≫
        qH.map ((NatIso.mapHomologicalComplex γ (.up ℤ)).hom.app X) =
        e.hom.app (DerivedCategory.Q.obj X) ≫ δ.app X := by
  let rc := r.mapHomologicalComplex (.up ℤ)
  let gc := g.mapHomologicalComplex (.up ℤ)
  let γc : rc ⋙ f.mapHomologicalComplex (.up ℤ) ≅ gc :=
    NatIso.mapHomologicalComplex γ (.up ℤ)
  let a : DerivedCategory.Q ⋙ (dr ⋙ df) ⟶ gc ⋙ qH :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight α.inv _ ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft rc β ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight γc.hom _
  have ha X (hX : P X) : IsIso (a.app X) := by
    have := hβ X hX
    dsimp only [a, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  obtain ⟨e, he⟩ := resolving_comparison_iso (dr ⋙ df) dg (gc ⋙ qH) P hres a δ ha hδ
  refine ⟨e, ?_⟩
  intro X hX
  have h := he X hX
  dsimp only [a, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  simpa only [Category.id_comp, Category.comp_id, Category.assoc] using h.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restricted_kFlat {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (hB : SheafOfModules.IsFlat ((res φ).obj (SheafOfModules.unit (siteModuleRings B))))
    (P : Cx B) (hP : P.IsKFlatTensor) :
    CochainComplex.IsKFlatTensor
      (((res φ).mapHomologicalComplex (.up ℤ)).obj P) := by
  let := SheafOfModules.monoidalCategory R
  have hflat :=
    (exactFunctor (Mod R) (Mod R)).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R
        ((res φ).obj (SheafOfModules.unit (siteModuleRings B)))).symm hB
  have h := SheafOfModules.isKFlat_restrictScalars_of_flat φ hflat P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP)
  exact (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 h.1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem module_flat_kFlat_resolution {R : Sheaf J CommRingCat.{u}} (P : Cx R) :
    ∃ (K : Cx R) (f : K ⟶ P),
      (K.IsKFlatTensor ∧ ∀ q : ℤ, SheafOfModules.IsFlat (K.X q)) ∧ QuasiIso f := by
  obtain ⟨K, f, hK, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
  let := SheafOfModules.monoidalCategory R
  refine ⟨K, f, ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat K).1 hK, ?_⟩,
    hq⟩
  intro q
  exact hf q

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restricted_flat {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (hB : SheafOfModules.IsFlat ((res φ).obj (SheafOfModules.unit (siteModuleRings B))))
    (P : Cx B) (hP : P.IsKFlatTensor)
    (hf : ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) :
    ∀ q : ℤ, SheafOfModules.IsFlat (((res φ).obj (P.X q))) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory B
  have hflat :=
    (exactFunctor (Mod R) (Mod R)).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R
        ((res φ).obj (SheafOfModules.unit (siteModuleRings B)))).symm hB
  have h := SheafOfModules.isKFlat_restrictScalars_of_flat φ hflat P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP)
  have hf' (q : ℤ) :=
    (exactFunctor (Mod B) (Mod B)).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso B (P.X q)).symm (hf q)
  intro q
  exact (exactFunctor (Mod R) (Mod R)).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R ((res φ).obj (P.X q))) (h.2 hf' q)

section
attribute [local irreducible] dres change

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite scalar comparison in D(S_n), normalized on every flat-term K-flat complex.
Source: Stacks 099L, 06YY (auxiliary; not a blueprint node).
Proof: a flat-term K-flat B-complex remains K-flat over R because B is R-flat.
Use finiteComparison on that representative. Its pure-tensor formula is natural and
independent of replacements by the universal derived-change-of-rings counits, giving
this natural isomorphism and the displayed computation square. -/
theorem finiteDerivedComparison (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    ∃ e : dres (coefficientMap J A I) ⋙ extend (quotient J A I n) ≅
        extend (projection J A I n),
      ∀ (P : Cx (completed J A I)), P.IsKFlatTensor →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        (extend (quotient J A I n)).map
            ((resFactors (coefficientMap J A I)).inv.app P) ≫
          (extendComparison (quotient J A I n)).app
            (((res (coefficientMap J A I)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (Q (finite J A I n)).map
            ((NatIso.mapHomologicalComplex (finiteComparison J A I n)
              (ComplexShape.up ℤ)).hom.app P) =
        (e.hom.app ((Q (completed J A I)).obj P)) ≫
          (extendComparison (projection J A I n)).app P := by
  let := HasDerivedCategory.standard (Mod (constant J A))
  let := HasDerivedCategory.standard (Mod (completed J A I))
  let := HasDerivedCategory.standard (Mod (finite J A I n))
  let φ := coefficientMap J A I
  let P (X : Cx (completed J A I)) := X.IsKFlatTensor
  have hres (X : Cx (completed J A I)) :
      ∃ (K : Cx (completed J A I)) (s : K ⟶ X), P K ∧ QuasiIso s := by
    obtain ⟨K, f, hK, _, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients X
    exact ⟨K, f, (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat K).1 hK, hf⟩
  obtain ⟨e, he⟩ := resolving_finite_comparison
    (Q (constant J A)) (Q (finite J A I n))
    (res φ) (change (quotient J A I n)) (change (projection J A I n))
    (dres φ) (extend (quotient J A I n)) (extend (projection J A I n))
    (resFactors φ) (extendComparison (quotient J A I n)) (finiteComparison J A I n)
    (extendComparison (projection J A I n)) P hres
    (fun X hX ↦ (derivedExtension (quotient J A I n)).computation _
      (restricted_kFlat φ (flat_and_quotients J A I).1 X hX))
    (fun X hX ↦ (derivedExtension (projection J A I n)).computation X hX)
  exact ⟨e, fun X hX _ ↦ he X hX⟩

end

variable (J A I)

/-- The two coefficient sheaves, false for constant and true for completed coefficients.
Source: Stacks 099L (auxiliary; not a blueprint node). -/
abbrev coefficients (b : Bool) : Sheaf J CommRingCat.{u} :=
  if b then completed J A I else constant J A

/-- Their structural constant coefficient maps. Source: Stacks 099L
(auxiliary; not a blueprint node). -/
def baseMap (b : Bool) : constant J A ⟶ coefficients J A I b :=
  match b with
  | false => 𝟙 _
  | true => coefficientMap J A I

/-- Their finite projections, the original quotient maps. Source: Stacks 099L
(auxiliary; not a blueprint node). -/
def finiteMap (b : Bool) (n : ℕ) : coefficients J A I b ⟶ finite J A I n :=
  match b with
  | false => quotient J A I n
  | true => projection J A I n

/-- Finite reduction with the original coefficient action retained. Source: Stacks 099L
(auxiliary; not a blueprint node). -/
def reduction (b : Bool) (n : ℕ) :
    Mod (coefficients J A I b) ⥤ Mod (coefficients J A I b) :=
  change (finiteMap J A I b n) ⋙ res (finiteMap J A I b n)

/-- The quotient transition is fixed uniquely by its sectionwise tensor formula.
Source: Stacks 099L, 06YY (auxiliary; not a blueprint node).
Proof: the finite quotient transition preserves the balanced tensor relations because
it commutes with the coefficient projections. Sheafify its map s tensor m ↦ bar(s) tensor m.
The formula is linear, commutes with restrictions and module maps, and determines it uniquely. -/
theorem reductionStep_existsUnique (b : Bool) (n : ℕ) :
    ∃! t : reduction J A I b (n + 1) ⟶ reduction J A I b n,
      ∀ (M : Mod (coefficients J A I b)) (U : Cᵒᵖ)
        (s : (finite J A I (n + 1)).obj.obj U) (m : M.val.obj U),
        (t.app M).val.app U (tensorSection (finiteMap J A I b (n + 1)) M U s m) =
          tensorSection (finiteMap J A I b n) M U
            ((transition J A I n).hom.app U s) m := by
  have h : finiteMap J A I b (n + 1) ≫ transition J A I n = finiteMap J A I b n := by
    cases b with
    | false =>
      simpa only [finiteMap, Functor.const_obj_map, Functor.const_obj_obj,
        Category.id_comp, finiteSystem,
        Functor.ofOpSequence_map_homOfLE_succ, Category.id_comp] using (quotient_step J A I n).symm
    | true =>
      change projection J A I (n + 1) ≫ transition J A I n = projection J A I n
      unfold projection completed
      simpa only [finiteSystem,
        Functor.ofOpSequence_map_homOfLE_succ] using
          limit.w (finiteSystem J A I) (homOfLE (Nat.le_succ n)).op
  let t := scalarTransition (finiteMap J A I b (n + 1)) (transition J A I n)
    (finiteMap J A I b n) h
  refine ⟨t, scalarTransition_tmul _ _ _ h, ?_⟩
  intro t' ht'
  apply NatTrans.ext
  funext M
  apply restrictedTensor_hom_ext (finiteMap J A I b (n + 1)) M
  intro U s m
  exact (ht' M U s m).trans (scalarTransition_tmul _ _ _ h M U s m).symm

/-- The actual finite quotient transition with its uniquely specified tensor formula.
Source: Stacks 099L (auxiliary; not a blueprint node). -/
def reductionStep (b : Bool) (n : ℕ) :
    reduction J A I b (n + 1) ⟶ reduction J A I b n :=
  (reductionStep_existsUnique J A I b n).exists.choose

/-- The strict reduction tower, retaining all its transitions functorially.
Source: Stacks 099L, 099M (auxiliary; not a blueprint node). -/
def reductionTower (b : Bool) : Mod (coefficients J A I b) ⥤
    (ℕᵒᵖ ⥤ Mod (coefficients J A I b)) :=
  (Functor.ofOpSequence (reductionStep J A I b)).flip

/-- The tower is additive, since every evaluation is additive scalar extension/restriction.
Source: Stacks 06YY (auxiliary; not a blueprint node).
Proof: evaluate the additive-functor identity at each tower index. The chosen tensor functor
and restriction of scalars are additive. Evaluation is jointly faithful. -/
theorem reductionTower_additive (b : Bool) : (reductionTower J A I b).Additive := by
  constructor
  intro M N f g
  apply NatTrans.ext
  funext n
  change (reduction J A I b n.unop).map (f + g) = _
  have : (reduction J A I b n.unop).Additive := by
    dsimp only [reduction, res]
    infer_instance
  exact Functor.map_add (reduction J A I b n.unop)

attribute [instance] reductionTower_additive

/-- The constant module tower functor. Source: Stacks 0940
(auxiliary; not a blueprint node). -/
abbrev constantTower (O : Sheaf J CommRingCat.{u}) : Mod O ⥤ (ℕᵒᵖ ⥤ Mod O) :=
  Functor.const ℕᵒᵖ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized scalar-extension unit, constructed before sheafification.
Its section maps are the ordinary module adjunction units followed by sheafification;
restriction and module-map naturality follow from the two presheaf unit equations. -/
private theorem scalarExtensionUnit_exists {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) :
    ∃ η : 𝟭 (Mod R) ⟶ change φ ⋙ res φ,
      ∀ (M : Mod R) (U : Cᵒᵖ) (m : M.val.obj U),
        (η.app M).val.app U m = tensorSection φ M U 1 m := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings S).obj)
  let q (M : Mod R) : M ⟶ (res φ).obj ((change φ).obj M) :=
    { val :=
      { app := fun U ↦
          (ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).unit.app (M.val.obj U) ≫
            (ModuleCat.restrictScalars (φ.hom.app U).hom).map
              ((adj.unit.app (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M)).app U)
        naturality := by
          intro U V f
          ext m
          change tensorSection φ M V 1 (M.val.map f m) =
            ((change φ).obj M).val.map f (tensorSection φ M U 1 m)
          let η := adj.unit.app (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M)
          have h := PresheafOfModules.naturality_apply η f
            ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)
          have ht := Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap φ M f)
            1 m
          rw [map_one] at ht
          exact (congrArg (η.app V) ht.symm).trans h } }
  let η : 𝟭 (Mod R) ⟶ change φ ⋙ res φ :=
    { app := q
      naturality := by
        intro M N f
        ext U m
        let a : SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M ⟶
            SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ N :=
          { app := fun V ↦ (ModuleCat.extendScalars (φ.hom.app V).hom).map (f.val.app V)
            naturality := SheafOfModules.changeOfRingsHom_naturality φ M f }
        have h := congrArg (fun t ↦ t.app U
          ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m))
          (adj.unit.naturality a)
        change tensorSection φ N U 1 (f.val.app U m) =
          ((change φ).map f).val.app U (tensorSection φ M U 1 m)
        change (adj.unit.app (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ N)).app U
            ((ModuleCat.extendScalars (φ.hom.app U).hom).map (f.val.app U)
              ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)) =
          ((change φ).map f).val.app U (tensorSection φ M U 1 m) at h
        rw [ModuleCat.ExtendScalars.map_tmul] at h
        exact h }
  exact ⟨η, fun _ _ _ ↦ rfl⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The strict quotient unit is uniquely determined by m ↦ 1 tensor m at every level.
Source: Stacks 099M (auxiliary; not a blueprint node).
Proof: the scalar-extension units commute with quotient transitions since they preserve 1.
They are linear in the original coefficients and natural in M, so form a natural
transformation of strict towers. The section formula determines every component. -/
theorem reductionUnit_existsUnique (b : Bool) :
    ∃! η : constantTower J (coefficients J A I b) ⟶ reductionTower J A I b,
      ∀ (M : Mod (coefficients J A I b)) (n : ℕ) (U : Cᵒᵖ) (m : M.val.obj U),
        ((η.app M).app (op n)).val.app U m =
          tensorSection (finiteMap J A I b n) M U 1 m := by
  let ηn (n : ℕ) : 𝟭 (Mod (coefficients J A I b)) ⟶ reduction J A I b n :=
    (scalarExtensionUnit_exists J (finiteMap J A I b n)).choose
  have hη (n : ℕ) (M : Mod (coefficients J A I b)) (U : Cᵒᵖ) (m : M.val.obj U) :
      ((ηn n).app M).val.app U m = tensorSection (finiteMap J A I b n) M U 1 m :=
    (scalarExtensionUnit_exists J (finiteMap J A I b n)).choose_spec M U m
  have hstep (M : Mod (coefficients J A I b)) (n : ℕ) :
      ((Functor.const ℕᵒᵖ).obj M).map (homOfLE (Nat.le_succ n)).op ≫ (ηn n).app M =
        (ηn (n + 1)).app M ≫
          ((reductionTower J A I b).obj M).map (homOfLE (Nat.le_succ n)).op := by
    change 𝟙 M ≫ (ηn n).app M = (ηn (n + 1)).app M ≫
      ((Functor.ofOpSequence (reductionStep J A I b)).map
        (homOfLE (Nat.le_succ n)).op).app M
    rw [Category.id_comp, Functor.ofOpSequence_map_homOfLE_succ]
    ext U m
    change ((ηn n).app M).val.app U m =
      ((reductionStep J A I b n).app M).val.app U (((ηn (n + 1)).app M).val.app U m)
    rw [hη, hη]
    have ht := (reductionStep_existsUnique J A I b n).exists.choose_spec M U
      (1 : (finite J A I (n + 1)).obj.obj U) m
    simpa only [map_one, reductionStep] using ht.symm
  let η : constantTower J (coefficients J A I b) ⟶ reductionTower J A I b :=
    { app := fun M ↦ NatTrans.ofOpSequence (fun n ↦ (ηn n).app M) (hstep M)
      naturality := by
        intro M N f
        apply NatTrans.ext
        funext n
        exact (ηn n.unop).naturality f }
  refine ⟨η, fun M n U m ↦ hη n M U m, ?_⟩
  intro η' hη'
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  ext U m
  exact (hη' M n.unop U m).trans (hη n.unop M U m).symm

/-- The actual strict quotient-tower unit. Source: Stacks 099M
(auxiliary; not a blueprint node). -/
def reductionUnit (b : Bool) :
    constantTower J (coefficients J A I b) ⟶ reductionTower J A I b :=
  (reductionUnit_existsUnique J A I b).exists.choose

variable {J A I}

/-- The standard derived category of strict module towers. Source: Stacks 0940
(auxiliary; not a blueprint node). -/
abbrev TD (O : Sheaf J CommRingCat.{u}) :=
  @DerivedCategory (ℕᵒᵖ ⥤ Mod O) _ _ (HasDerivedCategory.standard _)

/-- Localization of strict tower complexes. Source: Stacks 0940
(auxiliary; not a blueprint node). -/
abbrev TQ (O : Sheaf J CommRingCat.{u}) :
    CochainComplex (ℕᵒᵖ ⥤ Mod O) ℤ ⥤ TD O :=
  @DerivedCategory.Q (ℕᵒᵖ ⥤ Mod O) _ _ (HasDerivedCategory.standard _)

/-- The degreewise limit functor on complexes, with an abstract coefficient category.
Source: Stacks 0940 (auxiliary; not a blueprint node). -/
def complexLimitFunctor (M : Type*) [Category M] [Preadditive M]
    [HasLimitsOfShape ℕᵒᵖ M] [(lim : (ℕᵒᵖ ⥤ M) ⥤ M).PreservesZeroMorphisms] :
    CochainComplex (ℕᵒᵖ ⥤ M) ℤ ⥤ CochainComplex M ℤ :=
  (lim : (ℕᵒᵖ ⥤ M) ⥤ M).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The ordinary termwise limit of strict tower complexes. Source: Stacks 0940
(auxiliary; not a blueprint node). -/
abbrev ordinaryLimit (O : Sheaf J CommRingCat.{u}) :
    CochainComplex (ℕᵒᵖ ⥤ Mod O) ℤ ⥤ Cx O :=
  letI : (lim : (ℕᵒᵖ ⥤ Mod O) ⥤ Mod O).Additive :=
    Functor.additive_of_preserves_binary_products _
  complexLimitFunctor (Mod O)

set_option genSizeOf false in
set_option genInjectivity false in
/-- The total right derived strict-limit universal property and K-injective computation.
Source: Stacks 0940, 0941 (auxiliary; not a blueprint node). -/
structure StrictLimit (O : Sheaf J CommRingCat.{u}) where
  functor : TD O ⥤ D O
  comparison : ordinaryLimit O ⋙ Q O ⟶ TQ O ⋙ functor
  universal : functor.IsRightDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ Mod O) (ComplexShape.up ℤ))
  computation : ∀ P : CochainComplex (ℕᵒᵖ ⥤ Mod O) ℤ,
    P.IsKInjective → IsIso (comparison.app P)

/-- The strict-tower theorem supplies this existing total derived functor and comparison.
Source: Stacks 0940 (auxiliary; not a blueprint node).
Proof: specialize ringedStrictTowerHomotopyLimit to O with commutativity retained and to
the standard localizations. Project its universal right-derived pair and its computation
on K-injective tower complexes. These are precisely the fields displayed here. -/
theorem strictLimit_exists (O : Sheaf J CommRingCat.{u}) : Nonempty (StrictLimit O) := by
  let := HasDerivedCategory.standard (Mod O)
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod O)
  obtain ⟨RF, η, huniv, hcomp, _⟩ :=
    ringedStrictTowerHomotopyLimit J (siteModuleRings O) (fun U a b ↦ @mul_comm (O.obj.obj U) _ a b)
  exact ⟨{ functor := RF
           comparison := η
           universal := huniv
           computation := hcomp }⟩

/-- Select the total derived strict limit by its universal comparison.
Source: Stacks 0940 (auxiliary; not a blueprint node). -/
def strictLimit (O : Sheaf J CommRingCat.{u}) : StrictLimit O :=
  Classical.choice (strictLimit_exists O)

attribute [local irreducible] strictLimit

/-- Total right derived strict inverse limit, not a noncanonical triangulated cone.
Source: Stacks 0940 (auxiliary; not a blueprint node). -/
def rlim (O : Sheaf J CommRingCat.{u}) : TD O ⥤ D O := (strictLimit O).functor

/-- Its universal comparison from ordinary termwise inverse limit.
Source: Stacks 0940 (auxiliary; not a blueprint node). -/
def limitComparison (O : Sheaf J CommRingCat.{u}) :
    ordinaryLimit O ⋙ Q O ⟶ TQ O ⋙ rlim O := (strictLimit O).comparison

variable (J A I)

/-- The ordinary strict reduction-tower complex, on one fixed representative.
Source: Stacks 099M (auxiliary; not a blueprint node). -/
abbrev reductionComplex (b : Bool) (P : Cx (coefficients J A I b)) :=
  ((reductionTower J A I b).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The degreewise universal limit map for an abstract tower functor and its unit.
The chain equation follows after each limit projection from naturality of the unit. -/
private theorem complexLimitUnit {M : Type*} [Category M] [Preadditive M]
    [HasLimitsOfShape ℕᵒᵖ M] (T : M ⥤ (ℕᵒᵖ ⥤ M)) [T.PreservesZeroMorphisms]
    [(lim : (ℕᵒᵖ ⥤ M) ⥤ M).PreservesZeroMorphisms]
    (η : Functor.const ℕᵒᵖ ⟶ T) (P : CochainComplex M ℤ) :
    ∃! f : P ⟶ (complexLimitFunctor M).obj ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj P),
      ∀ (q : ℤ) (n : ℕ), f.f q ≫ limit.π (T.obj (P.X q)) (op n) =
        (η.app (P.X q)).app (op n) := by
  let f : P ⟶
      (complexLimitFunctor M).obj
        ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
    { f := fun q ↦ limit.lift _
        { pt := P.X q
          π := η.app (P.X q) }
      comm' := by
        intro q q' h
        apply limit.hom_ext
        intro n
        rw [Category.assoc, Category.assoc]
        change limit.lift _ _ ≫
          limMap (((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).d q q') ≫
            limit.π _ n = _
        rw [limMap_π, limit.lift_π_assoc]
        calc
          _ = P.d q q' ≫ (η.app (P.X q')).app n :=
            (congrArg (fun t ↦ t.app n)
              (η.naturality (P.d q q'))).symm
          _ = _ := congrArg (fun t ↦ P.d q q' ≫ t)
            (limit.lift_π (F := T.obj (P.X q'))
              { pt := P.X q', π := η.app (P.X q') } n).symm }
  refine ⟨f, ?_, ?_⟩
  · intro q n
    exact limit.lift_π _ _
  · intro g hg
    apply HomologicalComplex.hom_ext
    intro q
    apply limit.hom_ext
    intro n
    change g.f q ≫ limit.π (T.obj (P.X q)) n =
      limit.lift _ { pt := P.X q, π := η.app (P.X q) } ≫
        limit.π (T.obj (P.X q)) n
    rw [limit.lift_π]
    exact hg q n.unop

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary limit unit is the unique chain map with the prescribed quotient components.
Source: Stacks 099M, 0940 (auxiliary; not a blueprint node).
Proof: at degree q use limit.lift on the strict quotient-unit cone. The differential
commutes with every projection by naturality of reductionUnit, hence with their limit.
Joint monicity of the projections proves uniqueness in every degree. -/
theorem ordinaryUnit_existsUnique (b : Bool) (P : Cx (coefficients J A I b)) :
    ∃! f : P ⟶ (ordinaryLimit (coefficients J A I b)).obj (reductionComplex J A I b P),
      ∀ (q : ℤ) (n : ℕ), f.f q ≫
        limit.π ((reductionComplex J A I b P).X q) (op n) =
          ((reductionUnit J A I b).app (P.X q)).app (op n) := by
  have : (lim : (ℕᵒᵖ ⥤ Mod (coefficients J A I b)) ⥤
      Mod (coefficients J A I b)).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact complexLimitUnit (reductionTower J A I b) (reductionUnit J A I b) P

/-- The actual ordinary strict-limit unit, fixed by its quotient projections.
Source: Stacks 099M (auxiliary; not a blueprint node). -/
def ordinaryUnit (b : Bool) (P : Cx (coefficients J A I b)) :
    P ⟶ (ordinaryLimit (coefficients J A I b)).obj (reductionComplex J A I b P) :=
  (ordinaryUnit_existsUnique J A I b P).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Precomposition by a fully faithful whiskering functor preserves the terminal
right-extension universal property. Construct its lifts by taking preimages. -/
private theorem kan_precomp
    {A B D H : Type*} [Category A] [Category B] [Category D] [Category H]
    (P : A ⥤ B) (Q : B ⥤ D) (T : D ⥤ H) (G : B ⥤ H) (ε : Q ⋙ T ⟶ G)
    [((Functor.whiskeringLeft A B H).obj P).Full]
    [((Functor.whiskeringLeft A B H).obj P).Faithful]
    [T.IsRightKanExtension ε] :
    T.IsRightKanExtension
      ((Functor.associator P Q T).hom ≫ Functor.whiskerLeft P ε) := by
  let K := (Functor.whiskeringLeft A B H).obj P
  let lift (s : Functor.RightExtension (P ⋙ Q) (P ⋙ G)) : s.left ⟶ T :=
    T.liftOfIsRightKanExtension ε s.left
      (K.preimage ((Functor.associator P Q s.left).inv ≫ s.hom))
  have fac (s : Functor.RightExtension (P ⋙ Q) (P ⋙ G)) :
      Functor.whiskerLeft (P ⋙ Q) (lift s) ≫
        ((Functor.associator P Q T).hom ≫ Functor.whiskerLeft P ε) = s.hom := by
    as_aux_lemma =>
      apply NatTrans.ext
      funext X
      have h := congrArg (fun t ↦ t.app (P.obj X))
        (T.liftOfIsRightKanExtension_fac ε s.left
          (K.preimage ((Functor.associator P Q s.left).inv ≫ s.hom)))
      have hp := congrArg (fun t ↦ t.app X)
        (K.map_preimage ((Functor.associator P Q s.left).inv ≫ s.hom))
      change (lift s).app (Q.obj (P.obj X)) ≫ (𝟙 _ ≫ ε.app (P.obj X)) = _
      rw [Category.id_comp]
      exact (h.trans hp).trans (Category.id_comp _)
  clear_value lift
  refine ⟨⟨IsTerminal.ofUniqueHom
    (fun s ↦ CostructuredArrow.homMk (lift s) (fac s)) ?_⟩⟩
  as_aux_lemma =>
    intro s m
    apply CostructuredArrow.hom_ext
    apply T.hom_ext_of_isRightKanExtension ε
    apply K.map_injective
    have h := CostructuredArrow.w m
    apply NatTrans.ext
    funext X
    have h' := congrArg (fun t ↦ t.app X) h
    have h'' := congrArg (fun t ↦ t.app X) (fac s)
    have hh := h'.trans h''.symm
    change m.left.app (Q.obj (P.obj X)) ≫ (𝟙 _ ≫ ε.app (P.obj X)) = _ at hh
    rw [Category.id_comp] at hh
    change _ = (lift s).app (Q.obj (P.obj X)) ≫ (𝟙 _ ≫ ε.app (P.obj X)) at hh
    rw [Category.id_comp] at hh
    exact hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport a right Kan extension across isomorphisms of its source diagram and target. -/
private theorem kan_change
    {A D H : Type*} [Category A] [Category D] [Category H]
    {Q Q' : A ⥤ D} {G G' : A ⥤ H} (T : D ⥤ H)
    (i : Q ≅ Q') (j : G ≅ G') (ε : Q ⋙ T ⟶ G)
    [T.IsRightKanExtension ε] :
    T.IsRightKanExtension (Functor.whiskerRight i.inv T ≫ ε ≫ j.hom) := by
  let Φ := Functor.rightExtensionEquivalenceOfIso₁ i G
  have ht := (IsTerminal.isTerminalIffObj Φ.functor
    (Functor.RightExtension.mk T ε)).1 (T.isUniversalOfIsRightKanExtension ε)
  have hε : T.IsRightKanExtension (Functor.whiskerRight i.inv T ≫ ε) := ⟨⟨ht⟩⟩
  exact (Functor.isRightKanExtension_iff_of_iso₂
    (Functor.whiskerRight i.inv T ≫ ε)
    (Functor.whiskerRight i.inv T ≫ ε ≫ j.hom) j (Iso.refl T) (by simp)).1 hε

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport a homotopy-level derived counit to complexes, with abstract categories.
The quotient comparison is invertible, so the transport preserves every computation
component that is already an isomorphism. -/
private theorem cochain_derived_counit
    {A₀ B₀ : Type*} [Category A₀] [Category B₀] [Abelian A₀] [Abelian B₀]
    [HasDerivedCategory A₀] [HasDerivedCategory B₀]
    (E : A₀ ⥤ B₀) [E.Additive]
    (T : DerivedCategory A₀ ⥤ DerivedCategory B₀)
    (ε : DerivedCategory.Qh ⋙ T ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [T.IsRightKanExtension ε] :
    ∃ β : DerivedCategory.Q ⋙ T ⟶
        E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q,
      T.IsRightKanExtension β ∧
        ∀ P : CochainComplex A₀ ℤ,
          IsIso (ε.app ((HomotopyCategory.quotient A₀ (.up ℤ)).obj P)) →
            IsIso (β.app P) := by
  let q := HomotopyCategory.quotient A₀ (.up ℤ)
  let H := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let α := (Functor.associator q DerivedCategory.Qh T).hom ≫ Functor.whiskerLeft q ε
  have : T.IsRightKanExtension α := kan_precomp q DerivedCategory.Qh T H ε
  let i := DerivedCategory.quotientCompQhIso A₀
  let j : q ⋙ H ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B₀)
  let β : DerivedCategory.Q ⋙ T ⟶
      E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight i.inv T ≫ α ≫ j.hom
  refine ⟨β, kan_change T i j α, ?_⟩
  intro P hP
  have := hP
  dsimp [β, α]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem resolving_derived_cochain
    {M E : Type*} [Category M] [Abelian M] [HasDerivedCategory M]
    [Category E] [Abelian E] [HasDerivedCategory E]
    (T : M ⥤ E) [T.Additive] (S₀ : CochainComplex M ℤ → Prop)
    (hres₀ : ∀ P : CochainComplex M ℤ,
      ∃ (K : CochainComplex M ℤ) (f : K ⟶ P), S₀ K ∧ QuasiIso f)
    (hT : ∀ {P P' : CochainComplex M ℤ} (f : P ⟶ P'), S₀ P →
      S₀ P' → QuasiIso f →
        QuasiIso ((T.mapHomologicalComplex (.up ℤ)).map f)) :
    ∃ (LT : DerivedCategory M ⥤ DerivedCategory E)
      (β : DerivedCategory.Q ⋙ LT ⟶ T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q),
      LT.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso M (.up ℤ)) ∧
        ∀ P : CochainComplex M ℤ, S₀ P → IsIso (β.app P) := by
  let q := HomotopyCategory.quotient M (.up ℤ)
  let H := T.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let S : Set (HomotopyCategory M (.up ℤ)) :=
    {X | ∃ P : CochainComplex M ℤ, S₀ P ∧ q.obj P = X}
  have hres (X : HomotopyCategory M (.up ℤ)) :
      ∃ (Y : HomotopyCategory M (.up ℤ)) (f : Y ⟶ X),
        Y ∈ S ∧ HomotopyCategory.quasiIso M (.up ℤ) f := by
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨K, f, hK, hf⟩ := hres₀ P
    exact ⟨q.obj K, q.map f, ⟨K, hK, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf⟩
  have hinv (X Y : HomotopyCategory M (.up ℤ)) (f : X ⟶ Y)
      (hX : X ∈ S) (hY : Y ∈ S)
      (hf : HomotopyCategory.quasiIso M (.up ℤ) f) : IsIso (H.map f) := by
    obtain ⟨P, hP, rfl⟩ := hX
    obtain ⟨P', hP', rfl⟩ := hY
    obtain ⟨g, rfl⟩ := q.map_surjective f
    have hg := (HomotopyCategory.quotient_map_mem_quasiIso_iff g).1 hf
    have ht := hT g hP hP' hg
    change IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient E (.up ℤ)).map
        ((T.mapHomologicalComplex (.up ℤ)).map g)))
    exact Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso E (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 ht)
  obtain ⟨_, LT, ε, hu, _, hc⟩ :=
    Functor.leftDerived_from_resolvingClass M (DerivedCategory E) H S hres hinv
  have : LT.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso M (.up ℤ)) := hu
  have : LT.IsRightKanExtension ε :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension LT ε
      (HomotopyCategory.quasiIso M (.up ℤ))
  obtain ⟨β, hβ, hcomp⟩ := cochain_derived_counit T LT ε
  exact ⟨LT, β, ⟨hβ⟩, fun P hP ↦ hcomp P (hc (q.obj P) ⟨P, hP, rfl⟩)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem change_preserves_kFlat_quasiIso
    {R S : Sheaf J CommRingCat.{u}}
    (φ : R ⟶ S) {P P' : Cx R} (f : P ⟶ P')
    (hP : P.IsKFlatTensor) (hP' : P'.IsKFlatTensor) (hf : QuasiIso f) :
    QuasiIso (((change φ).mapHomologicalComplex (.up ℤ)).map f) := by
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod S)
  let d := derivedExtension φ
  have : IsIso (d.comparison.app P) := d.computation P hP
  have : IsIso (d.comparison.app P') := d.computation P' hP'
  have : IsIso ((Q R).map f) := (DerivedCategory.isIso_Q_map_iff_quasiIso (Mod R) f).2 hf
  have h := d.comparison.naturality f
  dsimp only [Functor.comp_map] at h
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso (Mod S) _).1
  have : IsIso (d.comparison.app P ≫ (Q S).map
      (((change φ).mapHomologicalComplex (.up ℤ)).map f)) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_left (d.comparison.app P) _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_tower_unit
    {A₀ A₁ D₀ D₁ : Type*}
    [Category A₀] [Category A₁] [Category D₀] [Category D₁]
    (q : A₀ ⥤ D₀) (q' : A₁ ⥤ D₁) (W : MorphismProperty A₀)
    [q.IsLocalization W] {G T : A₀ ⥤ A₁} {F : A₁ ⥤ A₀}
    (ν : 𝟭 A₀ ⟶ G ⋙ F) (η : G ⟶ T) (DG LT : D₀ ⥤ D₁) (RF : D₁ ⥤ D₀)
    (α : q ⋙ DG ≅ G ⋙ q') (β : q ⋙ LT ⟶ T ⋙ q')
    [LT.IsLeftDerivedFunctor β W] (γ : F ⋙ q ⟶ q' ⋙ RF) :
    ∃ unit : 𝟭 D₀ ⟶ LT ⋙ RF,
      ∀ X, unit.app (q.obj X) ≫ RF.map (β.app X) =
        q.map (ν.app X ≫ F.map (η.app X)) ≫ γ.app (T.obj X) := by
  have : (DG ⋙ RF).IsLeftDerivedFunctor
      ((Functor.associator q DG RF).inv ≫ Functor.whiskerRight α.hom RF) W :=
    Functor.isLeftDerivedFunctor_of_inverts W _
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight α RF)
  let δ := (Functor.associator q DG RF).inv ≫ Functor.whiskerRight α.hom RF
  let θ := q.rightUnitor.hom ≫ q.leftUnitor.inv ≫ Functor.whiskerRight ν q ≫
    (Functor.associator G F q).hom ≫ Functor.whiskerLeft G γ ≫
      (Functor.associator G q' RF).inv
  let u := (DG ⋙ RF).leftDerivedLift δ W (𝟭 D₀) θ
  let t := LT.leftDerivedLift β W DG (α.hom ≫ Functor.whiskerRight η q')
  refine ⟨u ≫ Functor.whiskerRight t RF, ?_⟩
  intro X
  change (u.app (q.obj X) ≫ RF.map (t.app (q.obj X))) ≫ RF.map (β.app X) = _
  rw [Category.assoc, ← RF.map_comp,
    LT.leftDerived_fac_app β W DG (α.hom ≫ Functor.whiskerRight η q') X]
  change u.app (q.obj X) ≫ RF.map (α.hom.app X ≫ q'.map (η.app X)) = _
  have hu : u.app (q.obj X) ≫ RF.map (α.hom.app X) =
      q.map (ν.app X) ≫ γ.app (G.obj X) := by
    have hfac := (DG ⋙ RF).leftDerived_fac_app δ W (𝟭 D₀) θ X
    change u.app (q.obj X) ≫ (𝟙 _ ≫ RF.map (α.hom.app X)) =
      𝟙 _ ≫ 𝟙 _ ≫ q.map (ν.app X) ≫ 𝟙 _ ≫ γ.app (G.obj X) ≫ 𝟙 _ at hfac
    simpa only [Category.id_comp, Category.comp_id] using hfac
  rw [RF.map_comp, ← Category.assoc, hu]
  have hn := γ.naturality (η.app X)
  change q.map (F.map (η.app X)) ≫ γ.app (T.obj X) =
    γ.app (G.obj X) ≫ RF.map (q'.map (η.app X)) at hn
  rw [Category.assoc, ← hn, ← Category.assoc, ← q.map_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem module_kFlat_resolution {R : Sheaf J CommRingCat.{u}} (P : Cx R) :
    ∃ (K : Cx R) (f : K ⟶ P), K.IsKFlatTensor ∧ QuasiIso f := by
  obtain ⟨K, f, hK, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
  exact ⟨K, f, (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat K).1 hK, hf⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem reductionTower_preserves_kFlat_quasiIso (b : Bool)
    {P P' : Cx (coefficients J A I b)} (f : P ⟶ P')
    (hP : P.IsKFlatTensor) (hP' : P'.IsKFlatTensor) (hf : QuasiIso f) :
    QuasiIso (((reductionTower J A I b).mapHomologicalComplex (.up ℤ)).map f) := by
  apply (HomologicalComplex.quasiIso_iff_evaluation _).2
  intro n
  have he := change_preserves_kFlat_quasiIso J (finiteMap J A I b n.unop) f hP hP' hf
  have := (siteRestrictScalars_exact (finiteMap J A I b n.unop)).1
  have := (siteRestrictScalars_exact (finiteMap J A I b n.unop)).2
  exact inferInstanceAs (QuasiIso
    (((res (finiteMap J A I b n.unop)).mapHomologicalComplex (.up ℤ)).map
      (((change (finiteMap J A I b n.unop)).mapHomologicalComplex (.up ℤ)).map f)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryUnit_spec (J : GrothendieckTopology C)
    (A : Type u) [CommRing A] (I : Ideal A) (b : Bool)
    (P : Cx (coefficients J A I b)) (q : ℤ) (n : ℕ) :
    (ordinaryUnit J A I b P).f q ≫
      limit.π ((reductionComplex J A I b P).X q) (op n) =
        ((reductionUnit J A I b).app (P.X q)).app (op n) :=
  (ordinaryUnit_existsUnique J A I b P).exists.choose_spec q n

attribute [local irreducible] ordinaryUnit

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_tower_presentation
    {M : Type*} [Category M] [Abelian M] [HasDerivedCategory M]
    [HasDerivedCategory (ℕᵒᵖ ⥤ M)] [HasLimitsOfShape ℕᵒᵖ M]
    [(lim : (ℕᵒᵖ ⥤ M) ⥤ M).Additive]
    (T : M ⥤ ℕᵒᵖ ⥤ M) [T.Additive]
    (η : (Functor.const ℕᵒᵖ : M ⥤ ℕᵒᵖ ⥤ M) ⟶ T)
    (S₀ : CochainComplex M ℤ → Prop)
    (hres : ∀ P : CochainComplex M ℤ,
      ∃ (K : CochainComplex M ℤ) (f : K ⟶ P), S₀ K ∧ QuasiIso f)
    (hT : ∀ {P P' : CochainComplex M ℤ} (f : P ⟶ P'), S₀ P → S₀ P' →
      QuasiIso f → QuasiIso ((T.mapHomologicalComplex (.up ℤ)).map f))
    (RF : DerivedCategory (ℕᵒᵖ ⥤ M) ⥤ DerivedCategory M)
    (γ : complexLimitFunctor M ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (u : ∀ P : CochainComplex M ℤ,
      P ⟶ (complexLimitFunctor M).obj ((T.mapHomologicalComplex (.up ℤ)).obj P))
    (hucoord : ∀ (P : CochainComplex M ℤ) (q : ℤ) (n : ℕ),
      (u P).f q ≫ limit.π (T.obj (P.X q)) (op n) = (η.app (P.X q)).app (op n)) :
    ∃ (LT : DerivedCategory M ⥤ DerivedCategory (ℕᵒᵖ ⥤ M))
      (β : DerivedCategory.Q ⋙ LT ⟶ T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (unit : 𝟭 (DerivedCategory M) ⟶ LT ⋙ RF),
      LT.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso M (.up ℤ)) ∧
      (∀ P : CochainComplex M ℤ, S₀ P → IsIso (β.app P)) ∧
      (∀ P : CochainComplex M ℤ,
        unit.app (DerivedCategory.Q.obj P) ≫ RF.map (β.app P) =
          DerivedCategory.Q.map (u P) ≫
            γ.app ((T.mapHomologicalComplex (.up ℤ)).obj P)) := by
  obtain ⟨LT, β, hu, hc⟩ := resolving_derived_cochain T S₀ hres hT
  have : LT.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso M (.up ℤ)) := hu
  let G : M ⥤ ℕᵒᵖ ⥤ M := Functor.const ℕᵒᵖ
  let ηC := NatTrans.mapHomologicalComplex η (.up ℤ)
  let ν : 𝟭 (CochainComplex M ℤ) ⟶
      G.mapHomologicalComplex (.up ℤ) ⋙ complexLimitFunctor M :=
    { app := fun P ↦
        { f := fun q ↦ constLimAdj.unit.app (P.X q)
          comm' := fun i j _ ↦ (constLimAdj.unit.naturality (P.d i j)).symm }
      naturality := fun P P' f ↦ by
        ext q
        exact constLimAdj.unit.naturality (f.f q) }
  obtain ⟨unit, hunit⟩ := derived_tower_unit DerivedCategory.Q DerivedCategory.Q
    (HomologicalComplex.quasiIso M (.up ℤ))
    ν ηC
    G.mapDerivedCategory LT RF G.mapDerivedCategoryFactors β γ
  refine ⟨LT, β, unit, hu, hc, ?_⟩
  intro P
  have hord : ν.app P ≫
      (complexLimitFunctor M).map (ηC.app P) = u P := by
    apply (complexLimitUnit T η P).unique
    · intro q n
      change (limit.lift _ { pt := P.X q, π := 𝟙 _ } ≫
        limMap (η.app (P.X q))) ≫ limit.π _ (op n) = _
      rw [Category.assoc, limMap_π, limit.lift_π_assoc]
      change 𝟙 _ ≫ _ = _
      rw [Category.id_comp]
    · exact hucoord P
  have h := hunit P
  change unit.app (DerivedCategory.Q.obj P) ≫ RF.map (β.app P) =
    DerivedCategory.Q.map
      (ν.app P ≫
        (complexLimitFunctor M).map (ηC.app P)) ≫
      γ.app ((T.mapHomologicalComplex (.up ℤ)).obj P) at h
  rw [hord] at h
  exact h

private theorem derived_tower_presentation_cps
    {M : Type*} [Category M] [Abelian M] [HasDerivedCategory M]
    [HasDerivedCategory (ℕᵒᵖ ⥤ M)] [HasLimitsOfShape ℕᵒᵖ M]
    [(lim : (ℕᵒᵖ ⥤ M) ⥤ M).Additive]
    (T : M ⥤ ℕᵒᵖ ⥤ M) [T.Additive]
    (η : (Functor.const ℕᵒᵖ : M ⥤ ℕᵒᵖ ⥤ M) ⟶ T)
    (S₀ : CochainComplex M ℤ → Prop)
    (hres : ∀ P : CochainComplex M ℤ,
      ∃ (K : CochainComplex M ℤ) (f : K ⟶ P), S₀ K ∧ QuasiIso f)
    (hT : ∀ {P P' : CochainComplex M ℤ} (f : P ⟶ P'), S₀ P → S₀ P' →
      QuasiIso f → QuasiIso ((T.mapHomologicalComplex (.up ℤ)).map f))
    (RF : DerivedCategory (ℕᵒᵖ ⥤ M) ⥤ DerivedCategory M)
    (γ : complexLimitFunctor M ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (u : ∀ P : CochainComplex M ℤ,
      P ⟶ (complexLimitFunctor M).obj ((T.mapHomologicalComplex (.up ℤ)).obj P))
    (hucoord : ∀ (P : CochainComplex M ℤ) (q : ℤ) (n : ℕ),
      (u P).f q ≫ limit.π (T.obj (P.X q)) (op n) = (η.app (P.X q)).app (op n)) (X : Type*)
    (mk : ∀ (LT : DerivedCategory M ⥤ DerivedCategory (ℕᵒᵖ ⥤ M))
      (β : DerivedCategory.Q ⋙ LT ⟶ T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (unit : 𝟭 (DerivedCategory M) ⟶ LT ⋙ RF),
      LT.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso M (.up ℤ)) →
      (∀ P : CochainComplex M ℤ, S₀ P → IsIso (β.app P)) →
      (∀ P : CochainComplex M ℤ,
        unit.app (DerivedCategory.Q.obj P) ≫ RF.map (β.app P) =
          DerivedCategory.Q.map (u P) ≫
            γ.app ((T.mapHomologicalComplex (.up ℤ)).obj P)) → X) : Nonempty X := by
  obtain ⟨LT, β, unit, hu, hc, he⟩ :=
    derived_tower_presentation T η S₀ hres hT RF γ u hucoord
  exact ⟨mk LT β unit hu hc he⟩

/-- The universal derived-tower laws and the actual quotient-unit computation.
Naming this predicate keeps the dependent record small; its normalization is unchanged.
Source: Stacks 099M, 06YY, 0940
(auxiliary; not a blueprint node). -/
def QuotientPresentationLaws (b : Bool)
    (tower : D (coefficients J A I b) ⥤ TD (coefficients J A I b))
    (comparison : Q (coefficients J A I b) ⋙ tower ⟶
      (reductionTower J A I b).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        TQ (coefficients J A I b))
    (unit : 𝟭 (D (coefficients J A I b)) ⟶ tower ⋙ rlim (coefficients J A I b)) : Prop :=
  tower.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (Mod (coefficients J A I b)) (ComplexShape.up ℤ)) ∧
    (∀ P : Cx (coefficients J A I b), P.IsKFlatTensor →
      (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) → IsIso (comparison.app P)) ∧
    (∀ P : Cx (coefficients J A I b), P.IsKFlatTensor →
      (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        unit.app ((Q (coefficients J A I b)).obj P) ≫
          (rlim (coefficients J A I b)).map (comparison.app P) =
        (Q (coefficients J A I b)).map (ordinaryUnit J A I b P) ≫
          (limitComparison (coefficients J A I b)).app (reductionComplex J A I b P))

set_option genSizeOf false in
set_option genInjectivity false in
/-- A universal derived strict reduction tower with its prescribed completion unit.
The laws specify the actual quotient maps and total right derived strict inverse limit.
Source: Stacks 099M, 06YY, 0940
(auxiliary; not a blueprint node). -/
structure QuotientPresentation (b : Bool) where
  tower : D (coefficients J A I b) ⥤ TD (coefficients J A I b)
  comparison : Q (coefficients J A I b) ⋙ tower ⟶
    (reductionTower J A I b).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      TQ (coefficients J A I b)
  unit : 𝟭 (D (coefficients J A I b)) ⟶ tower ⋙ rlim (coefficients J A I b)
  laws : QuotientPresentationLaws J A I b tower comparison unit

section

attribute [local irreducible] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem module_tower_presentation {O : Sheaf J CommRingCat.{u}}
    (T : Mod O ⥤ ℕᵒᵖ ⥤ Mod O) [T.Additive]
    (η : Functor.const ℕᵒᵖ ⟶ T) (S : Cx O → Prop)
    (hres : ∀ P : Cx O, ∃ (K : Cx O) (f : K ⟶ P), S K ∧ QuasiIso f)
    (hT : ∀ {P P' : Cx O} (f : P ⟶ P'), S P → S P' →
      QuasiIso f → QuasiIso ((T.mapHomologicalComplex (.up ℤ)).map f))
    (u : ∀ P : Cx O,
      P ⟶ (ordinaryLimit O).obj ((T.mapHomologicalComplex (.up ℤ)).obj P))
    (hu : ∀ (P : Cx O) (q : ℤ) (n : ℕ),
      (u P).f q ≫ limit.π (T.obj (P.X q)) (op n) = (η.app (P.X q)).app (op n))
    (X : Type*)
    (mk : ∀ (LT : D O ⥤ TD O)
      (β : Q O ⋙ LT ⟶ T.mapHomologicalComplex (.up ℤ) ⋙ TQ O)
      (unit : 𝟭 (D O) ⟶ LT ⋙ rlim O),
      LT.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso (Mod O) (.up ℤ)) →
      (∀ P : Cx O, S P → IsIso (β.app P)) →
      (∀ P : Cx O, unit.app ((Q O).obj P) ≫ (rlim O).map (β.app P) =
        (Q O).map (u P) ≫ (limitComparison O).app
          ((T.mapHomologicalComplex (.up ℤ)).obj P)) → X) : Nonempty X := by
  let : Abelian (Mod O) :=
    { (inferInstance : Abelian (Mod O)) with
      toPreadditive := (inferInstance : Preadditive (Mod O)) }
  let := HasDerivedCategory.standard (Mod O)
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod O)
  have : (lim : (ℕᵒᵖ ⥤ Mod O) ⥤ Mod O).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact derived_tower_presentation_cps T η S hres hT (rlim O) (limitComparison O) u hu X mk

set_option backward.isDefEq.respectTransparency.types true in
/-- Strict diagram K-flat replacements and the universal derived limit supply this pair.
Source: Stacks 06YY, 0940, 099M
(auxiliary; not a blueprint node).
Proof: use a single flat-term K-flat representative for the entire reduction tower.
Each scalar extension preserves quasi-isomorphisms between such representatives, so the
resolving-class localization theorem gives the displayed universal tower and computation.
Apply total right derived limit to its strict quotient units. Their naturality and
invariance under quasi-isomorphisms descend the unit to D(O). The comparison square is
its construction, and determines it because every object has such a representative. -/
theorem quotientPresentation_exists (b : Bool) : Nonempty (QuotientPresentation J A I b) := by
  let : Abelian (Mod (coefficients J A I b)) :=
    { (inferInstance : Abelian (Mod (coefficients J A I b))) with
      toPreadditive := (inferInstance : Preadditive (Mod (coefficients J A I b))) }
  let : Abelian (ℕᵒᵖ ⥤ Mod (coefficients J A I b)) :=
    { (inferInstance : Abelian (ℕᵒᵖ ⥤ Mod (coefficients J A I b))) with
      toPreadditive :=
        (inferInstance : Preadditive (ℕᵒᵖ ⥤ Mod (coefficients J A I b))) }
  exact module_tower_presentation (J := J) (reductionTower J A I b)
    (reductionUnit J A I b) (fun P ↦ P.IsKFlatTensor) (module_kFlat_resolution J)
    (reductionTower_preserves_kFlat_quasiIso J A I b)
    (ordinaryUnit J A I b) (ordinaryUnit_spec J A I b) (QuotientPresentation J A I b)
    (fun LT β unit hu hc he ↦
      ⟨LT, β, unit, hu, fun P hk _ ↦ hc P hk, fun P _ _ ↦ he P⟩)

end

/-- Choose the universally specified reduction tower and normalized unit.
Source: Stacks 099M (auxiliary; not a blueprint node). -/
def quotientPresentation (b : Bool) : QuotientPresentation J A I b :=
  Classical.choice (quotientPresentation_exists J A I b)

attribute [local irreducible] quotientPresentation

/-- Quotient-tower derived completion, using total right derived inverse limit.
Source: Stacks 099M (auxiliary; not a blueprint node). -/
def completion (b : Bool) : D (coefficients J A I b) ⥤ D (coefficients J A I b) :=
  (quotientPresentation J A I b).tower ⋙ rlim (coefficients J A I b)

/-- Its prescribed quotient-tower completion unit. Source: Stacks 099M
(auxiliary; not a blueprint node). -/
def completionUnit (b : Bool) : 𝟭 (D (coefficients J A I b)) ⟶ completion J A I b :=
  (quotientPresentation J A I b).unit

/-- The existing strict Koszul presentation, for the images of the given generators.
Source: Stacks 0A0E (auxiliary; not a blueprint node). -/
abbrev KoszulPresentation (b : Bool) (r : ℕ) (a : Fin r → A) :=
  letI := HasDerivedCategory.standard (Mod (coefficients J A I b))
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod (coefficients J A I b))
  RingedKoszulLimitPresentation (coefficients J A I b) r
    (fun i ↦ algebraSection (baseMap J A I b) (a i))

/-- Completion from the actual dual Koszul tensor tower with transitions (a_i,1).
Source: Stacks 0A0E (auxiliary; not a blueprint node). -/
def koszulCompletion {b : Bool} {r : ℕ} {a : Fin r → A}
    (K : KoszulPresentation J A I b r a) : D (coefficients J A I b) ⥤
      D (coefficients J A I b) :=
  letI := HasDerivedCategory.standard (Mod (coefficients J A I b))
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod (coefficients J A I b))
  K.completion

/-- The specified degree-zero Koszul unit in the standard localization.
Source: Stacks 0A0E (auxiliary; not a blueprint node). -/
def koszulUnit {b : Bool} {r : ℕ} {a : Fin r → A}
    (K : KoszulPresentation J A I b r a) (M : D (coefficients J A I b)) :
    M ⟶ (koszulCompletion J A I K).obj M :=
  letI := HasDerivedCategory.standard (Mod (coefficients J A I b))
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod (coefficients J A I b))
  K.unit M

end CategoryTheory.ConstantCompletion
