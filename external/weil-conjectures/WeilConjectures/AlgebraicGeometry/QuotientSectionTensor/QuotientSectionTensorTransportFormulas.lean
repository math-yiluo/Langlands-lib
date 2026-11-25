/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
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
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-! # Scalar section tensor transport formulas

## References

* Stacks, Cohomology on Sites, Tags 06YY and 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local instance] AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient
open ModuleRingedComparison

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

/-- The normalized scalar localization square without its identity comparison.
Expand the termwise functor comparison in ScalarSectionNormalized. The comparison
for the identity is the identity cochain map; localization preserves its identity.
Remove that final identity and identify the mapped ordinary comparison components. -/
theorem section_scalar_normalization (T : Scheme.{u})
    (c : ScalarSectionData a T) (hc : ScalarSectionNormalized a T c)
    (P : CochainComplex (Modules Λ T) ℤ) :
    c.derived.hom.app (DerivedCategory.Q.obj P) ≫
      c.model.T.map (sectionLocalizationComparison Λ T P).hom ≫
      c.model.ε.app (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P) =
    (derivedFunctor Λ' T).map (compute a T P) ≫
      (sectionLocalizationComparison Λ' T
        (((extension a T).mapHomologicalComplex (.up ℤ)).obj P)).hom ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c.ordinary (.up ℤ)).hom.app P) := by
  have h := hc.2 P
  simp only [Functor.mapHomologicalComplexCompIso, Iso.refl_inv,
    NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex_id,
    NatTrans.id_app] at h
  erw [CategoryTheory.Functor.map_id] at h
  simpa only [Category.comp_id, NatIso.mapHomologicalComplex] using h

private theorem paste_total_path {𝒞 : Type*} [Category 𝒞]
    {A B C D E F G H I J J₀ K L M N P : 𝒞}
    {a : A ⟶ B} {b : B ⟶ C} {c : C ⟶ D} {d : D ⟶ E}
    {e : E ⟶ F} {f : F ⟶ G} {g : A ⟶ H} {h : H ⟶ I}
    {i : B ⟶ I} {j : I ⟶ J} {k : J ⟶ E} {l : J ⟶ J₀}
    {m₀ : J₀ ⟶ F} {m : H ⟶ K} {n : K ⟶ L} {o : L ⟶ J₀}
    {p : L ⟶ M} {q : M ⟶ N} {r : N ⟶ G} {s : K ⟶ P} {t : P ⟶ M}
    (hfac : b ≫ c ≫ d = i ≫ j ≫ k) (hnat : k ≫ e = l ≫ m₀)
    (hp : g ≫ h = a ≫ i) (hscalar : m ≫ n ≫ o = h ≫ j ≫ l)
    (htotal : p ≫ q ≫ r = o ≫ m₀ ≫ f) (hlocal : s ≫ t = n ≫ p) :
    a ≫ b ≫ c ≫ d ≫ e ≫ f = g ≫ m ≫ s ≫ t ≫ q ≫ r := by
  rw [reassoc_of% hfac, reassoc_of% hnat, ← reassoc_of% hp,
    ← reassoc_of% hscalar, ← htotal, ← reassoc_of% hlocal]

private theorem paste_internal_path {𝒞 : Type*} [Category 𝒞]
    {A G H K M N O P U U₀ V X Y : 𝒞}
    {l : A ⟶ G} {g : A ⟶ H} {m : H ⟶ K} {s : K ⟶ P}
    {t : P ⟶ M} {q : M ⟶ N} {r : N ⟶ G}
    {u : A ⟶ U} {v : U ⟶ O} {w : O ⟶ P} {x : O ⟶ V}
    {y : V ⟶ X} {z : X ⟶ N} {τ : U ⟶ U₀} {aa : U₀ ⟶ V}
    {ab : X ⟶ Y} {ac : Y ⟶ G}
    (hl : l = g ≫ m ≫ s ≫ t ≫ q ≫ r)
    (hi : g ≫ m ≫ s = u ≫ v ≫ w)
    (hf : x ≫ y ≫ z = w ≫ t ≫ q)
    (ht : v ≫ x = τ ≫ aa) (hq : ab ≫ ac = z ≫ r) :
    l = u ≫ τ ≫ aa ≫ y ≫ ab ≫ ac := by
  rw [hl, reassoc_of% hi, ← reassoc_of% hf, reassoc_of% ht, ← hq]

private theorem paste_section_path {𝒞 : Type*} [Category 𝒞]
    {A B C D E F G H I J : 𝒞}
    {a : A ⟶ B} {b : B ⟶ C} {c : C ⟶ D}
    {d : D ⟶ E} {e : E ⟶ F} {f : F ⟶ G}
    {g : D ⟶ H} {h : H ⟶ I} {i : I ⟶ G}
    {j : C ⟶ J} {k : J ⟶ H}
    (hb : g ≫ h ≫ i = d ≫ e ≫ f) (hn : c ≫ g = j ≫ k) :
    a ≫ b ≫ c ≫ d ≫ e ≫ f = a ≫ b ≫ j ≫ k ≫ h ≫ i := by
  rw [← hb, reassoc_of% hn]

private theorem iso_of_eq {𝒞 : Type*} [Category 𝒞] {A B : 𝒞}
    {f g : A ⟶ B} (h : f = g) [IsIso g] : IsIso f := by
  rw [h]
  infer_instance

private theorem map_pair_iso {A B C : Type*} [Category A] [Category B] [Category C]
    (G : A × B ⥤ C) {X X' : A} {Y Y' : B} (f : X ⟶ X') (g : Y ⟶ Y')
    [IsIso f] [IsIso g] : IsIso (G.map (Prod.mkHom f g)) := by
  have : IsIso (Prod.mkHom f g) :=
    (isIso_prod_iff (f := Prod.mkHom f g)).mpr ⟨inferInstance, inferInstance⟩
  infer_instance

private theorem pair_conjugation {A B C : Type*} [Category A] [Category B] [Category C]
    (G : A × B ⥤ C) {X X' : A} {Y Y' : B} (e : X ≅ X') (f : Y ≅ Y')
    {U V : C} {u : U ⟶ V} {v : V ⟶ G.obj (X, Y)} {w : U ⟶ G.obj (X', Y')}
    (h : u ≫ v ≫ G.map (Prod.mkHom e.hom f.hom) = w) :
    u ≫ v = w ≫ G.map (Prod.mkHom e.inv f.inv) := by
  have : IsIso (G.map (Prod.mkHom e.hom f.hom)) := map_pair_iso G _ _
  apply (cancel_mono (G.map (Prod.mkHom e.hom f.hom))).mp
  simpa only [Category.assoc, ← G.map_comp, prod_comp, Iso.inv_hom_id,
    ← prod_id, CategoryTheory.Functor.map_id, Category.comp_id] using h

private theorem map_pair_three {A B C : Type*} [Category A] [Category B] [Category C]
    (G : A × B ⥤ C) {x₀ x₁ x₂ x₃ y₁ y₂ : A}
    {z₀ z₁ z₂ z₃ w₁ w₂ : B}
    {a : x₀ ⟶ x₁} {b : x₁ ⟶ x₂} {c : x₂ ⟶ x₃}
    {d : x₀ ⟶ y₁} {e : y₁ ⟶ y₂} {f : y₂ ⟶ x₃}
    {a' : z₀ ⟶ z₁} {b' : z₁ ⟶ z₂} {c' : z₂ ⟶ z₃}
    {d' : z₀ ⟶ w₁} {e' : w₁ ⟶ w₂} {f' : w₂ ⟶ z₃}
    (h₁ : a ≫ b ≫ c = d ≫ e ≫ f) (h₂ : a' ≫ b' ≫ c' = d' ≫ e' ≫ f') :
    G.map (Prod.mkHom a a') ≫ G.map (Prod.mkHom b b') ≫ G.map (Prod.mkHom c c') =
      G.map (Prod.mkHom d d') ≫ G.map (Prod.mkHom e e') ≫ G.map (Prod.mkHom f f') := by
  simp only [← G.map_comp, prod_comp]
  exact congrArg G.map (congrArg₂ Prod.mkHom h₁ h₂)

private theorem total_tensor_map
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ X)]
    (Z : Scheme.{u}) {P P' Q Q' : CochainComplex (ModuleRingedComparison.modules Λ Z) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    (ModuleRingedComparison.totalTensor Λ Z).map (Prod.mkHom f g) = f ⊗ₘ g := by
  change (f ▷ _) ≫ (_ ◁ g) = f ⊗ₘ g
  exact (tensorHom_def f g).symm

private theorem tensor_comparison_natural
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ X)]
    (Z : Scheme.{u}) {A A' B B' : DerivedCategory (ModuleRingedComparison.internalModules Λ Z)}
    (f : A ⟶ A') (g : B ⟶ B') :
    (ModuleRingedComparison.derivedEquivalence Λ Z).functor.map (f ⊗ₘ g) ≫
        (ModuleRingedComparison.tensorComparison Λ Z).hom.app (A', B') =
      (ModuleRingedComparison.tensorComparison Λ Z).hom.app (A, B) ≫
        (ModuleRingedComparison.tensor Λ Z).map (Prod.mkHom
          ((ModuleRingedComparison.derivedEquivalence Λ Z).functor.map f)
          ((ModuleRingedComparison.derivedEquivalence Λ Z).functor.map g)) := by
  simpa only [Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map,
    CondensedRing.derivedTensor, curriedTensor_obj_map, curriedTensor_map_app,
    ← MonoidalCategory.tensorHom_def] using
    (ModuleRingedComparison.tensorComparison Λ Z).hom.naturality (Prod.mkHom f g)

private theorem localization_tensor_natural
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ X)]
    (Z : Scheme.{u}) {P P' Q Q' : CochainComplex (ModuleRingedComparison.modules Λ Z) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    let q (K L : CochainComplex (ModuleRingedComparison.modules Λ Z) ℤ) :
        (ModuleRingedComparison.tensor Λ Z).obj (DerivedCategory.Q.obj K,
          DerivedCategory.Q.obj L) ⟶ DerivedCategory.Q.obj (K ⊗ L) :=
      (ModuleRingedComparison.qTensor Λ Z).app (K, L)
    (ModuleRingedComparison.tensor Λ Z).map
        (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫ q P' Q' =
      q P Q ≫ DerivedCategory.Q.map (f ⊗ₘ g) := by
  dsimp only
  have hn := (ModuleRingedComparison.qTensor Λ Z).naturality (Prod.mkHom f g)
  simp only [Functor.comp_map, Functor.prod_map] at hn
  rw [total_tensor_map] at hn
  exact hn

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)] in
private theorem section_resolving_iff (T : Scheme.{u})
    (P : CochainComplex (Modules Λ T) ℤ) :
    ((∀ A : CochainComplex (Modules Λ T) ℤ, A.Acyclic →
      (CochainComplex.mapBifunctor A P (curriedTensor (Modules Λ T))).Acyclic) ∧
      ∀ i : ℤ, exactFunctor _ _ (tensorRight (P.X i))) ↔
    CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ T)
        (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P) ∧
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology T)
        (R := ring Λ T) ((equivalence Λ T).functor.obj (P.X i))) := by
  have h := (InternalAbelianSheafModule.internal_section_tensor_comparison
    (Scheme.ProEt.topology T) (condensedRingObj Λ T)).2.choose_spec.choose_spec
  constructor
  · intro hP
    exact ⟨(h.2.2.2.2.2.2.2.2.2.2 P).mp hP.1,
      fun i ↦ (h.2.2.2.2.2.2.2.2.2.1 (P.X i)).mp (hP.2 i)⟩
  · intro hP
    exact ⟨(h.2.2.2.2.2.2.2.2.2.2 P).mpr hP.1,
      fun i ↦ (h.2.2.2.2.2.2.2.2.2.1 (P.X i)).mpr (hP.2 i)⟩

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)] in
private theorem internal_test_of_kflat (T : Scheme.{u})
    (P : CochainComplex (Modules Λ T) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    ∀ A : CochainComplex (Modules Λ T) ℤ, A.Acyclic →
      (CochainComplex.mapBifunctor A P (curriedTensor (Modules Λ T))).Acyclic := by
  intro A hA
  have h := ((HomotopyCategory.kFlat_iff_preserves_acyclic _).mp
    ((HomotopyCategory.kFlat_quotient_obj_iff P).mpr hP)
    ((HomotopyCategory.quotient _ _).obj A)
    ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic A).mpr hA)).2
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp h

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)] in
private theorem compute_isIso (T : Scheme.{u})
    (P : CochainComplex (Modules Λ T) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    IsIso (compute a T P) := by
  have hs : IsIso ((scalarCounit a T).app
      ((HomotopyCategory.quotient _ _).obj P)) := by
    unfold scalarCounit D
    exact (extension a T).isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
  unfold compute
  infer_instance

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)] in
private theorem total_scalar_isIso (T : Scheme.{u})
    (P Q : CochainComplex (Modules Λ T) ℤ) : IsIso (totalScalar a T P Q) := by
  let := CondensedRing.internalScalarMonoidal a T
  change IsIso (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans
    (.up ℤ) (extension a T)).app P).app Q)
  infer_instance

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
