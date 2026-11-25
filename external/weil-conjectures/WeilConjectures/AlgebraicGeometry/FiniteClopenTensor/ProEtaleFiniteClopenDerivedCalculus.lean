/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenRingedModuleGluing
public import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
public import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
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
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.AlgebraicGeometry.ClopenMonoidalDescent.ProEtaleClopenMonoidalNormalization
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenDerivedScalarData
import WeilConjectures.CategoryTheory.FiniteProductDerived.FiniteProductDerivedLocalization
import WeilConjectures.CategoryTheory.FiniteProductCoordinates.AdditiveFiniteProductCoordinates
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.CategoryTheory.PUnit

/-!
# Unbounded derived calculus for a finite clopen partition

Source: Stacks Project, derived.tex, Tags 015F and 05RU; sites-modules.tex, Tag 0GMW;
sites-cohomology.tex, Tags 06YN, 06YS, 0G7D and 06YU; finite-component application
(blueprint: lem-pur-finite-clopen-derived-calculus).

All restrictions are the sectionwise functors of the module-gluing node. Tensor products
and their constraints are the existing sheafification and K-flat localization constructions.
-/

@[expose] public noncomputable section

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenScalar.derived
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_hasSheafify
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

-- The canonical public wrappers below provide these instances to consumers.
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.hasDerived
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.monoidal
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.symmetric
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.restrictionLimits
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.restrictionColimits

set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe t u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory
  DerivedCategory.Q Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  HasDerivedCategory.standard DerivedCategory.Qh DerivedCategory.quotientCompQhIso
  Functor.mapDerivedCategoryFactorsh Functor.mapHomotopyCategoryFactors
  RingedDerivedNative.monoidal RingedDerivedNative.symmetric
  coefficientTotalTensor
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.ModelNormalization

namespace AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor

/-- The recorded module category, with a coefficient universe containing the small site.
Source: Stacks 03D7 (blueprint: lem-pur-finite-clopen-derived-calculus). -/
abbrev Modules {X : Scheme.{t}} (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :=
  clopenTensorModules.{t, u} R

/-- Restrict commutative rings by the same site composition as `clopenRingRestriction`.
Source: Stacks 04TR (blueprint: lem-pur-finite-clopen-derived-calculus). -/
abbrev rings {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j] :=
  clopenTensorRings.{t, u} j

/-- The module restriction of the recorded gluing theorem, without changing its data.
Source: Stacks 04TR (blueprint: lem-pur-finite-clopen-derived-calculus). -/
abbrev restriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    Modules.{t, u} R ⥤ Modules.{t, u} ((rings.{t, u} j).obj R) :=
  clopenTensorRestriction.{t, u} j R

/-- Exactness of component restriction, including the unbounded case.
Source: Stacks 015F and 04TR (blueprint: lem-pur-finite-clopen-derived-calculus).
Proof: identify the component site with the slice at the open immersion. Restriction
preserves kernels and sheafified cokernels by the exact module-gluing equivalence;
equivalently sheaf exactness is local on this slice. No exactness of sections is used. -/
theorem restriction_exact {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    PreservesFiniteLimits (restriction.{t, u} j R) ∧
      PreservesFiniteColimits (restriction.{t, u} j R) := by
  exact ⟨ClopenScalar.resLimits j R, ClopenScalar.resColimits j R⟩

/-- Exact restriction preserves finite limits.
Source: Stacks 015F (blueprint: lem-pur-finite-clopen-derived-calculus). -/
instance restrictionLimits {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    PreservesFiniteLimits (restriction.{t, u} j R) := (restriction_exact j R).1

/-- Exact restriction preserves finite colimits.
Source: Stacks 015F (blueprint: lem-pur-finite-clopen-derived-calculus). -/
instance restrictionColimits {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    PreservesFiniteColimits (restriction.{t, u} j R) := (restriction_exact j R).2

/-- Additivity is the already recorded sectionwise restriction additivity.
Source: Stacks 04TR (blueprint: lem-pur-finite-clopen-derived-calculus). -/
instance restrictionAdditive {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    (restriction.{t, u} j R).Additive :=
  clopenModuleRestriction_additive j _

/-- Standard localization in the fixed module universe, with no boundedness restriction.
Source: Stacks 05RU (blueprint: lem-pur-finite-clopen-derived-calculus). -/
@[instance_reducible]
instance hasDerived {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    HasDerivedCategory.{max (u + 1) (t + 2)} (Modules.{t, u} R) :=
  ClopenMonoidalDescent.hasDerived.{t, u} R

/-- Degreewise restriction followed by localization at quasi-isomorphisms.
Source: Stacks 015F, 05RU (blueprint: lem-pur-finite-clopen-derived-calculus). -/
abbrev derivedRestriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :=
  ClopenMonoidalDescent.derivedRestriction.{t, u} j R

/-- The existing native K-flat derived tensor, with its prescribed constraints.
Source: Stacks 0FPT (blueprint: lem-pur-finite-clopen-derived-calculus). -/
instance derivedMonoidal {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    MonoidalCategory (DerivedCategory (Modules.{t, u} R)) :=
  ClopenMonoidalDescent.monoidal.{t, u} R

/-- Its existing Koszul symmetry.
Source: Stacks 0FPT (blueprint: lem-pur-finite-clopen-derived-calculus). -/
instance derivedSymmetric {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    SymmetricCategory (DerivedCategory (Modules.{t, u} R)) :=
  ClopenMonoidalDescent.symmetric.{t, u} R

/-- The pure tensor in the existing localization tensor of module sheaves.
Source: Stacks 0GMW (blueprint: lem-pur-finite-clopen-derived-calculus). -/
def pure {X : Scheme.{t}} (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (F H : Modules.{t, u} R) (U : X.ProEtᵒᵖ) (x : F.val.obj U) (y : H.val.obj U) :
    (F ⊗ H).val.obj U :=
  clopenTensorPure.{t, u} R F H U x y

/-- The inverse tensorator of a braided restriction functor.
Source: Stacks 0GMW (blueprint: lem-pur-finite-clopen-derived-calculus). -/
def tensorComparison {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (restriction.{t, u} j R).Braided) (F H : Modules.{t, u} R) :
    (restriction.{t, u} j R).obj (F ⊗ H) ≅
      (restriction.{t, u} j R).obj F ⊗ (restriction.{t, u} j R).obj H :=
  clopenTensorComparison.{t, u} j R h F H

/-- The inverse tensorator on the prescribed native derived tensors.
Source: Stacks 06YU, 0FPT (blueprint: lem-pur-finite-clopen-derived-calculus). -/
def derivedTensorComparison {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (derivedRestriction.{t, u} j R).Braided)
    (K L : DerivedCategory (Modules.{t, u} R)) :
    (derivedRestriction.{t, u} j R).obj (K ⊗ L) ≅
      (derivedRestriction.{t, u} j R).obj K ⊗ (derivedRestriction.{t, u} j R).obj L :=
  (ClopenMonoidalDescent.braidedComparison.{t, u} j R h).app (K, L)

private local instance piPreadditive {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, Preadditive (D i)] : Preadditive (∀ i, D i) :=
  CategoryTheory.FiniteProductCoordinates.piPreadditive D

private theorem equivalenceCoordinateDecomposition
    {C : Type*} [Category C] [Preadditive C] {J : Type*} [Finite J]
    (D : J → Type*) [∀ i, Category (D i)] [∀ i, Preadditive (D i)]
    [∀ i, HasZeroObject (D i)] (E : C ≌ ∀ i, D i) [E.inverse.Additive] :
    ∃ e : ∀ i, D i ⥤ C,
      (∀ i, Nonempty (e i ⋙ (E.functor ⋙ Pi.eval D i) ≅ 𝟭 _)) ∧
      (∀ i k, i ≠ k → ∀ M, IsZero ((e k ⋙ (E.functor ⋙ Pi.eval D i)).obj M)) ∧
      (∃ s : ∀ i, D i ⥤ ∀ k, D k,
        ∀ i, e i = s i ⋙ E.inverse ∧
          Nonempty (s i ⋙ Pi.eval D i ≅ 𝟭 _) ∧
          (∀ k, k ≠ i → ∀ M, IsZero ((s i).obj M k))) ∧
      (∃ b : Bicone (fun i ↦ (E.functor ⋙ Pi.eval D i) ⋙ e i),
        b.pt = 𝟭 _ ∧ Nonempty b.IsBilimit) ∧
      (∃ b : Bicone (fun i ↦ Pi.eval D i ⋙ e i),
        b.pt = E.inverse ∧ Nonempty b.IsBilimit) := by
  exact CategoryTheory.FiniteProductCoordinates.equivalenceCoordinateDecomposition D E

section DerivedPi

universe a b c d z
variable {A : Type a} [Category.{b} A] [Abelian A] [HasDerivedCategory A]
  {I : Type z} [Finite I] {B : I → Type c} [∀ i, Category.{d} (B i)]
  [∀ i, Abelian (B i)] [∀ i, HasDerivedCategory (B i)]
  (r : ∀ i, A ⥤ B i) [∀ i, (r i).Additive]
  [∀ i, PreservesFiniteLimits (r i)] [∀ i, PreservesFiniteColimits (r i)]
  (G : (∀ i, B i) ⥤ A)
  (hzero : ∀ (M N : ∀ i, B i), G.map (fun i ↦ (0 : M i ⟶ N i)) = 0)
  (η : 𝟭 A ≅ Functor.pi' r ⋙ G) (ε : G ⋙ Functor.pi' r ≅ 𝟭 _)

end DerivedPi

end AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor
