/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteClopenTensor.ProEtaleFiniteClopenDerivedCalculus
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
import WeilConjectures.CategoryTheory.FiniteProductDerived.FiniteProductDerivedLocalization
import WeilConjectures.CategoryTheory.FiniteProductCoordinates.AdditiveFiniteProductCoordinates
import WeilConjectures.AlgebraicGeometry.ClopenMonoidalDescent.ProEtaleFiniteClopenNormalizedTensorModels
import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenArbitraryScalarNormalizedWitnesses
import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenScalarHomotopyRepresentative

/-!
# Tensor and unbounded derived calculus for a finite clopen partition

Source: Stacks Project, derived.tex, Tags 015F and 05RU; sites-modules.tex, Tag 0GMW;
sites-cohomology.tex, Tags 06YN, 06YS, 0G7D and 06YU; finite-component application
(blueprint: lem-pur-finite-product-derived-tensor-calculus).

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

-- The normalized comparison types carry several dependent localization instances.
/-- Ordinary and total tensor comparisons, flatness and K-flatness, and the normalized
symmetric monoidal derived restriction. Each `Braided` structure contains invertible
tensorators and unit comparison, their naturality, associativity, both unit diagrams,
and the symmetry diagram; the tensor products are the existing ones on both sides.
Source: Stacks 0GMW, 06YN, 06YS, 0G7D, 06YU and 0FPT
(blueprint: lem-pur-finite-product-derived-tensor-calculus).

Proof (node steps 4-9): the bilinear universal property constructs the restriction
tensorator. Its inverse is obtained by gluing the component bilinear maps. Both
composites fix pure tensors, so they are identities. Reassociation, exchange and unit
multiplication agree on generators. Restriction is left adjoint to zero insertion,
hence preserves the sums over p+q=n. Apply the tensorator on each summand: both
differentials send x tensor y to dx tensor y + (-1)^p x tensor dy. This gives the natural
chain isomorphism below. Test exact tensoring first by restriction and then by exact
zero insertion to obtain both directions of flatness. Test K-flatness against arbitrary
acyclic complexes, using restriction in one direction and insertion in the other.
Choose flat-term K-flat resolutions. Their restrictions are again such resolutions.
The K-flat localization equivalence and its unique natural-transformation extension
clause descend the chain tensorator and its inverse to all derived morphisms. The
representative square below fixes this descent to the native K-flat tensor models.
Associativity, units and Koszul symmetry descend because their diagrams agree on pure
triple tensors and degree (p,q) generators, with the same sign (-1)^(pq). Empty and zero
categories have unique maps and satisfy all these formulas. -/
theorem finite_clopen_tensor_calculus
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    (∀ F : Modules.{t, u} R,
      SheafOfModules.IsFlatOnSite (J := topology X) (R := R) F ↔
        ∀ i, SheafOfModules.IsFlatOnSite (J := topology (Y i))
          (R := (rings.{t, u} (j i)).obj R)
          ((restriction.{t, u} (j i) R).obj F)) ∧
    (∀ P : CochainComplex (Modules.{t, u} R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := topology X) (R := R) P ↔
        ∀ i, CochainComplex.IsKFlatIndependentCoefficients (J := topology (Y i))
          (R := (rings.{t, u} (j i)).obj R)
          (((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj P)) ∧
    ∀ i, ∃ (h : (restriction.{t, u} (j i) R).Braided)
      (c : coefficientTotalTensor.{u, t + 1, t} (topology X) R ⋙
          (restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ) ≅
        (((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).prod
          ((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ))) ⋙
            coefficientTotalTensor.{u, t + 1, t} (topology (Y i)) ((rings.{t, u} (j i)).obj R))
      (d : (derivedRestriction.{t, u} (j i) R).Braided),
      (∀ (F H : Modules.{t, u} R) (U : (Y i).ProEt) (x : F.val.obj
          (op ((MorphismProperty.Over.map ⊤
            (inferInstance : WeaklyEtale (j i))).obj U)))
        (y : H.val.obj (op ((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale (j i))).obj U))),
        ((tensorComparison (j i) R h F H).hom.val.app (op U))
          (pure R F H _ x y) =
        pure ((rings.{t, u} (j i)).obj R) ((restriction.{t, u} (j i) R).obj F)
          ((restriction.{t, u} (j i) R).obj H) (op U) x y) ∧
      (∀ (P Q : CochainComplex (Modules.{t, u} R) ℤ) (p q n : ℤ) (hpq : p + q = n)
        (U : (Y i).ProEt)
        (x : (P.X p).val.obj (op ((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale (j i))).obj U)))
        (y : (Q.X q).val.obj (op ((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale (j i))).obj U))),
        (((c.hom.app (P, Q)).f n).val.app (op U))
          (coefficientTensorGenerator.{u, t + 1, t} (topology X) R P Q p q n hpq _ x y) =
        coefficientTensorGenerator.{u, t + 1, t} (topology (Y i)) ((rings.{t, u} (j i)).obj R)
          (((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj P)
          (((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj Q)
          p q n hpq (op U) x y) ∧
      (∀ (P Q : CochainComplex (Modules.{t, u} R) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients (J := topology X) (R := R) P)
        (_hQ : CochainComplex.IsKFlatIndependentCoefficients (J := topology X) (R := R) Q)
        (hiP : CochainComplex.IsKFlatIndependentCoefficients (J := topology (Y i))
          (R := (rings.{t, u} (j i)).obj R)
          (((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj P))
        (_hiQ : CochainComplex.IsKFlatIndependentCoefficients (J := topology (Y i))
          (R := (rings.{t, u} (j i)).obj R)
          (((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj Q)),
        (derivedRestriction.{t, u} (j i) R).map
            (RingedDerivedNative.tensorIso.{t + 1, t, u} (topology X) R P Q
              (Or.inl hP)).hom ≫
          (derivedTensorComparison (j i) R d (DerivedCategory.Q.obj P)
            (DerivedCategory.Q.obj Q)).hom ≫
          ((restriction.{t, u} (j i) R).mapDerivedCategoryFactors.hom.app P ⊗ₘ
            (restriction.{t, u} (j i) R).mapDerivedCategoryFactors.hom.app Q) =
        (restriction.{t, u} (j i) R).mapDerivedCategoryFactors.hom.app
            ((coefficientTotalTensor.{u, t + 1, t} (topology X) R).obj (P, Q)) ≫
          DerivedCategory.Q.map (c.hom.app (P, Q)) ≫
          (RingedDerivedNative.tensorIso.{t + 1, t, u} (topology (Y i))
            ((rings.{t, u} (j i)).obj R)
            (((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj P)
            (((restriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj Q)
            (Or.inl hiP)).hom) := by
  have h := clopen_total_tensor_kflat_detection X I Y j hdisjoint hcover R
  exact ⟨h.1, h.2.1,
    ClopenMonoidalDescent.finite_clopen_normalized_tensor_models
      X I Y j hdisjoint hcover R⟩

open SheafOfModules.SuccessiveDerivedQuotient

/-- The already defined universal coefficient-extension presentations on this site.
Source: Stacks 06YY (blueprint: lem-pur-finite-product-derived-tensor-calculus). -/
abbrev Presentations (X : Scheme.{t}) :=
  ∀ {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S),
    Presentation.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (J := topology X) a

/-- Apply the existing normalized scalar compositor to the restricted ring maps.
The final equality transport is only functoriality of ring restriction.
Source: Stacks 0D6D (blueprint: lem-pur-finite-product-derived-tensor-calculus). -/
def scalarComposite {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (p : Presentations.{t, u} Y) (N : Normalization (J := topology Y) p)
    {R S T : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S) (b : S ⟶ T) :
    (p ((rings.{t, u} j).map a)).derived ⋙ (p ((rings.{t, u} j).map b)).derived ≅
      (p ((rings.{t, u} j).map (a ≫ b))).derived :=
  N.derived ((rings.{t, u} j).map a) ((rings.{t, u} j).map b) ≪≫
    eqToIso (congrArg (fun f ↦ (p f).derived) ((rings.{t, u} j).map_comp a b).symm)

-- The normalized comparison types carry several dependent localization instances.
end AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor
