/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtension
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import WeilConjectures.AlgebraicGeometry.LatticeSheafBasic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Continuous coefficients and slice restrictions for lisse lattices

The coefficient constructions used by the etale-local lattice theorem.
Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale

/-- The continuous coefficient sheaf, with the canonical extension of the p-adic norm.
Source: Bhatt--Scholze, Definition 6.8.1
(auxiliary; not a blueprint node). -/
noncomputable def lisseFieldSheaf (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  letI := spectralNorm.normedField ℚ_[l] E
  latticeCoefficientSheaf X E

/-- The integral coefficient sheaf, with the topology induced from the coefficient field.
Source: Bhatt--Scholze, Definition 6.8.1
(auxiliary; not a blueprint node). -/
noncomputable def lisseIntegerSheaf (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  letI := spectralNorm.normedField ℚ_[l] E
  latticeCoefficientSheaf X (Padic.coefficientExtensionIntegers l E)

/-- Postcomposition with the valuation-ring inclusion is the scalar extension map.
Source: Bhatt--Scholze, Proposition 6.8.4(6)
(auxiliary; not a blueprint node). -/
noncomputable def lisseIntegerToField (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    lisseIntegerSheaf l E X ⟶ lisseFieldSheaf l E X :=
  letI := spectralNorm.normedField ℚ_[l] E
  ⟨{ app := fun U ↦ CommRingCat.ofHom
       ((continuousMapRingPresheafMap X (Padic.coefficientExtensionIntegers l E).subtype
         continuous_subtype_val).app U).hom
     naturality := fun _ _ _ ↦ rfl }⟩

/-- Composition with an etale arrow embeds its small pro-etale site into the ambient site.
Source: Bhatt--Scholze, Proposition 6.8.4(6), slice-site restriction
(auxiliary; not a blueprint node). -/
noncomputable def lisseEtaleSiteInclusion {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] :
    Y.ProEt ⥤ X.ProEt where
  obj V := Scheme.ProEt.mk (V.hom ≫ f)
  map {V W} a := MorphismProperty.Over.homMk a.left
    ((Category.assoc a.left W.hom f).symm.trans
      (congrArg (fun b : V.left ⟶ Y ↦ b ≫ f) a.w))

/-- The slice coefficient identification is the identity on continuous functions.
Source: Bhatt--Scholze, Proposition 6.8.4(6)
(auxiliary; not a blueprint node). -/
noncomputable def lisseEtaleCoefficientIdentification (l : ℕ) [Fact l.Prime]
    (E : Type) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] :
    ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l E Y)).obj ⟶
    (lisseEtaleSiteInclusion f).op ⋙
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l E X)).obj :=
  { app := fun _ ↦ 𝟙 _
    naturality := fun _ _ _ ↦ rfl }

end AlgebraicGeometry.ProEtale
