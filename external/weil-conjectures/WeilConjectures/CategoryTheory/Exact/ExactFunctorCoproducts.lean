/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import all WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Coproduct preservation by exact derived functors

Source: Stacks 07D9 and 070I.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v u' v' w w' s
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Localization preserves termwise coproducts in the presence of K-injective resolutions.
Source: Stacks 07D9 and 070I (blueprint: lem-pur-exact-derived-coproducts).
Proof: compute maps into a K-injective resolution of the target. Both chain maps and
homotopies out of a termwise coproduct are families of maps and homotopies. Thus the
localized termwise coproduct cofan has the coproduct universal property. -/
theorem derived_Q_preservesCoproducts
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [Abelian.HasKInjectiveResolutions A] [HasCoproducts.{s} A] (I : Type s) :
    PreservesColimitsOfShape (Discrete I) (DerivedCategory.Q (C := A)) := by
  let Q := DerivedCategory.Q (C := A)
  have (K : I → CochainComplex A ℤ) : PreservesColimit (Discrete.functor K) Q := by
    apply preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct K)
    have h := (derivedCoproductCofan I (fun i ↦ Q.obj (K i)) K
      (fun _ ↦ Iso.refl _)).some
    apply (IsColimit.equivOfNatIsoOfIso
      (Discrete.compNatIsoDiscrete K Q).symm _ _ ?_) h
    refine Cocone.ext (Iso.refl _) ?_
    intro i
    simp [Q]
  exact preservesColimitsOfShape_of_discrete Q

/-- An exact functor preserving coproducts also preserves them on unbounded derived categories.
Source: Stacks 07D9 and 015F (blueprint: lem-pur-exact-derived-coproducts).
Proof: represent every derived summand by a complex. The source coproduct is the
localization of the termwise coproduct. Exactness identifies its image with the
localization of the image complex; ordinary coproduct preservation makes that complex
the coproduct of the image complexes. The target localization preserves this coproduct
by the K-injective universal-property argument. Transport along the representative
isomorphisms and the exact-functor factorization. -/
theorem Functor.mapDerivedCategory_preservesCoproducts
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions D]
    [HasCoproducts.{s} A] [HasCoproducts.{s} D]
    (F : A ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (I : Type s) [PreservesColimitsOfShape (Discrete I) F] :
    PreservesColimitsOfShape (Discrete I) F.mapDerivedCategory := by
  let Q := DerivedCategory.Q (C := A)
  let Q' := DerivedCategory.Q (C := D)
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let FD := F.mapDerivedCategory
  let ε := F.mapDerivedCategoryFactors
  have := derived_Q_preservesCoproducts (A := A) I
  have := derived_Q_preservesCoproducts (A := D) I
  have hK (K : I → CochainComplex A ℤ) :
      PreservesColimit (Discrete.functor (fun i ↦ Q.obj (K i))) FD := by
    let c := Cofan.mk (∐ K) (Sigma.ι K)
    have hc : IsColimit c := coproductIsCoproduct K
    have hs := isColimitOfPreserves Q hc
    have hp : PreservesColimit (Discrete.functor K ⋙ Q) FD := by
      apply preservesColimit_of_preserves_colimit_cocone hs
      let d := Q'.mapCocone (Fc.mapCocone c)
      have hd : IsColimit d := isColimitOfPreserves Q' (isColimitOfPreserves Fc hc)
      let α : (Discrete.functor K ⋙ Q) ⋙ FD ≅
          (Discrete.functor K ⋙ Fc) ⋙ Q' :=
        Discrete.natIso (fun i ↦ ε.app (K i.as))
      apply (IsColimit.equivOfNatIsoOfIso α _ d ?_).symm hd
      refine Cocone.ext (ε.app (∐ K)) ?_
      intro i
      change (ε.inv.app (K i.as) ≫ FD.map (Q.map (Sigma.ι K i.as))) ≫
        ε.hom.app (∐ K) = Q'.map (Fc.map (Sigma.ι K i.as))
      rw [Category.assoc]
      erw [ε.hom.naturality]
      simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
      rfl
    exact preservesColimit_of_iso_diagram FD (Discrete.compNatIsoDiscrete K Q)
  have (E : I → DerivedCategory A) : PreservesColimit (Discrete.functor E) FD := by
    let K (i : I) := Q.objPreimage (E i)
    have := hK K
    exact preservesColimit_of_iso_diagram FD
      (Discrete.natIso
        (F := Discrete.functor (fun i ↦ Q.obj (K i)))
        (G := Discrete.functor E) (fun i ↦ Q.objObjPreimageIso (E i.as)))
  exact preservesColimitsOfShape_of_discrete FD

end CategoryTheory
