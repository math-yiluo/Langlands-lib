/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.BaseTensorDerivedComparisonModel

/-! # Naturality of localized base-derived tensor comparison

Source: Stacks Project, More on Algebra, Tag 06Y6; perfect.tex, equation-bc (Tag 0DJ7).
(blueprint: lem-pc-base-derived-tensor-localized-naturality).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace ModuleCat

variable {A D : Type u} [CommRing A] [CommRing D]
  [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} D)]

/-- The homology identification supplied by an invertible scalar-extension counit.
Source: Stacks Project, More on Algebra, Tag 06Y6.
(blueprint: lem-pc-base-derived-tensor-localized-naturality). -/
def scalarExtensionHomologyIso (ρ : A →+* D)
    (L : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} D))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (extendScalars.{u, u, u} ρ).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) (i : ℤ) :
    (DerivedCategory.homologyFunctor _ i).obj (L.obj (DerivedCategory.Q.obj P)) ≅
      (((extendScalars.{u, u, u} ρ).mapHomologicalComplex (.up ℤ)).obj P).homology i :=
  letI := hP
  (DerivedCategory.homologyFunctor _ i).mapIso
    (L.mapIso ((DerivedCategory.quotientCompQhIso _).symm.app P) ≪≫
      asIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≪≫
      DerivedCategory.Qh.mapIso
        (((extendScalars.{u, u, u} ρ).mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
      (DerivedCategory.quotientCompQhIso _).app _) ≪≫
    (DerivedCategory.homologyFunctorFactors _ i).app _

variable (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} D)]

/-- Localization factors identify the input to a base tensor model with derived
restriction of an A-complex. Source: Stacks Project, Tag 06Y6.
(blueprint: lem-pc-base-derived-tensor-localized-naturality). -/
def baseTensorInputIso (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj
      (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj P)) ≅
      (restrictScalars.{u} (algebraMap R A)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj P) :=
  (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    (restrictScalars.{u} (algebraMap R A)).mapDerivedCategoryFactors.symm.app P

/-- Transport on model cohomology along a derived A-linear isomorphism, before
lifting the transport from B to the tensor algebra. Source: Stacks Project, Tag 06Y6.
(blueprint: lem-pc-base-derived-tensor-localized-naturality). -/
def baseTensorSourceIso
    {P Q : CochainComplex (ModuleCat.{u} A) ℤ}
    (M : BaseDerivedTensorCohomologyModel R A B P D)
    (N : BaseDerivedTensorCohomologyModel R A B Q D)
    (a : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) (i : ℤ) :
    (restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).obj (M.cohomology i) ≅
      (restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).obj (N.cohomology i) :=
  letI := M.universal
  letI := N.universal
  let b := baseTensorInputIso R A P ≪≫
    (restrictScalars.{u} (algebraMap R A)).mapDerivedCategory.mapIso a ≪≫
    (baseTensorInputIso R A Q).symm
  M.cohomologyIso i ≪≫ (DerivedCategory.homologyFunctor _ i).mapIso
    (M.derived.mapIso b ≪≫
      (Functor.leftDerivedNatIso M.derived N.derived M.counit N.counit
        (HomotopyCategory.quasiIso _ (.up ℤ)) (Iso.refl _)).app _) ≪≫
    (N.cohomologyIso i).symm

/-- The localized model comparison is natural into derived A-to-D scalar extension.
This is an algebraic statement about arbitrary counit-compatible models, with no
schemes or tensor-stalk identifications.

Proof: the scalar-extension and tensor-associativity maps on complexes induce a
transformation from base-derived tensor (after exact restriction from A to R) to
derived extension from A to D, restricted to B. Derive the transformation using
K-flat resolutions and localization; its naturality holds for every derived
A-linear morphism. The universal property identifies the base-derived functors
of M and N by their unique counit-compatible isomorphism. Apply degree-i homology.
The equations comparison_eq for M and N identify the cohomology maps induced by
these counits with their comparison maps. The generator equations for ordinaryIso
and ordinaryToLocalized fix the tensor-associativity and coefficient-extension
maps and ensure their compatibility with the derived transformation. The equations
localized_eq identify localizedComparison with the adjoint transpose of this map.
Naturality of extension/restriction adjunction therefore gives the asserted
D-linear square. The hypothesis on e identifies its restriction with the model
transport; faithful restriction to B then gives the same tensor-algebra morphism.
The invertible scalar-extension counits identify the two target objects with
ordinary scalar-extension homology, through scalarExtensionHomologyIso. No
invertibility of localizedComparison, R-flatness, or flatness of D is used.
The identity morphism, zero complexes and zero coefficient rings follow the same
adjunction calculation.
Source: Stacks Project, More on Algebra, Tag 06Y6, lemma-derived-base-change;
perfect.tex, equation-bc (Tag 0DJ7).
(blueprint: lem-pc-base-derived-tensor-localized-naturality). -/
theorem baseDerivedTensor_localized_naturality
    {P Q : CochainComplex (ModuleCat.{u} A) ℤ}
    (M : BaseDerivedTensorCohomologyModel R A B P D)
    (N : BaseDerivedTensorCohomologyModel R A B Q D)
    (L : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} D))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (extendScalars.{u, u, u} ((algebraMap (A ⊗[R] B) D).comp
        (algebraMap A (A ⊗[R] B)))).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hL : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ)))
    (hcP : IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (hcQ : IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)))
    (a : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) (i : ℤ)
    (e : M.cohomology i ≅ N.cohomology i)
    (he : (restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).map e.hom =
      (baseTensorSourceIso R A B D M N a i).hom) :
    M.localizedComparison i ≫ (scalarExtensionHomologyIso _ L ε P hcP i).inv ≫
        (DerivedCategory.homologyFunctor _ i).map (L.map a.hom) =
      (extendScalars.{u, u, u} (algebraMap (A ⊗[R] B) D)).map e.hom ≫
        N.localizedComparison i ≫ (scalarExtensionHomologyIso _ L ε Q hcQ i).inv := by
  let _ := M.universal
  let _ := N.universal
  let ζ := Functor.leftDerivedNatIso M.derived N.derived M.counit N.counit
    (HomotopyCategory.quasiIso _ (.up ℤ)) (Iso.refl _)
  obtain ⟨τ, hτ⟩ := exists_baseTensorDerivedComparison R A B D
    N.derived N.counit N.universal L ε hL i
  let sP := scalarExtensionHomologyIso _ L ε P hcP i
  let sQ := scalarExtensionHomologyIso _ L ε Q hcQ i
  have hsP : sP.hom = scalarExtensionHomologyMap _ L ε P i := by
    simp [sP, scalarExtensionHomologyIso, scalarExtensionHomologyMap]
  have hsQ : sQ.hom = scalarExtensionHomologyMap _ L ε Q i := by
    simp [sQ, scalarExtensionHomologyIso, scalarExtensionHomologyMap]
  have hζ : Functor.whiskerLeft DerivedCategory.Qh ζ.hom ≫ N.counit = M.counit := by
    simp [ζ]
  have hP := baseTensorDerivedComparison_model R A B D N.derived N.counit L ε i
    τ hτ P M ζ hζ sP hsP
  have hQ := baseTensorDerivedComparison_model R A B D N.derived N.counit L ε i
    τ hτ Q N (Iso.refl _) (by simp) sQ hsQ
  let adj := extendRestrictScalarsAdj.{u, u, u} (algebraMap (A ⊗[R] B) D)
  apply (adj.homEquiv _ _).injective
  change adj.homEquiv _ _ ((M.localizedComparison i ≫ sP.inv) ≫
    (DerivedCategory.homologyFunctor _ i).map (L.map a.hom)) =
    adj.homEquiv _ _ ((extendScalars _).map e.hom ≫
      (N.localizedComparison i ≫ sQ.inv))
  rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_left]
  apply (restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).map_injective
  simp only [Functor.map_comp]
  rw [he]
  rw [show adj.homEquiv _ _ (M.localizedComparison i ≫ sP.inv) =
    adj.unit.app _ ≫ (restrictScalars _).map (M.localizedComparison i ≫ sP.inv)
    from rfl]
  rw [show adj.homEquiv _ _ (N.localizedComparison i ≫ sQ.inv) =
    adj.unit.app _ ≫ (restrictScalars _).map (N.localizedComparison i ≫ sQ.inv)
    from rfl]
  rw [hP, hQ]
  simp only [Category.assoc]
  have ht := τ.naturality a.hom
  simp only [Functor.comp_map] at ht
  rw [← ht]
  dsimp only [baseTensorSourceIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.refl_hom, Iso.app_hom,
    NatTrans.id_app]
  let cP := baseTensorInputIso R A P
  let cQ := baseTensorInputIso R A Q
  let f := (restrictScalars.{u} (algebraMap R A)).mapDerivedCategory.map a.hom
  have hg : M.derived.map cP.hom ≫ ζ.hom.app _ ≫ N.derived.map f =
      M.derived.map (cP.hom ≫ f ≫ cQ.inv) ≫ ζ.hom.app _ ≫
        N.derived.map cQ.hom := by
    rw [← ζ.hom.naturality f, ← ζ.hom.naturality cQ.hom]
    simp [← Functor.map_comp]
  change (M.cohomologyIso i).hom ≫
    (DerivedCategory.homologyFunctor _ i).map (M.derived.map cP.hom ≫ ζ.hom.app _) ≫
      (DerivedCategory.homologyFunctor _ i).map (N.derived.map f) ≫ τ.app _ =
    (M.cohomologyIso i).hom ≫
      (DerivedCategory.homologyFunctor _ i).map
        (M.derived.map (cP.hom ≫ f ≫ cQ.inv) ≫ ζ.hom.app _) ≫
      (DerivedCategory.homologyFunctor _ i).map (N.derived.map cQ.hom ≫ 𝟙 _) ≫ τ.app _
  simpa only [Category.comp_id, Functor.map_comp, Category.assoc] using
    congrArg (fun k ↦ (M.cohomologyIso i).hom ≫
      (DerivedCategory.homologyFunctor _ i).map k ≫ τ.app (DerivedCategory.Q.obj Q)) hg

end ModuleCat
