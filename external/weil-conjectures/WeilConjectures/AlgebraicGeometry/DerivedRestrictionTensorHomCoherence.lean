/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorAugmentation
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.AlgebraicGeometry.DerivedRestrictionTensorNaturality
import WeilConjectures.AlgebraicGeometry.DerivedRestrictionEvaluationMateIsIso

/-! # Coherent derived tensor and Hom restriction
Source: Stacks Project, Tags 08DJ, 08DL and 079U.
(blueprint: lem-sc-derived-restriction-tensor-hom-coherence).
-/

@[expose] public section

set_option autoImplicit false
universe uX wD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

private theorem restriction_mate_equation
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (H : Cᵒᵖ × C ⥤ C) (J : Dᵒᵖ × D ⥤ D) (R : C ⥤ D)
    (e : ∀ K L E : C, (K ⟶ H.obj (op L, E)) ≃ (K ⊗ L ⟶ E))
    (eU : ∀ K L E : D, (K ⟶ J.obj (op L, E)) ≃ (K ⊗ L ⟶ E))
    (hx : ∀ K K' L E (a : K' ⟶ K) (f : K ⟶ H.obj (op L, E)),
      e K' L E (a ≫ f) = (a ⊗ₘ 𝟙 L) ≫ e K L E f)
    (hu : ∀ K K' L E (a : K' ⟶ K) (f : K ⟶ J.obj (op L, E)),
      eU K' L E (a ≫ f) = (a ⊗ₘ 𝟙 L) ≫ eU K L E f)
    (t : ∀ K L : C, R.obj (K ⊗ L) ≅ R.obj K ⊗ R.obj L)
    (ht : ∀ K K' L L' (a : K ⟶ K') (b : L ⟶ L'),
      R.map (a ⊗ₘ b) ≫ (t K' L').hom = (t K L).hom ≫ (R.map a ⊗ₘ R.map b))
    (K L E : C) (ξ : K ⟶ H.obj (op L, E)) :
    (t K L).hom ≫ eU (R.obj K) (R.obj L) (R.obj E)
      (R.map ξ ≫ (eU (R.obj (H.obj (op L, E))) (R.obj L) (R.obj E)).symm
        ((t (H.obj (op L, E)) L).inv ≫ R.map (e (H.obj (op L, E)) L E (𝟙 _)))) =
      R.map (e K L E ξ) := by
  rw [hu, Equiv.apply_symm_apply]
  have hn := ht K (H.obj (op L, E)) L L ξ (𝟙 L)
  rw [R.map_id] at hn
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← R.map_comp]
  have h := hx (H.obj (op L, E)) K L E ξ (𝟙 _)
  simpa only [Category.comp_id] using congrArg R.map h.symm

/-- Exact open restriction has simultaneous tensor and internal-Hom comparisons
compatible with the canonical tensor-Hom bijections.
Source: Stacks Project, Tags 079U, 08DL and 08DJ.
(blueprint: lem-sc-derived-restriction-tensor-hom-coherence).

Proof: compute the tensor comparison on K-flat representatives of its arguments.
Restrict their total tensor termwise and use preservation of K-flatness. The
localization factorization identifies this with restriction of derived tensor.
Naturality on complexes descends through quasi-isomorphisms to arbitrary derived
maps, giving the displayed tensor naturality square. For an open immersion,
ordinary restriction is exact, so it computes derived pullback in Tag 079U.
Common K-flat resolutions identify the comparisons for different representatives;
their inverses give the same square for roofs. Compute internal Hom with
K-injective representatives of the second argument; restriction preserves these
and identifies the Hom complexes termwise. Transport through the over-site
module equivalence, obtaining the Hom comparison. Choose these comparisons from
the same termwise restriction maps. On each total-tensor summand, restricting
uncurrying evaluates the same local linear map as uncurrying after restriction.
Thus their evaluation square commutes on representatives. With a K-flat model
of the second tensor factor, its Hom into a K-injective is K-injective, so every
map from an arbitrary first factor is represented modulo homotopy. Uncurrying
preserves homotopies. The representative characterization and uniqueness of the
canonical tensor-Hom family therefore give the evaluation equation for every
derived map. The construction includes zero objects and the empty open. -/
theorem exists_derivedRestriction_tensorHom_coherence
    (X : Scheme.{uX}) (U : X.Opens)
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))] :
    let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf
    let HU := derivedInternalHom (Opens.grothendieckTopology U.toScheme.toRingedSpace)
      U.toScheme.toRingedSpace.sheaf
    ∃ (t : ∀ K L : schemeDerivedCategory X, R.obj (K ⊗ L) ≅ R.obj K ⊗ R.obj L)
      (h : ∀ L E, R.obj (H.obj (op L, E)) ≅ HU.obj (op (R.obj L), R.obj E)),
      (∀ K K' L L' (a : K ⟶ K') (b : L ⟶ L'),
        R.map (a ⊗ₘ b) ≫ (t K' L').hom =
          (t K L).hom ≫ (R.map a ⊗ₘ R.map b)) ∧
      (∀ K L E (ξ : K ⟶ H.obj (op L, E)),
        (t K L).hom ≫ schemeDerivedTensorHomEquiv U.toScheme
          (R.obj K) (R.obj L) (R.obj E) (R.map ξ ≫ (h L E).hom) =
        R.map (schemeDerivedTensorHomEquiv X K L E ξ)) := by
  classical
  obtain ⟨t, ht⟩ := exists_derivedRestriction_tensor_natural X U
  intro R H HU
  let e := schemeDerivedTensorHomEquiv X
  let eU := schemeDerivedTensorHomEquiv U.toScheme
  have he : IsCanonicalDerivedTensorHom X e :=
    Classical.choose_spec (exists_canonicalDerivedTensorHom X)
  have heU : IsCanonicalDerivedTensorHom U.toScheme eU :=
    Classical.choose_spec (exists_canonicalDerivedTensorHom U.toScheme)
  let m := fun L E ↦ (eU (R.obj (H.obj (op L, E))) (R.obj L) (R.obj E)).symm
    ((t (H.obj (op L, E)) L).inv ≫ R.map (e (H.obj (op L, E)) L E (𝟙 _)))
  have hm (L E : schemeDerivedCategory X) : IsIso (m L E) :=
    derivedRestriction_evaluationMate_isIso X U t ht L E
  let h := fun L E ↦ asIso (m L E)
  refine ⟨t, h, ht, ?_⟩
  intro K L E ξ
  change (t K L).hom ≫ eU (R.obj K) (R.obj L) (R.obj E)
    (R.map ξ ≫ m L E) = R.map (e K L E ξ)
  apply restriction_mate_equation H _ R e eU ?_ ?_ t ht K L E ξ
  · intro A A' B M a f
    have hn := he.1 A A' B B M M a (𝟙 B) (𝟙 M) f
    change e A' B M (a ≫ f ≫ H.map (𝟙 (op B, M))) = _ at hn
    simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using hn
  · intro A A' B M a f
    have hn := heU.1 A A' B B M M a (𝟙 B) (𝟙 M) f
    change eU A' B M (a ≫ f ≫
      (derivedInternalHom (Opens.grothendieckTopology U.toScheme.toRingedSpace)
        U.toScheme.toRingedSpace.sheaf).map (𝟙 (op B, M))) = _ at hn
    simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using hn

end AlgebraicGeometry.Scheme
