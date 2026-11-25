/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom

import WeilConjectures.AlgebraicGeometry.OpenRestrictionDerivedMonoidal
import WeilConjectures.AlgebraicGeometry.OpenRestrictionEvaluationMateIsIso

/-! # Closed monoidal comparisons for open restriction

Source: Stacks Project, cohomology.tex, Tags 08DJ and 08DL.
(blueprint: lem-pc-open-restriction-closed-monoidal).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The standard localization is available on the open scheme independently of the
specified localization universe of the over-site.
Source: Stacks Project, Tag 05RU.
(blueprint: lem-pc-open-restriction-closed-monoidal). -/
local instance closedRestrictionStandardDerived (X : Scheme.{u}) (U : X.Opens) :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
  HasDerivedCategory.standard _

private theorem monoidal_restriction_mate_equation
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (H : Cᵒᵖ × C ⥤ C) (J : Dᵒᵖ × D ⥤ D) (R : C ⥤ D) [R.Monoidal]
    (e : ∀ A K N : C, (A ⟶ H.obj (op K, N)) ≃ (A ⊗ K ⟶ N))
    (eU : ∀ A K N : D, (A ⟶ J.obj (op K, N)) ≃ (A ⊗ K ⟶ N))
    (hx : ∀ A A' K N (a : A' ⟶ A) (f : A ⟶ H.obj (op K, N)),
      e A' K N (a ≫ f) = (a ⊗ₘ 𝟙 K) ≫ e A K N f)
    (hu : ∀ A A' K N (a : A' ⟶ A) (f : A ⟶ J.obj (op K, N)),
      eU A' K N (a ≫ f) = (a ⊗ₘ 𝟙 K) ≫ eU A K N f)
    (A K N : C) (ξ : A ⟶ H.obj (op K, N)) :
    eU (R.obj A) (R.obj K) (R.obj N)
      (R.map ξ ≫ (eU (R.obj (H.obj (op K, N))) (R.obj K) (R.obj N)).symm
        ((Functor.Monoidal.μIso R (H.obj (op K, N)) K).hom ≫
          R.map (e (H.obj (op K, N)) K N (𝟙 _)))) =
      (Functor.Monoidal.μIso R A K).hom ≫ R.map (e A K N ξ) := by
  rw [hu, Equiv.apply_symm_apply]
  have hn := Functor.LaxMonoidal.μ_natural R ξ (𝟙 K)
  rw [R.map_id] at hn
  change (R.map ξ ⊗ₘ 𝟙 (R.obj K)) ≫
    (Functor.Monoidal.μIso R (H.obj (op K, N)) K).hom =
    (Functor.Monoidal.μIso R A K).hom ≫ R.map (ξ ⊗ₘ 𝟙 K) at hn
  rw [← Category.assoc, hn, Category.assoc, ← R.map_comp]
  have h := hx (H.obj (op K, N)) A K N ξ (𝟙 _)
  simpa only [Category.comp_id] using congrArg
    (fun f ↦ (Functor.Monoidal.μIso R A K).hom ≫ R.map f) h.symm

private theorem closedRestriction_tensorHomEquiv_comp (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (A A' K N : schemeDerivedCategory X) (a : A' ⟶ A)
    (f : A ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.sheaf).obj (op K, N)) :
    schemeDerivedTensorHomEquiv X A' K N (a ≫ f) =
      (a ⊗ₘ 𝟙 K) ≫ schemeDerivedTensorHomEquiv X A K N f := by
  have hn := (Classical.choose_spec (exists_canonicalDerivedTensorHom X)).1
    A A' K K N N a (𝟙 K) (𝟙 N) f
  change schemeDerivedTensorHomEquiv X A' K N
    (a ≫ f ≫ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.sheaf).map (𝟙 (op K, N))) =
    (a ⊗ₘ 𝟙 K) ≫ schemeDerivedTensorHomEquiv X A K N f ≫ 𝟙 N at hn
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using hn

set_option linter.style.haveILetI false in
/-- Exact restriction carries compatible strong tensor and internal-Hom comparisons.

Source: Stacks Project, cohomology.tex, Tags 06YH, 08DJ and 08DL.
(blueprint: lem-pc-open-restriction-closed-monoidal).

Proof: choose K-flat representatives for both tensor inputs. Exact restriction
preserves their K-flatness, and its termwise sheaf-tensor comparison, summed over
all bidegrees of each total degree, identifies their total tensors. Descend this
natural comparison through localization and the over-site equivalence. Use
`Scheme.Modules.pullbackMonoidal` transported along the ordinary restriction
isomorphism for the termwise coherence, rather than choosing unrelated tensor
comparisons. Restrict
the structure sheaf in degree zero to obtain the unit comparison. Associativity
and both unit laws hold on pure tensors of the sheaf representatives, hence on
complexes and after localization; the inverse tensor comparisons define m.
Resolve each Hom target by the fixed functorial K-injective resolution. Its open
restriction is K-injective. The product Hom-complex comparison restricts each
local map and respects the signed differential. Localize and transport through
the over equivalence to obtain h. Choose h using these same restriction maps.
On each total-tensor summand, restricting an uncurried local map is the same as
uncurrying its restriction. This proves the displayed equation on chain maps.
By `CochainComplex.isKInjective_homComplex_of_isKFlat` (Stacks Tag 0A96),
Hom from a K-flat second argument into a K-injective is K-injective, so every
morphism into this Hom is represented modulo homotopy; uncurrying respects that
homotopy. Common K-flat resolutions and naturality give the equation for all
objects. The universal localization factorizations compare the independently
specified universes. All comparisons and laws apply also to zero complexes and
the empty open. No evaluation map is asserted to be invertible. -/
theorem exists_openRestriction_closedMonoidal (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    let E := (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory ⋙ E
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace) X.sheaf
    let HU := derivedInternalHom
      (Opens.grothendieckTopology U.toScheme.toRingedSpace) U.toScheme.sheaf
    ∃ m : R.Monoidal,
      letI := m
      ∃ h : ∀ K N : schemeDerivedCategory X,
        R.obj (H.obj (op K, N)) ≅ HU.obj (op (R.obj K), R.obj N),
        ∀ A K N (ξ : A ⟶ H.obj (op K, N)),
          schemeDerivedTensorHomEquiv U.toScheme (R.obj A) (R.obj K) (R.obj N)
            (R.map ξ ≫ (h K N).hom) =
          (Functor.Monoidal.μIso R A K).hom ≫
            R.map (schemeDerivedTensorHomEquiv X A K N ξ) := by
  classical
  -- Reuse the functors in the statement instead of elaborating their instances again.
  intro E R H HU
  let e := schemeDerivedTensorHomEquiv X
  let eU := schemeDerivedTensorHomEquiv U.toScheme
  -- Choose the local instance directly, avoiding a dependent elimination over this context.
  let m : R.Monoidal := Classical.choice (exists_openRestriction_derivedMonoidal X U)
  let c := fun K N ↦ (eU (R.obj (H.obj (op K, N))) (R.obj K) (R.obj N)).symm
    ((Functor.Monoidal.μIso R (H.obj (op K, N)) K).hom ≫
      R.map (e (H.obj (op K, N)) K N (𝟙 _)))
  have hc (K N : schemeDerivedCategory X) : IsIso (c K N) :=
    openRestriction_evaluationMate_isIso X U m K N
  let h := fun K N ↦ asIso (c K N)
  refine ⟨m, h, ?_⟩
  intro A K N ξ
  change eU (R.obj A) (R.obj K) (R.obj N) (R.map ξ ≫ c K N) =
    (Functor.Monoidal.μIso R A K).hom ≫ R.map (e A K N ξ)
  exact monoidal_restriction_mate_equation H HU R e eU
    (closedRestriction_tensorHomEquiv_comp X)
    (closedRestriction_tensorHomEquiv_comp U.toScheme) A K N ξ

end AlgebraicGeometry
