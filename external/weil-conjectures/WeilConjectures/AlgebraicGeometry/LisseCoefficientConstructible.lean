/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
public import WeilConjectures.CategoryTheory.LocallyConstantFiniteTypeModules
import WeilConjectures.CategoryTheory.CoefficientFiniteLocalSystemsPullback

/-! # Lisse coefficient modules are constructible

Source: Stacks Project, etale-cohomology.tex, Tag 03RW(3).
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Constant-scalar restriction on an actual slice before changing its ring presentation. -/
private def fixedOver {D : Type w} [SmallCategory D]
    (T : GrothendieckTopology D) (R : Type w) [CommRing R] (U : D) :
    CategoryTheory.ConstantCompletion.Mod
        ((CategoryTheory.ConstantCompletion.constant T R).over U) ⥤
      Sheaf (T.over U) (ModuleCat.{w} R) where
  obj F :=
    { obj :=
        { obj := fun V ↦ ((PresheafOfModules.restrictScalars
            (Functor.whiskerLeft (Over.forget U).op
              (SheafOfModules.constantCoefficientUnit T R))).obj F.val).obj V
          map := fun f ↦ ((PresheafOfModules.restrictScalars
            (Functor.whiskerLeft (Over.forget U).op
              (SheafOfModules.constantCoefficientUnit T R))).obj F.val).map f
          map_id := fun _ ↦ by ext x; simp; rfl
          map_comp := fun _ _ ↦ by ext x; simp; rfl }
      property := Presheaf.isSheaf_of_isSheaf_comp _ _
        (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) F.isSheaf }
  map f := ObjectProperty.homMk
    { app := fun V ↦ (ModuleCat.restrictScalars
        ((SheafOfModules.constantCoefficientUnit T R).app
          (op V.unop.left)).hom).map (f.val.app V)
      naturality := fun {_ _} g ↦ by
        ext x
        exact PresheafOfModules.naturality_apply f.val g x }

/-- The sheafification unit identifies the two constant module constructions. -/
private def constantFixedIso {D : Type w} [SmallCategory D]
    (T : GrothendieckTopology D) (R : Type w) [CommRing R] (M : ModuleCat.{w} R) :
    (constantSheaf T (ModuleCat.{w} R)).obj M ≅
      (coefficientModelFixedScalars T R).obj
        ((SheafOfModules.constantCoefficientModule T R).obj M) := by
  let P := (SheafOfModules.strictPerfectConstantPresheaf (C := D) R).obj M
  let η := (PresheafOfModules.sheafificationAdjunction
    (SheafOfModules.constantCoefficientUnit T R)).unit.app P
  let F := (coefficientModelFixedScalars T R).obj
    ((SheafOfModules.constantCoefficientModule T R).obj M)
  let τ : (Functor.const Dᵒᵖ).obj M ⟶ F.obj :=
    { app := fun V ↦ η.app V
      naturality := fun {_ _} f ↦ by
        ext x
        exact PresheafOfModules.naturality_apply η f x }
  have hτ : T.W τ := by
    apply (T.W_iff_isLocallyBijective τ).mpr
    constructor
    · constructor
      intro V x y h
      exact Presheaf.equalizerSieve_mem T (toSheafify T P.presheaf) x y h
    · constructor
      intro V x
      exact Presheaf.imageSieve_mem T (toSheafify T P.presheaf) x
  have : IsIso ((presheafToSheaf T (ModuleCat.{w} R)).map τ) := (T.W_iff τ).mp hτ
  exact asIso ((presheafToSheaf T (ModuleCat.{w} R)).map τ) ≪≫
    asIso ((sheafificationAdjunction T (ModuleCat.{w} R)).counit.app F)

private theorem fixed_lisse {D : Type w} [SmallCategory D]
    (T : GrothendieckTopology D) (R : Type w) [CommRing R]
    (F : CategoryTheory.ConstantCompletion.Mod (CategoryTheory.ConstantCompletion.constant T R))
    (hF : SheafOfModules.IsLocallyConstantFiniteTypeModules T R F) :
    IsCoefficientModelLocallyConstantFinite T R ((coefficientModelFixedScalars T R).obj F) := by
  intro V
  obtain ⟨S, hS, hm⟩ := hF V
  refine ⟨S, hS, ?_⟩
  intro U f hf
  obtain ⟨M, hM, ⟨e⟩⟩ := hm U f hf
  refine ⟨M, hM, ⟨?_⟩⟩
  exact (fixedOver T R U).mapIso e ≪≫
    (T.overPullback (ModuleCat.{w} R) U).mapIso (constantFixedIso T R M).symm ≪≫
      (T.overPullbackConstantSheafIso (ModuleCat.{w} R) U).app M

/-- A finite locally constant module is constructible on the coefficient-sized etale site.
Source: Stacks Project, etale-cohomology.tex, Tag 03RW(3).
(auxiliary; not a blueprint node).

Proof: Restrict the scalar action along constant sections. This exact equivalence sends
constant module sheaves to constant module-valued sheaves and commutes with restriction
to slices. Thus the given covering sieves give finite locally constant fixed-scalar
models. On each affine open choose the one-stratum stratification with stratum the whole
open, domain the open itself and immersion the identity. Its stratum is constructible.
Etale inverse image preserves the local models and their finite generating modules, so
the restriction to this stratum satisfies the required fixed-scalar condition. The
whole-space stratum also works for an empty affine open, since it imposes no nonemptiness. -/
theorem lisseCoefficient_constructible
    (X : Scheme.{u}) (R : Type (max v (u + 1))) [CommRing R] [IsNoetherianRing R]
    (F : CategoryTheory.ConstantCompletion.Mod
      (CategoryTheory.ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X) R))
    (hF : SheafOfModules.IsLocallyConstantFiniteTypeModules
      (smallModelComparisonEtaleTopology.{u, v} X) R F) :
    IsCoefficientConstructibleEtaleModule.{u, v} X R F := by
  have hfixed := fixed_lisse (smallModelComparisonEtaleTopology.{u, v} X) R F hF
  intro U _
  let S : FiniteLocallyClosedStratification U.toScheme :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      iUnion_stratum_eq_univ := by
        ext x
        constructor
        · intro _; trivial
        · intro _; exact Set.mem_iUnion.mpr ⟨0, trivial⟩
      pairwise_disjoint_stratum := by intro i j h; exact (h (Subsingleton.elim i j)).elim
      domain := fun _ ↦ U.toScheme
      immersion := fun _ ↦ 𝟙 U.toScheme
      isImmersion := fun _ ↦ inferInstance
      range_immersion := fun _ ↦ by simp }
  refine ⟨S, fun _ ↦ Topology.IsConstructible.univ, ?_⟩
  intro i
  change IsCoefficientModelLocallyConstantFinite _ R
    ((coefficientEtaleFixedPullback.{u, v} (𝟙 U.toScheme ≫ U.ι) R).obj
      ((coefficientModelFixedScalars _ R).obj F))
  rw [Category.id_comp]
  let G := coefficientEtaleBaseChange.{u, v} U.ι
  let : PreservesFiniteLimits
      (AsSmall.down : smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale) :=
    inferInstanceAs (PreservesFiniteLimits
      (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).inverse)
  let : PreservesFiniteLimits
      (AsSmall.up : U.toScheme.Etale ⥤ smallModelComparisonEtaleSite.{u, v} U.toScheme) :=
    inferInstanceAs (PreservesFiniteLimits
      (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := U.toScheme.Etale)).functor)
  let : PreservesFiniteLimits (MorphismProperty.Over.pullback @Etale ⊤ U.ι) := inferInstance
  let : PreservesFiniteLimits G := comp_preservesFiniteLimits _ _
  exact coefficient_finite_local_systems_pullback
    (smallModelComparisonEtaleTopology.{u, v} X)
    (smallModelComparisonEtaleTopology.{u, v} U.toScheme) G R _ hfixed

end AlgebraicGeometry.Scheme
