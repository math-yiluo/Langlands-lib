/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement

/-! # Effacing constructible finite module coefficients on a closed subscheme

Source: Stacks Project, Tag 09ZE, constructible finite-pushforward step of the proof.
(blueprint: lem-weil-pbc-constructible-module-closed-effacement)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The constructible finite-module part of affine closed-subscheme effacement.

Source: Stacks Project, Tag 09ZE, proof, constructible case; Tags 09Z7 and 09ZD.
(blueprint: lem-weil-pbc-constructible-module-closed-effacement)

Proof:
1. Embed C into a finite sum of finite pushforwards of constant finite modules M_j
   along finite finitely presented maps f_j:Y_j to X, using Tag 09Z7. Each Y_j is
   affine. Pullback is exact, and forgetting coefficients preserves monomorphisms.
2. Take the image of x under this embedding and its projections to the summands.
   Finite exchange and the finite-pushforward cohomology edge isomorphism identify
   each component with a class of the constant underlying abelian sheaf M_j on
   Y_j times_X Z. Forgetting modules commutes with constants and inverse image.
3. Apply Tag 09ZD to obtain finite surjective finitely presented covers
   π_j:Y'_j to Y_j killing those classes. Each adjunction unit from constant M_j
   to π_j*π_j^*M_j is monic by surjectivity. Finite pushforward preserves monos.
   The pullback of the constant module is canonically constant on Y'_j.
4. Push these units forward by f_j and take their finite sum. Compose with the
   embedding of C to obtain a monomorphism into the resulting module sheaf D.
   Base-change/unit/edge compatibility says that every projected image of x is
   zero. Cohomology respects finite biproducts, so the full image is zero.
   No constructibility is asserted for D and no comparison hypothesis is used.
   Empty sums and zero coefficient rings give zero sheaves. The restriction is
   to a closed subscheme, so the killing lemma applies; q>0 is essential.
-/
theorem exists_constructible_module_mono_closed_cohomology_eq_zero
    {X Z : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (C : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hC : Scheme.IsConstructibleEtaleModuleSheaf C) (q : ℕ) (hq : 0 < q)
    (x : Sheaf.H (((i)^*[AddCommGrpCat.{u + 1}]).obj
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj C)) q) :
    ∃ (D : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (b : C ⟶ D),
      Mono b ∧ Sheaf.H.map (((i)^*[AddCommGrpCat.{u + 1}]).map
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map b))
          q x = 0 := by
  classical
  let U := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let V := (i)^*[AddCommGrpCat.{u + 1}]
  let : U.Additive := { map_add := by intro F G α β; ext W; rfl }
  obtain ⟨n, Y, f, hf, hfp, M, hM, φ, hφ⟩ :=
    finite_pushforward_embedding_of_isConstructibleEtaleModuleSheaf Λ C hC
  let A (j : Fin n) := (lowerStar (ModuleCat.{u + 1} Λ) (f j)).obj
    ((constantSheaf (Y j).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M j))
  -- Kill the projected class by a cover of the corresponding finite source.
  have hcover (j : Fin n) := by
    have : IsFinite (f j) := hf j
    have : LocallyOfFinitePresentation (f j) := hfp j
    have : Finite (M j) := hM j
    exact exists_finite_cover_pushforward_unit_closed_cohomology_eq_zero
      (f j) i Λ (M j) q hq
        (Sheaf.H.map (V.map (U.map (φ ≫ biproduct.π A j))) q x)
  choose Y' π hπ hsurj hπfp hkill using hcover
  let B (j : Fin n) := (lowerStar (ModuleCat.{u + 1} Λ) (f j)).obj
    ((lowerStar (ModuleCat.{u + 1} Λ) (π j)).obj
      (((π j)^*[ModuleCat.{u + 1} Λ]).obj
        ((constantSheaf (Y j).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M j))))
  let b (j : Fin n) : A j ⟶ B j :=
    (lowerStar (ModuleCat.{u + 1} Λ) (f j)).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (π j)).unit.app
        ((constantSheaf (Y j).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M j)))
  -- Surjectivity makes each unit monic; right adjoints preserve monomorphisms.
  have hb (j : Fin n) : Mono (b j) := by
    have := mono_unit_app_of_surjective Λ (π j) (hsurj j).surj
      ((constantSheaf (Y j).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M j))
    dsimp only [b]
    infer_instance
  let : Mono φ := hφ
  let : ∀ j, Mono (b j) := hb
  refine ⟨⨁ B, φ ≫ biproduct.map b, inferInstance, ?_⟩
  change Sheaf.H.map (V.map (U.map (φ ≫ biproduct.map b))) q x = 0
  let z := Sheaf.H.map (V.map (U.map (φ ≫ biproduct.map b))) q x
  have hz (j : Fin n) :
      Sheaf.H.map (V.map (U.map (biproduct.π B j))) q z = 0 := by
    dsimp only [z]
    rw [← Sheaf.H.map_comp_apply, ← V.map_comp, ← U.map_comp,
      Category.assoc, biproduct.map_π, ← Category.assoc,
      U.map_comp, V.map_comp, Sheaf.H.map_comp_apply]
    exact hkill j
  -- After the additive restriction functor, the projections detect zero in cohomology.
  apply (Abelian.Ext.addEquivBiproduct _
    (isBilimitOfPreserves (U ⋙ V) (biproduct.isBilimit B)) q).injective
  rw [map_zero]
  funext j
  exact hz j

end AlgebraicGeometry.Etale
