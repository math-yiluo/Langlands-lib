/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompletedCoefficientData
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
import WeilConjectures.CategoryTheory.Scalar.ScalarTelescopeRingUniversal
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
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.EssentiallySmall
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying

/-!
# Rational coefficient comparison from fraction maps
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

private theorem sfb_rational_comparison_of_fraction_maps
    (ℓ : ℕ) (R K : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    (i : ∀ X : Scheme.{u}, coefficientRing X (Mon.mk (Profinite.continuousMapRingObj R)) ⟶
      coefficientRing X (Mon.mk (Profinite.continuousMapRingObj K)))
    (j : ∀ X : Scheme.{u}, ℕ →
      (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj R) X) ⟶
        sfbRationalCoefficientModule R K i X))
    (hj : ∀ X : Scheme.{u},
      IsIso (ℓ • 𝟙 (condensedRingObj (Profinite.continuousMapRingObj K) X)) ∧
      (j X 0).hom = (i X).hom ∧
      (∀ n, ℓ • j X (n + 1) = j X n) ∧
      (∀ (B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj R) X))
        (b : ℕ → (Mod.regular
          (condensedRingObj (Profinite.continuousMapRingObj R) X) ⟶ B)),
        (∀ n, ℓ • b (n + 1) = b n) →
        ∃! a : sfbRationalCoefficientModule R K i X ⟶ B, ∀ n, j X n ≫ a = b n))
    (hnat : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (n : ℕ),
      (upperStar Ab.{u + 1} f).map (j Y n).hom ≫
          ((coefficientPullbackIso f
            (Mon.mk (Profinite.continuousMapRingObj K))).hom).hom =
        ((coefficientPullbackIso f
            (Mon.mk (Profinite.continuousMapRingObj R))).hom).hom ≫ (j X n).hom) :
    ∃ ι : ∀ X : Scheme.{u}, sfbRationalizationSequence ℓ R X ⟶
        (Functor.const ℕ).obj (sfbRationalCoefficientModule R K i X),
      (∀ X : Scheme.{u},
        ((ι X).app 0).hom = (i X).hom ∧
        Nonempty (IsColimit (Cocone.mk (sfbRationalCoefficientModule R K i X) (ι X))) ∧
        IsIso (ℓ • 𝟙 (condensedRingObj (Profinite.continuousMapRingObj K) X))) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (m : ℕ),
        (upperStar Ab.{u + 1} f).map (((ι Y).app m).hom) ≫
            ((coefficientPullbackIso f
            (Mon.mk (Profinite.continuousMapRingObj K))).hom).hom =
          ((coefficientPullbackIso f
            (Mon.mk (Profinite.continuousMapRingObj R))).hom).hom ≫
            ((ι X).app m).hom) ∧
      (∀ (X : Scheme.{u}) (B : Mon (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})),
        IsIso (ℓ • 𝟙 B.X) →
        ∀ a : coefficientRing X (Mon.mk (Profinite.continuousMapRingObj R)) ⟶ B,
          ∃! b : coefficientRing X (Mon.mk (Profinite.continuousMapRingObj K)) ⟶ B,
            i X ≫ b = a) := by
  let ι (X : Scheme.{u}) : sfbRationalizationSequence ℓ R X ⟶
      (Functor.const ℕ).obj (sfbRationalCoefficientModule R K i X) :=
    NatTrans.ofSequence (j X) (fun n ↦ by
      dsimp only [sfbRationalizationSequence]
      rw [Functor.ofSequence_map_homOfLE_succ]
      change (ℓ • 𝟙 _) ≫ j X (n + 1) = j X n ≫ 𝟙 _
      simpa only [Category.comp_id, Preadditive.nsmul_comp, Category.id_comp] using
        (hj X).2.2.1 n)
  have hrec (X : Scheme.{u}) (c : Cocone (sfbRationalizationSequence ℓ R X)) (n : ℕ) :
      ℓ • c.ι.app (n + 1) = c.ι.app n := by
    have h := c.w (homOfLE (Nat.le_succ n))
    simp only [sfbRationalizationSequence, Functor.ofSequence_map_homOfLE_succ] at h
    change (ℓ • 𝟙 (Mod.regular
      (condensedRingObj (Profinite.continuousMapRingObj R) X))) ≫
        c.ι.app (n + 1) = c.ι.app n at h
    change ℓ • (c.ι.app (n + 1) : Mod.regular
      (condensedRingObj (Profinite.continuousMapRingObj R) X) ⟶ c.pt) = c.ι.app n
    simpa only [Preadditive.nsmul_comp, Category.id_comp] using h
  have hc (X : Scheme.{u}) : IsColimit
      (Cocone.mk (sfbRationalCoefficientModule R K i X) (ι X)) := by
    refine
      { desc := fun c ↦ ((hj X).2.2.2 c.pt (fun n ↦ c.ι.app n) (hrec X c)).choose
        fac := ?_
        uniq := ?_ }
    · intro c n
      exact ((hj X).2.2.2 c.pt (fun n ↦ c.ι.app n) (hrec X c)).choose_spec.1 n
    · intro c a ha
      exact ((hj X).2.2.2 c.pt (fun n ↦ c.ι.app n) (hrec X c)).choose_spec.2 a ha
  refine ⟨ι, fun X ↦ ⟨(hj X).2.1, ⟨hc X⟩, (hj X).1⟩, hnat, ?_⟩
  intro X B hB a
  exact scalar_telescope_ring_universal ℓ _ _ (i X) (ι X) (hj X).2.1 (hc X)
    (hj X).1 B hB a

/-- Assemble a rational coefficient comparison from the existing fraction maps.
-/
theorem sfb_rational_comparison_from_completed
    (ℓ : ℕ) (R K : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    (φ : R →+* K) (hφ : Continuous φ)
    (h : ∃ j : ∀ X : Scheme.{u}, ℕ →
      (Mod.regular ((completedCoefficient X (Profinite.continuousMapRingSheaf R)).X) ⟶
        ((Mod.comap (completedCoefficientMap X
          (Profinite.continuousMapRingSheafMap φ hφ)).hom).obj
        (Mod.regular (completedCoefficient X (Profinite.continuousMapRingSheaf K)).X))),
      (∀ X : Scheme.{u},
      IsIso (ℓ • 𝟙 ((completedCoefficient X (Profinite.continuousMapRingSheaf K)).X)) ∧
      (j X 0).hom = (completedCoefficientMap X
          (Profinite.continuousMapRingSheafMap φ hφ)).hom ∧
      (∀ n, ℓ • j X (n + 1) = j X n) ∧
      (∀ (B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          ((completedCoefficient X (Profinite.continuousMapRingSheaf R)).X))
        (b : ℕ → (Mod.regular
          (completedCoefficient X (Profinite.continuousMapRingSheaf R)).X ⟶ B)),
        (∀ n, ℓ • b (n + 1) = b n) →
        ∃! a : ((Mod.comap (completedCoefficientMap X
          (Profinite.continuousMapRingSheafMap φ hφ)).hom).obj
        (Mod.regular (completedCoefficient X (Profinite.continuousMapRingSheaf K)).X)) ⟶ B,
          ∀ n, j X n ≫ a = b n)) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (n : ℕ),
      (upperStar Ab.{u + 1} f).map (j Y n).hom ≫
          ((coefficientPullbackIso f
            (Mon.mk (Profinite.continuousMapRingObj K))).hom).hom =
        ((coefficientPullbackIso f
            (Mon.mk (Profinite.continuousMapRingObj R))).hom).hom ≫ (j X n).hom)) :
    ∃ ι : ∀ X : Scheme.{u}, sfbRationalizationSequence ℓ R X ⟶
        (Functor.const ℕ).obj (sfbRationalCoefficientModule R K
          (fun Z ↦ completedCoefficientMap Z (Profinite.continuousMapRingSheafMap φ hφ)) X),
      (∀ X : Scheme.{u},
        ((ι X).app 0).hom = (completedCoefficientMap X
          (Profinite.continuousMapRingSheafMap φ hφ)).hom ∧
        Nonempty (IsColimit (Cocone.mk (sfbRationalCoefficientModule R K
          (fun Z ↦ completedCoefficientMap Z (Profinite.continuousMapRingSheafMap φ hφ)) X)
          (ι X))) ∧
        IsIso (ℓ • 𝟙 (condensedRingObj (Profinite.continuousMapRingObj K) X))) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (m : ℕ),
        (upperStar Ab.{u + 1} f).map (((ι Y).app m).hom) ≫
            ((coefficientPullbackIso f
            (Mon.mk (Profinite.continuousMapRingObj K))).hom).hom =
          ((coefficientPullbackIso f
            (Mon.mk (Profinite.continuousMapRingObj R))).hom).hom ≫
            ((ι X).app m).hom) ∧
      (∀ (X : Scheme.{u}) (B : Mon (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})),
        IsIso (ℓ • 𝟙 B.X) →
        ∀ a : coefficientRing X (Mon.mk (Profinite.continuousMapRingObj R)) ⟶ B,
          ∃! b : coefficientRing X (Mon.mk (Profinite.continuousMapRingObj K)) ⟶ B,
            completedCoefficientMap X
              (Profinite.continuousMapRingSheafMap φ hφ) ≫ b = a) := by
  classical
  obtain ⟨j, hj, hnat⟩ := h
  exact sfb_rational_comparison_of_fraction_maps ℓ R K _ j hj hnat

end AlgebraicGeometry.ProEtale
