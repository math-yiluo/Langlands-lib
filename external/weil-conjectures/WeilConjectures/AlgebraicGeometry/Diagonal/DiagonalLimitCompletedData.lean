/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimitInterface
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalLimitEndpoints
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalLimitFiniteReduction
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalCompleteScalarRestrictionCore
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalCompletedDataAssembly

/-! # The completed part of the diagonal limit

Source: the diagonal tower limit proof, paragraph (3).
(blueprint: lem-sfb-diagonal-limit-completed-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- The completed part of the normalized diagonal limit, from the endpoint
and finite reduction calculations. Source: diagonal tower limit, paragraph (3)
(blueprint: lem-sfb-diagonal-limit-completed-data).
Proof: use the endpoint theorem to identify both ordinary and derived limits and
to obtain completeness. Existing complete-scalar restriction gives a hom-set
bijection; the categorical assembly theorem lifts the boundary and proves
uniqueness. The finite-reduction theorem supplies its normalized finite equations. -/
theorem diagonal_limit_completed_data (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (hcompletion : DiagonalCompletionSpec ℓ (diagonalSurface Y) D)
    (H : DiagonalSystems ℓ (diagonalSurface Y))
    (roots : H ⋙ diagonalForget ℓ (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) ℓ (Fact.out : ℓ.Prime))
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧) :
    diagonalCompleteDataAssertion ℓ (diagonalCompletedRestriction ℓ (diagonalSurface Y))
      (diagonalCompletedSource ℓ Y) (Scheme.purTwistZlModule (diagonalSurface Y) ℓ)
      (D.ordinary.E.obj (diagonalIntegralSource Y)) H _ _
      (D.T.map (diagonalIntegralBoundary Y).hom) a b
      (fun s ↦ ∀ n : ℕ,
        diagonalCompletedGenerator ℓ Y ≫ (diagonalForget ℓ (diagonalSurface Y)).map
          (s.hom ≫ limit.π (D.ordinary.E.obj (diagonalIntegralSource Y)) (op n)) =
        (diagonalScalarAdjunction ℓ (diagonalSurface Y)).unit.app (diagonalIntegralSource Y) ≫
          (diagonalForget ℓ (diagonalSurface Y)).map
            ((D.ordinary.π n).app (diagonalIntegralSource Y)))
      (fun t ↦ HEq ((diagonalForget ℓ (diagonalSurface Y)).map t.hom)
        (diagonalRootLimitComparison ℓ (diagonalSurface Y) H roots).inv) := by
  classical
  refine Exists.elim
    (diagonal_limit_endpoints ℓ k p hpℓ Y hY D hcompletion H roots a b) (fun L hL ↦ ?_)
  refine Exists.elim hL (fun s hsrest ↦ ?_)
  refine Exists.elim hsrest (fun t hparts ↦ ?_)
  obtain ⟨hs, ht, hsource, htarget, hP, hQ, hPC, hQC⟩ := hparts
  refine Exists.elim (diagonal_limit_finite_reduction ℓ k p hpℓ Y hY D hcompletion
    H a b L s t hsource htarget) (fun M hM ↦ ?_)
  let F := diagonalCompletedUnderlying ℓ (diagonalSurface Y)
  have hF : Function.Bijective (fun δ : diagonalCompletedDomain ℓ Y ⟶
      diagonalCompletedCodomain ℓ Y ↦ F.map δ) := by
    as_aux_lemma =>
      let complete : ObjectProperty
          (DerivedCategory (DiagonalCompleted ℓ (diagonalSurface Y))) :=
        fun P ↦ ∀ V : DerivedCategory (DiagonalMod ℓ (diagonalSurface Y)),
          IsIso (ℓ • 𝟙 V) → Subsingleton (V ⟶ F.obj P)
      obtain ⟨ff⟩ := DiagonalTrace.diagonalCompleteScalarRestrictionCore ℓ (diagonalSurface Y)
      let P : complete.FullSubcategory := ⟨diagonalCompletedDomain ℓ Y, hPC⟩
      let Q : complete.FullSubcategory := ⟨diagonalCompletedCodomain ℓ Y, hQC⟩
      constructor
      · intro x y h
        have hxy : (ObjectProperty.homMk x : P ⟶ Q) = ObjectProperty.homMk y :=
          ff.map_injective h
        exact congrArg (fun f : P ⟶ Q ↦ f.hom) hxy
      · intro f
        obtain ⟨g, hg⟩ := ff.map_surjective (X := P) (Y := Q) f
        exact ⟨g.hom, hg⟩
  apply diagonalCompleteData_of_bijective
    ℓ (diagonalCompletedRestriction ℓ (diagonalSurface Y)) _ _ _ _ _ _
    (D.T.map (diagonalIntegralBoundary Y).hom) a b _ _ L M s t hs ht
    hsource htarget hP hQ hF
  intro δ hδ n
  obtain ⟨e, g, he, hg, hmap⟩ := hM (diagonalIntegralBoundary Y).hom δ hδ n
  exact ⟨e, g, he, hg, hmap⟩

end AlgebraicGeometry.ProEtale
