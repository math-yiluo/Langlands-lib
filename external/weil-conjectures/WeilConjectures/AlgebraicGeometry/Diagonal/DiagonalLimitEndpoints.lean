/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimitInterface
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalSupportedOrdinaryLimit
import all WeilConjectures.AlgebraicGeometry.DiagonalEndpointsProof.DiagonalLimitEndpointsAux

/-! # Normalized completed diagonal endpoints

Source: the diagonal tower limit proof, paragraphs (1) and (3).
(blueprint: lem-sfb-diagonal-limit-endpoints).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u a b v w g
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
open DiagonalEndpointsProof

attribute [local irreducible] diagonalCompletedSource diagonalOrdinaryRlim
  diagonalSourceLimitMap diagonalTargetLimitMap diagonalRootLimitComparison
  diagonalSingleLimitComparison diagonalShiftedSingleLimitComparison
  diagonalCompletedRestriction DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ HasDerivedCategory.standard
  HomotopyCategory.singleFunctors diagonalScalarExtension diagonalScalarAdjunction
  diagonalIntegralBoundary diagonalDerivedSingleCounit

set_option linter.unusedVariables false in
/-- The ordinary supported constant and root limits, their canonical derived-limit
comparisons, and intrinsic completeness of the two completed endpoints.

Source: blueprint `sk-prop-diagonal-tower-limit.proof.md`, paragraphs (1) and (3);
Stacks 099L and 099M (blueprint: lem-sfb-diagonal-limit-endpoints).
Proof: the cokernel presentation of D.ordinary identifies the source tower, including
its quotient maps, with the supported finite constant tower. Closed direct image is
exact and preserves limits; its limit is the restricted completed constant. The unit
section of this comparison is diagonalCompletedGenerator, so composing with each
finite projection gives the displayed source normalization. At level n the root
groups are ell^(n+1)-torsion, so their Z_l actions factor through
Z_l/ell^(n+1) = Z/ell^(n+1). Hence the underlying root comparison is Z_l-linear.
Forgetting scalars creates limits, giving t with underlying map precisely the
inverse of diagonalRootLimitComparison. Quotient transitions are
epic, as are root power transitions when ell is invertible. The Milnor calculation on
weakly contractible affines makes the canonical ordinary-to-derived-limit maps
isomorphisms. Uniqueness of total right derived limits identifies these maps with the
unit of L; compose with a and b and the shift comparison. Finally, the difference
operator on a countable power is invertible on each finite-torsion level by a finite
geometric inverse, and hence on the ordinary limits. Scalar restriction preserves
products and reflects isomorphisms. Exact countable products make the single-complex
embedding preserve them, so maps from ell-invertible objects vanish by successive
ell-division and invertibility of the difference operator. Shift and derived
restriction comparisons transport this to all four required assertions.
No choice of a map between the endpoints occurs in this assertion. -/
theorem diagonal_limit_endpoints (ℓ : ℕ) [Fact ℓ.Prime]
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
    ∃ (L : DiagonalRlim (DiagonalMod ℓ (diagonalSurface Y)))
      (s : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
        (diagonalCompletedSource ℓ Y) ≅ limit (D.ordinary.E.obj (diagonalIntegralSource Y)))
      (t : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
        (Scheme.purTwistZlModule (diagonalSurface Y) ℓ) ≅ limit H),
      (∀ n : ℕ,
        diagonalCompletedGenerator ℓ Y ≫ (diagonalForget ℓ (diagonalSurface Y)).map
          (s.hom ≫ limit.π (D.ordinary.E.obj (diagonalIntegralSource Y)) (op n)) =
        (diagonalScalarAdjunction ℓ (diagonalSurface Y)).unit.app (diagonalIntegralSource Y) ≫
          (diagonalForget ℓ (diagonalSurface Y)).map
            ((D.ordinary.π n).app (diagonalIntegralSource Y))) ∧
      HEq ((diagonalForget ℓ (diagonalSurface Y)).map t.hom)
        (diagonalRootLimitComparison ℓ (diagonalSurface Y) H roots).inv ∧
      IsIso (diagonalSourceLimitMap ℓ Y D a L s) ∧
      IsIso (diagonalTargetLimitMap ℓ Y D H b L t) ∧
      (∀ V : DerivedCategory (DiagonalCompleted ℓ (diagonalSurface Y)),
        IsIso (ℓ • 𝟙 V) → Subsingleton (V ⟶ diagonalCompletedDomain ℓ Y)) ∧
      (∀ V : DerivedCategory (DiagonalCompleted ℓ (diagonalSurface Y)),
        IsIso (ℓ • 𝟙 V) → Subsingleton (V ⟶ diagonalCompletedCodomain ℓ Y)) ∧
      (∀ V : DerivedCategory (DiagonalMod ℓ (diagonalSurface Y)),
        IsIso (ℓ • 𝟙 V) → Subsingleton (V ⟶
          (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).obj
            (diagonalCompletedDomain ℓ Y))) ∧
      (∀ V : DerivedCategory (DiagonalMod ℓ (diagonalSurface Y)),
        IsIso (ℓ • 𝟙 V) → Subsingleton (V ⟶
          (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).obj
            (diagonalCompletedCodomain ℓ Y))) := by
  clear hpℓ hcompletion
  classical
  let X := diagonalSurface Y
  let S := D.ordinary.E.obj (diagonalIntegralSource Y)
  let s := (diagonal_supported_ordinary_limit ℓ Y D.ordinary).choose
  have hs := (diagonal_supported_ordinary_limit ℓ Y D.ordinary).choose_spec
  let t := (root_limit_iso ℓ X H roots).choose
  have ht := (root_limit_iso ℓ X H roots).choose_spec
  let L := Classical.choice (moduleRlim_exists ℓ X)
  have hS : IsIso (diagonalOrdinaryRlim L S) :=
    ordinaryRlim_isIso_of_epi ℓ X L S
      (ordinary_tower_epi ℓ (diagonalScalarExtension ℓ X) D.ordinary _)
  have hX : IsUnit (ℓ : Γ(X, ⊤)) := by
    simpa only [Nat.zero_add, pow_one] using diagonalSurface_power_unit ℓ Y hY 0
  have hHepi (n : ℕ) : Epi (H.map (homOfLE (Nat.le_succ n)).op) :=
    root_system_epi ℓ X hX H roots n
  have hH : IsIso (diagonalOrdinaryRlim L H) :=
    ordinaryRlim_isIso_of_epi ℓ X L H hHepi
  have hsource : IsIso (diagonalSourceLimitMap ℓ Y D a L s) :=
    sourceLimitMap_isIso ℓ Y D a L s hS
  have htarget : IsIso (diagonalTargetLimitMap ℓ Y D H b L t) :=
    targetLimitMap_isIso ℓ Y D H b L t hH
  have hSkill (n : ℕ) : ℓ ^ (n + 1) • 𝟙 (S.obj (op n)) = 0 :=
    ordinary_tower_killed ℓ (diagonalScalarExtension ℓ X) D.ordinary _ n
  have hHkill (n : ℕ) : ℓ ^ (n + 1) • 𝟙 (H.obj (op n)) = 0 :=
    root_system_killed ℓ X H roots n
  -- Finite torsion and exact products give completeness in both coefficient categories.
  exact ⟨L, s, t, hs, ht, hsource, htarget,
    completedEndpoints_orthogonal ℓ X (2 : ℤ)
      (diagonalCompletedSource ℓ Y) (Scheme.purTwistZlModule X ℓ) S H s t hSkill hHkill⟩

end AlgebraicGeometry.ProEtale
