/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geometric.GeometricOrdinaryRealization
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricCoefficientPullback
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricEvaluationMate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Derived evaluation and coefficient comparison for a fixed ordinary realization

Source: Zheng Construction 4.1, the paragraph preceding Lemma 4.10 and Lemma 4.10.
(blueprint: lem-coef-semilinear-geometric-derived-evaluation)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush)

variable (A : Data.{c, v, r} J B τ)
  (O : GeometryOrdinary.{c, v, r} J B τ J' uInv uPush adjSet)
  (target : Data.{c, v, r} J' O.coefficients O.coefficientTransition)
  [∀ n : ℕ, Abelian.HasKInjectiveResolutions (Mod.{c, v, max c v r} J' (O.coefficients n))]
  [Abelian.HasKInjectiveResolutions
    (Systems.{c, v, max c v r} J' O.coefficients O.coefficientTransition)]

/-- The derived right-evaluation and scalar comparisons of a fixed ordinary realization.
The left evaluation and both derived adjunctions are fixed canonical localizations.
Source: Zheng Construction 4.1 and Lemma 4.10.
(blueprint: lem-coef-semilinear-geometric-derived-evaluation). -/
structure GeometryEvaluation where
  /-- Derived direct-image evaluation; no K-injective evaluation assumption is made. -/
  pushEvaluation : ∀ n : ℕ,
    O.push.rightDerivedFunctor ⋙ e.{c, v, max c v r} J B τ n ≅
      e.{c, v, max c v r} J' O.coefficients O.coefficientTransition n ⋙ (O.levelPush
        n).rightDerivedFunctor
  /-- The evaluation identifications respect the actual adjunction units. -/
  unit_evaluation : ∀ (n : ℕ) (M : DS.{c, v, max c v r} J B τ),
    (e.{c, v, max c v r} J B τ n).map
      (O.ordinaryAdjunction.mapDerivedCategoryRightDerivedAdjunction.unit.app M) ≫
        (pushEvaluation n).hom.app (O.pull.mapDerivedCategory.obj M) ≫
        (O.levelPush n).rightDerivedFunctor.map (((geometryPullEvaluation J B τ J' uInv uPush adjSet
          O) n).hom.app M) =
      (O.levelAdjunction n).mapDerivedCategoryRightDerivedAdjunction.unit.app ((e.{c, v, max c v r}
        J B τ n).obj M)
  /-- The evaluation identifications respect the actual adjunction counits. -/
  counit_evaluation : ∀ (n : ℕ)
    (N : DS.{c, v, max c v r} J' O.coefficients O.coefficientTransition),
    (derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (O.coefficients n) (O.inverseImage n).modules).map ((pushEvaluation n).hom.app N) ≫
        (O.levelAdjunction n).mapDerivedCategoryRightDerivedAdjunction.counit.app
          ((e.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).obj N) =
      ((geometryPullEvaluation J B τ J' uInv uPush adjSet O) n).inv.app
        (O.push.rightDerivedFunctor.obj N) ≫
        (e.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).map
          (O.ordinaryAdjunction.mapDerivedCategoryRightDerivedAdjunction.counit.app N)
  /-- The coefficient tensor/inverse-image comparison whose mate is b. -/
  coefficientPullback : ∀ {m n : ℕ} (h : n ≤ m),
    (Data.scalar.{c, v, r} A h).T ⋙
        ((derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (O.coefficients n) (O.inverseImage n).modules) :
          D.{c, v, max c v r} J (B n) ⥤ D.{c, v, max c v r} J' (O.coefficients n)) ≅
      ((derivedExact.{c, v, max c v r, c, v} J J' (B m)
          (O.coefficients m) (O.inverseImage m).modules) :
        D.{c, v, max c v r} J (B m) ⥤ D.{c, v, max c v r} J' (O.coefficients m)) ⋙
          (Data.scalar.{c, v, r} target h).T
  /-- Coefficient pullback is the scalar-adjunction transpose of the localized
  identity-on-underlying-sheaves restriction comparison. -/
  coefficientPullback_transpose : ∀ {m n : ℕ} (h : n ≤ m)
    (P : D.{c, v, max c v r} J (B m)),
    ((target.scalar h).adjunction.homEquiv _ _) ((coefficientPullback h).inv.app P) =
      (derivedExact.{c, v, max c v r, c, v} J J' (B m) (O.coefficients m) (O.inverseImage
        m).modules).map
        ((A.scalar h).adjunction.unit.app P) ≫
      ((Functor.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.mapDerivedCategoryNatIso (O.restrictionPullback h) ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm).hom.app ((A.scalar h).T.obj P))

/-- Derived direct-image evaluation is obtained by conjugating singleton extension.
Source: Zheng Construction 4.1 and the paragraph preceding Lemma 4.10, printed pp. 21, 23;
Stacks 03EL and 07A6.
(blueprint: lem-coef-semilinear-geometric-derived-evaluation).

Proof: compatibility for every composite coefficient map follows by induction from
the adjacent compatibility, using preservation of composition. Apply the existing
exists_scalarInverseImageIndependent theorem to the actual ordinary scalar adjunctions.
Its unit equation and the identity-on-underlying-sheaves restriction comparison fix
the scalar mate. Resolve by flat-term K-flat complexes, where inverse image preserves
both flatness and K-flatness, and localize. The scalar transpose formula follows from
the ordinary adjunction formula and naturality of the resolving comparison.
For evaluation at n use the finite left extension E_n: below n it is coefficient
extension, and above n it is zero.
The just-constructed scalar comparison gives V E_n ≅ E'_n V_n on these representatives,
and hence V L_n ≅ L'_n V_n after localization. Conjugate its inverse through the
composite adjunctions L_n V ⊣ G e_n and V_n L'_n ⊣ e'_n G_n. This gives the displayed
push evaluation isomorphism. At level n, the singleton comparison is the ordinary
multiplication identification; its unit equation follows on representatives from
the ordinary unit-evaluation equation. The conjugate unit and counit identities give
exactly the two displayed derived unit/counit equations. This proof does not assume
that evaluation preserves K-injectives or detects equality of derived morphisms. -/
theorem semilinearGeometryEvaluation [PreservesFiniteLimits uInv] :
    Nonempty (GeometryEvaluation.{c, v, r} J B τ J' uInv uPush adjSet A O target) := by
  classical
  let β (n : ℕ) :=
    (mateEquiv O.ordinaryAdjunction.mapDerivedCategoryRightDerivedAdjunction
      (O.levelAdjunction n).mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _
        ((geometryPullEvaluation.{c, v, r} J B τ J' uInv uPush adjSet O) n).inv))
  have hβ (n : ℕ) : IsIso (β n) :=
    geometricEvaluationMate_isIso.{c, v, r} J B τ J' uInv uPush adjSet O n
  let γ {m n : ℕ} (h : n ≤ m) :=
    ((mateEquiv (A.scalar h).adjunction (target.scalar h).adjunction).symm
      (TwoSquare.mk _ _ _ _
        (Functor.mapDerivedCategorySquareIso (O.restrictionPullback h)).hom))
  have hγ {m n : ℕ} (h : n ≤ m) : IsIso (γ h) :=
    geometricCoefficientPullbackMate_isIso.{c, v, r} J B τ J' uInv uPush adjSet A O target h
  refine ⟨{
    pushEvaluation := fun n ↦ @asIso _ _ _ _ (β n) (hβ n)
    unit_evaluation := ?_
    counit_evaluation := ?_
    coefficientPullback := fun h ↦ (@asIso _ _ _ _ (γ h) (hγ h)).symm
    coefficientPullback_transpose := ?_ }⟩
  · intro n M
    have hu := unit_mateEquiv
      O.ordinaryAdjunction.mapDerivedCategoryRightDerivedAdjunction
      (O.levelAdjunction n).mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _
        ((geometryPullEvaluation.{c, v, r} J B τ J' uInv uPush adjSet O) n).inv) M
    change _ ≫ (β n).app _ ≫ _ = _
    erw [← Category.assoc, hu, Category.assoc, ← Functor.map_comp,
      Iso.inv_hom_id_app, (O.levelPush n).rightDerivedFunctor.map_id, Category.comp_id]
    rfl
  · intro n N
    exact mateEquiv_counit
      O.ordinaryAdjunction.mapDerivedCategoryRightDerivedAdjunction
      (O.levelAdjunction n).mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _
        ((geometryPullEvaluation.{c, v, r} J B τ J' uInv uPush adjSet O) n).inv) N
  · intro m n h P
    change (target.scalar h).adjunction.homEquiv _ _ ((γ h).app P) = _
    erw [Adjunction.homEquiv_unit]
    exact (unit_mateEquiv_symm (A.scalar h).adjunction (target.scalar h).adjunction
      (TwoSquare.mk _ _ _ _
        (Functor.mapDerivedCategorySquareIso (O.restrictionPullback h)).hom) P).symm

end WeilConjectures.SemilinearSections
