/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.FormalFunctionsLocalStalkComparison
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.FormalFunctionsFiniteQuotientIso
import WeilConjectures.AlgebraicGeometry.FormalFunctionsFiniteQuotientMaps

/-! # Finite quotient cohomology on the local base change

Source: Stacks Project, Tag 02OD, finite-level identifications; Tags 089W and 01FB.
(blueprint: lem-weil-pbc-formal-functions-finite-quotient-comparison)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
namespace AlgebraicGeometry
/-- The finite quotient system on the local base change is identified with the
infinitesimal fibre cohomology system. The theorem records only the finite-level
part of the geometric dictionary and leaves the stalk comparison separate.
Source: Stacks Project, Tag 02OD, finite-level identifications; Tags 089W and 01FB.
(blueprint: lem-weil-pbc-formal-functions-finite-quotient-comparison)

Proof: Write A = O_y and let i'_n : X_n → X' be induced by the factorization
Spec(A/m^(n+1)) → Spec A → Y. Pasting pullback squares identifies X_n with the
quotient base change of X'. Its immersion ideal is J^(n+1), by compatibility of
extended ideals with powers. Composition of tensor pullbacks identifies F_n with
i'_n^*F'. The closed-immersion unit is epi with kernel J^(n+1)F', so it induces an
isomorphism from formalModuleQuotient J (n+1) F' to i'_{n*}F_n. Apply H^p and the
affine cohomology edge isomorphism 089W to get b_n. The action of the completed local
ring, when restricted along algebraMap A, agrees with the quotient action of A
because evaluation of algebraMap is Ideal.Quotient.mk. Thus b_n has exactly the
specified scalar action. For adjacent levels the two sheaf maps to i'_{n*}F_n agree
after precomposition with the epimorphic larger quotient projection: both are the
unit for the composite immersion. Cancel this epi and apply h-map functoriality.
This proves naturality on adjacent transitions and hence all arrows of the inverse
sequence, yielding b. Define r_n by the cohomology pullback along i'_n. Its A-linearity
follows from the same scalar identity, and factorization of the unit through the
quotient gives r_n = b_n H^p(q_n). For any linear a with the local germ formula,
apply r_n to that formula for a representative xi on V. Composition of pullbacks
identifies the resulting class with pullback along X_n → f^{-1}V. Restriction to its
inverse-image open yields precisely IsFormalFunctionsTheta for (r_n).comp a.
Resolution independence ensures that this holds for every I, K and comparison choice
in that predicate. This argument never requires r_n to be surjective, so it includes
p=0, F=0 and an empty fibre. It uses no comparison with a completed module or limit. -/
theorem formalFunctions_finite_quotient_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [IsLocallyNoetherian Y] (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) (y : Y) (p : ℕ) :
    let X' := pullback (Y.fromSpecStalk y) f
    let f' := pullback.fst (Y.fromSpecStalk y) f
    let F' := (Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F
    let J := (Scheme.IdealSheafData.ofIdealTop
      ((maximalIdeal (Y.presheaf.stalk y)).map
        (Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv.hom)).comap f'
    let C := RingedSpace.moduleCohomology X'.toRingedSpace p ⋙
      ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫ f'.appTop).hom
    ∃ b : formalCompletionSystem J F' ⋙ C ≅
      formalFibreCohomologySystem f y F p ⋙ ModuleCat.restrictScalars
        (algebraMap (Y.presheaf.stalk y)
          (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))),
    ∃ r : ∀ n : ℕ, formalFunctionsLocalCohomology f y F p →ₗ[Y.presheaf.stalk y]
      formalFibreCohomologyLocal f y F p n,
      (∀ (n : ℕ) (z : formalFunctionsLocalCohomology f y F p),
        r n z = (b.hom.app (op n)) ((C.map (formalModuleQuotientπ J (n + 1) F')) z)) ∧
      ∀ a : formalFunctionsStalk f y F p →ₗ[Y.presheaf.stalk y]
          formalFunctionsLocalCohomology f y F p,
        IsFormalFunctionsLocalComparison f y F p a →
          ∀ n : ℕ, IsFormalFunctionsTheta f y F p n ((r n).comp a) := by
  dsimp
  obtain ⟨b, r, hr, hpull⟩ := formalFunctions_finite_quotient_iso f F hF y p
  refine ⟨b, r, hr, ?_⟩
  intro a ha n
  exact formalFunctions_finite_quotient_maps f F hF y p n (r n) (hpull n) a ha
end AlgebraicGeometry
