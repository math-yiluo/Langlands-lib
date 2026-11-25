/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.FormalFunctionsFinitePullback
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.FormalFunctionsFiniteQuotientIsoB
import WeilConjectures.AlgebraicGeometry.FormalFunctionsFiniteQuotientIsoR
@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
namespace AlgebraicGeometry
/-- The canonical quotient-system isomorphism, with its factorization of pullback.
Source: Stacks Project, Tags 02OD and 089W; Tags 01F7 and 01FB.
(blueprint: lem-weil-pbc-formal-functions-finite-quotient-iso)

Proof: Write A = O_y, g' : X' → X and i'_n = formalFunctionsFiniteι f y n.
Pasting the pullback squares shows that i'_n is the base change of
Spec(A/m^(n+1)) → Spec A, with ideal J^(n+1). Pullback of F' along i'_n
identifies with F_n: the identification is fixed by the equation of adjunction
units in formalFunctionsFiniteFMap. Coherence implies quasi-coherence, preserved
by tensor pullback. The closed-immersion unit quotient theorem therefore gives
rho_n : F'/J^(n+1)F' ≅ i'_(n*)F_n, with rho_n q_n equal to this h-map.
Apply H^p to rho_n and compose with the affine cohomology edge isomorphism 089W
to obtain b_n. The edge map is the canonical cohomology h-map. Functoriality
then identifies b_n H^p(q_n) with formalFunctionsFinitePullback f y F p n.
Linearity of h-map cohomology and the scalar identity obtained by applying
Gamma-Spec naturality to i'_n show that this pullback is A-linear; let r_n
be this same additive map with that linear structure. Evaluation of algebraMap A
in the completion at level n+1 is Ideal.Quotient.mk, so b_n is also linear
for precisely the restricted completed action displayed here. For adjacent
levels compare the two maps from F'/J^(n+2)F' into i'_(n*)F_n after the epi q_(n+1).
Their composites both equal the unit for i'_n by pullback composition and the
adjunction-unit equation defining formalFibreTransitionFMap. Cancel that epi,
then apply cohomology functoriality to get naturality of b_n. Every arrow of
N opposite is a composite of adjacent arrows; the component isomorphisms
assemble into b. The quotient-unit equation gives the first displayed equality,
and the definition of r_n gives the second. This uses no stalk comparison or
Theta compatibility, and works for degree zero, zero F and an empty fibre. -/
theorem formalFunctions_finite_quotient_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
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
      ∀ (n : ℕ) (z : formalFunctionsLocalCohomology f y F p),
        r n z = formalFunctionsFinitePullback f y F p n z := by
  dsimp
  obtain ⟨b, hb⟩ := formalFunctions_finite_quotient_iso_b f F hF y p
  obtain ⟨r, hr, hp⟩ := formalFunctions_finite_quotient_iso_r f F hF y p b hb
  exact ⟨b, r, hr, hp⟩
end AlgebraicGeometry
