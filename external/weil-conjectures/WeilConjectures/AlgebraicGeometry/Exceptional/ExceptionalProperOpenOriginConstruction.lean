/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemInterfaces
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalProCompactSupportConstruction
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemCompactificationComparisonConstruction

/-! # Construction of the proper/open strict-system operation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry

variable {O : Type (u + 1)} [CommRing O] {ell : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  {S : StrictEtaleCompactSupport O ell c}
  (G : StrictEtaleExceptionalAdjoint O ell c S)
  (CX : ExceptionalSystemSiteComparison O ell X S.PX)
  (CY : ExceptionalSystemSiteComparison O ell Y S.PY)
  (CZ : ExceptionalSystemSiteComparison O ell c.Z S.PZ)

/-- The pro-etale compact-support operation and its comparison data exist.
Source: Zheng Construction 5.15 and Lemmas 4.10, 5.16 and 5.22; Stacks 0B65.
(blueprint: lem-sf-exceptional-proper-open-origin-construction).

Proof: construct extension by zero on the pro-etale coefficient-system category,
then take the universal derived image of the proper factor.  The ordinary and
finite-level evaluation squares are obtained before localization.  The inverse
image comparison is the adjunction mate of the proper square followed by the
open square.  The mate identities and the recorded normalization equations give
an object of `ExceptionalSystemCompactificationComparison`; all constructions are
canonical and remain valid for zero rings and empty schemes. -/
theorem exceptionalProperOpenOriginConstruction
    [∀ n : ℕ, Finite (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))]
    (hX : ExceptionalSystemSiteEquivalence CX)
    (hY : ExceptionalSystemSiteEquivalence CY)
    (hZ : ExceptionalSystemSiteEquivalence CZ) :
    ∃ (P : ExceptionalProCompactSupport O ell c
        CX.proEvaluation CY.proEvaluation CZ.proEvaluation),
      Nonempty (ExceptionalSystemCompactificationComparison S CX CY CZ P) := by
  obtain ⟨P⟩ := exceptionalProCompactSupport_exists CX CY CZ hX hY hZ
  exact ⟨P, exceptionalSystemCompactificationComparison_exists CX CY CZ hX hY hZ P⟩

end AlgebraicGeometry
