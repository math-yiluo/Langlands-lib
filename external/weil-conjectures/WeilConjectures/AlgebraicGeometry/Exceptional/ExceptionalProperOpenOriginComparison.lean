/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemInterfaces
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalProperOpenOriginConstruction
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalProperOpenOriginProperties

/-! # Proper/open comparison on strict pro-etale systems -/

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

/-- Construct the proper/open pro-etale operation and its canonical comparison,
including origin stability before making an exceptional adjunction.
Source: Zheng Construction 5.15 and Lemmas 4.10, 5.16 and 5.22; Stacks 0B65.
(blueprint: lem-sf-exceptional-proper-open-origin-comparison).

Proof: lift the open restriction and proper inverse image to ordinary strict
systems. Their levelwise section maps commute with restriction of scalars. The
left adjoint of open restriction is extension by zero, constructed by sheafifying
the direct sum of sections over open lifts; kernels and cokernels are termwise.
Exact localization gives its derived adjunction and representative factors.
Construct the inverse-image square on ordinary sections and localize it, with
its evaluation square retained. Take the proper mate and compose with the open
comparison. The finite proper mate is invertible for the quasi-compact,
quasi-separated proper factor on bounded-below inputs. Exact evaluation preserves
these bounds and detects isomorphisms, so the system map is invertible. The source
site counit identifies its origin version. This gives left stability on origins,
on systems and at each finite level. For the finite right bound, realize a
bounded-below finite input by a system
concentrated at that level, with every other level zero and zero transitions.
Exact evaluation of the etale system bound, followed by G.evaluation, gives the
finite bound; no flat singleton extension is needed. The direct site image
preserves lower bounds. No absolute separatedness is used. Evaluating the actual
mate word gives the displayed comparison equation by the recorded unit/counit
identities and the open evaluation square. -/
theorem exceptionalProperOpenOriginComparison
    [∀ n : ℕ, Finite (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))]
    (hX : ExceptionalSystemSiteEquivalence CX)
    (hY : ExceptionalSystemSiteEquivalence CY)
    (hZ : ExceptionalSystemSiteEquivalence CZ) :
    ∃ (P : ExceptionalProCompactSupport O ell c
        CX.proEvaluation CY.proEvaluation CZ.proEvaluation)
      (R : ExceptionalSystemCompactificationComparison S CX CY CZ P),
      (∀ M, (∃ a : ℤ, M.IsGE a) →
        IsIso ((exceptionalSystemComparison R).app M)) ∧
      (∀ M, CX.origin M → CY.origin ((exceptionalProSupport P).obj M)) ∧
      (∀ n M, CX.levelOrigin n M → CY.levelOrigin n
        ((P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct).obj M)) ∧
      (∀ n M, CX.levelOrigin n M →
        IsIso ((exceptionalSystemLevelOriginComparison R n).app M)) ∧
      (∀ n N, CY.levelOrigin n N →
        ∃ a : ℤ, ((G.levelRight n).obj ((CY.image.level n).direct.obj N)).IsGE a) ∧
    (∀ n M,
    (CY.proEvaluation.evaluation n).map ((exceptionalSystemComparison R).app M) ≫
      (exceptionalProSupportEvaluation P n).hom.app (CX.image.system.inverse.obj M) ≫
      (P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct).map
        ((CX.image.inverseEvaluation n).hom.app M) =
    (CY.image.inverseEvaluation n).hom.app (S.functor.obj M) ≫
      (CY.image.level n).inverse.map ((S.evaluation n).hom.app M) ≫
      (exceptionalSystemLevelComparison R n).app ((S.PX.evaluation n).obj M)) := by
  obtain ⟨P, ⟨R⟩⟩ := exceptionalProperOpenOriginConstruction CX CY CZ hX hY hZ
  obtain h := exceptionalProperOpenOriginProperties G CX CY CZ hX hY hZ P R
  exact ⟨P, R, h⟩

end AlgebraicGeometry
