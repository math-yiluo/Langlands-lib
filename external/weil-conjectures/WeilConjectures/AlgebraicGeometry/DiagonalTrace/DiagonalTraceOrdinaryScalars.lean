/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceCoefficients
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Coefficient.DiagonalTraceCoefficientRestriction
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceVaryingScalarSquare
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Completed.DiagonalTraceCompletedScalarSquare

/-! # Ordinary coefficient restrictions and their section normalizations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

set_option linter.unusedVariables false in
/-- Construct the ordinary scalar restrictions, normalized coefficient cones, and
sectionwise direct-image squares, before any right derivation.

Source: blueprint latest, `sk-prop-diagonal-tower-trace.proof.md`, paragraph (1),
coefficient restriction and the ordinary squares in
`lem-sfb-diagonal-trace-scalar-comparisons`.
(blueprint: lem-sfb-diagonal-trace-ordinary-scalars).

Proof: at level n, restrict the action along Z_l → Z_l/l^(n+1) → O_E/l^(n+1).
The underlying groups, vertical restrictions, horizontal transitions and module
maps stay unchanged. Kernels are sectionwise and cokernels are obtained by
abelian sheafification, so restriction is additive and exact. For E=ULift Q_l,
the second finite-ring map is an isomorphism: transport the usual identification
of the integers of Q_l with Z_l along ULift, then pass to the quotient. Its
constant-sheaf image identifies the restricted coefficient unit with the finite
ring tower, preserving one. Scalar extension of the root module along this ring
isomorphism identifies the line with the original root tower; the tensor unit
sends x tensor one to x, followed by c.rootForget. The actual completed ring
and root-limit projections therefore give the two coefficient cones and their
stated component equations. Direct image on a pro-etale chart evaluates on its
pullback chart. The normalized component coordinates of g identify its varying
push with this evaluation; scalar restriction retains those sections, giving the
varying square. For completed coefficients the structure map is the limit of the
same finite constant-section maps. Its composition with constant Z_l agrees
with the constant action on the pulled-back chart, by each limit projection.
This gives the completed square. Both component maps are the identity on these
section carriers. These constructions also apply to empty sites, the identity
morphism and the first positive quotient. No derived comparison is asserted.
-/
theorem exists_diagonalTraceOrdinaryScalars (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (f : X ⟶ S) (b : SpTowerShriek.Base l (ULift.{u} (Padic l)))
    (g : SpTowerShriek.Geometry l (ULift.{u} (Padic l)) b f)
    (cS : Chern l (ULift.{u} (Padic l)) S)
    (cX : Chern l (ULift.{u} (Padic l)) X)
    (nS : cS.Normalized l (ULift.{u} (Padic l)))
    (nX : cX.Normalized l (ULift.{u} (Padic l)))
    :
    let E := ULift.{u} (Padic l)
    ∃ (rS : Restriction l E S) (rX : Restriction l E X),
      letI : rS.F.Additive := rS.additive
      letI : rX.F.Additive := rX.additive
      letI : PreservesFiniteLimits rS.F := rS.limits
      letI : PreservesFiniteColimits rS.F := rS.colimits
      letI : PreservesFiniteLimits rX.F := rX.limits
      letI : PreservesFiniteColimits rX.F := rX.colimits
      Nonempty (Coefficients l E S cS rS) ∧
      Nonempty (Coefficients l E X cX rX) ∧
      ∃ varyingOrdinary : g.push ⋙ rS.F ≅ rX.F ⋙ diagonalTraceSystemPush l f,
      ∃ varying_sections : ∀ (M : Systems X (Arings l E X)) (n : ℕ) (U : S.ProEtᵒᵖ)
          (x : (((g.push ⋙ rS.F).obj M).obj (op n)).obj.obj U),
        HEq (((varyingOrdinary.hom.app M).app (op n)).hom.app U x) x,
      ∃ completedOrdinary : diagonalTracePush l f ⋙ diagonalCompletedRestriction l S ≅
        diagonalCompletedRestriction l X ⋙
          lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f,
      ∀ (M : DiagonalCompleted l X) (U : S.ProEtᵒᵖ)
          (x : ((diagonalTracePush l f ⋙ diagonalCompletedRestriction l S).obj M).obj.obj U),
        HEq ((completedOrdinary.hom.app M).hom.app U x) x := by
  obtain ⟨rS, aS⟩ := exists_diagonalTraceCoefficientRestriction l S cS nS
  obtain ⟨rX, aX⟩ := exists_diagonalTraceCoefficientRestriction l X cX nX
  exact ⟨rS, rX, aS, aX, diagonalTraceVaryingScalarSquare l f b g rS rX,
    diagonalTraceVaryingScalarSquare_hom_app_app_hom_app l f b g rS rX,
    diagonalTraceCompletedScalarSquare l f,
    diagonalTraceCompletedScalarSquare_hom_app_hom_app l f⟩

end AlgebraicGeometry.ProEtale.DiagonalTrace
