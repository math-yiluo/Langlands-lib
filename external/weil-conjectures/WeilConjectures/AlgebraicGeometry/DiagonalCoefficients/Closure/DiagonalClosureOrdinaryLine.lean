/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientMaps
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Closure.DiagonalClosureOrdinaryLineFactorIso

/-! # Ordinary scalar extension of the rational root line to the closure -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The ordinary closure line is the scalar extension of the rational line, with
its actual colimit leg as the composite of the extension unit and the comparison.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (2); and
sec-proetale-coefficients/sk-def-sp-tate-twist/_section.md, compatible root bases.
(blueprint: lem-diagonal-closure-ordinary-line).

Proof: choose the pro-etale cover with compatible generators of all ell-power
roots of unity. On each slice the normalized rational root bases identify the
finite coefficient diagram with the rational-line diagram, compatibly with every
field inclusion. Their colimit identifies the closure line with the closure
coefficient unit. Under these identifications the map from the E-line is exactly
the coefficient inclusion, since both maps are the E-th colimit leg. Ordinary
extension of the regular E-module is the regular closure module by multiplication.
Consequently the adjoint of the root-line leg is an isomorphism on each slice.
The slice tensor comparisons identify it with the restriction of the global
adjoint. The covering is jointly conservative, so the global adjoint is an
isomorphism. Take that adjoint as the comparison: the scalar adjunction unit
identity is the displayed equation. This works also for the bottom field and
empty schemes; it uses no direct image or derived category. -/
theorem diagonalClosure_ordinaryLine
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (X : Scheme.{u}) (hX : IsUnit (l : Γ(X, ⊤))) :
    ∃ q : (Mod.extendScalars
        (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) X)).obj
          (spRationalTwist X l E) ≅ spQbarTwist X l,
      Mod.extendUnitHom (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) X)
          (spRationalTwist X l E) ≫ q.hom.hom = closureLineMap l E X := by
  obtain ⟨f, hf⟩ := diagonalClosure_ordinaryLine_factor l E X hX
  haveI : IsIso f := diagonalClosure_ordinaryLine_factor_isIso l E X hX f hf
  exact ⟨asIso f, hf⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
