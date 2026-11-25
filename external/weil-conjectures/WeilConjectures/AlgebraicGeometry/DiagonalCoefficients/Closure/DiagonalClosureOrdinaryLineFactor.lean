/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientMaps

/-! # Factorization of the ordinary closure-line leg -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor MonObj
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The prescribed finite-field leg factors through ordinary scalar extension.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (2), colimit-leg
factorization.  The compatible rational root bases identify the scalar extension
of the finite line with the corresponding colimit leg.  Passing to the sheafified
coefficient colimit gives the displayed factorization; no invertibility assertion
is used here.
(blueprint: lem-diagonal-closure-ordinary-line-factor).
-/
theorem diagonalClosure_ordinaryLine_factor
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (X : Scheme.{u}) (_hX : IsUnit (l : Γ(X, ⊤))) :
    ∃ f : (Mod.extendScalars
        (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) X)).obj
          (spRationalTwist X l E) ⟶ spQbarTwist X l,
      Mod.extendUnitHom (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) X)
          (spRationalTwist X l E) ≫ f.hom = closureLineMap l E X := by
  let c := coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) X
  let M := spRationalTwist X l E
  let Q := spQbarTwist X l
  have hact : Mod.act M.X ≫ closureLineMap l E X =
      (c ⊗ₘ closureLineMap l E X) ≫ Mod.act Q.X := by
    have h := (spQbarTwistAction_existsUnique X l).exists.choose_spec E E E
      (le_refl E) (le_refl E)
    change Mod.act M.X ≫ colimit.ι (spRationalTwistDiagram X l) E =
      (c ⊗ₘ colimit.ι (spRationalTwistDiagram X l) E) ≫
        (spQbarTwistAction_existsUnique X l).exists.choose.smul
    simpa only [Profinite.padicSubfieldRingObjMap_id, coefficientMap_id,
      spRationalTwistMap_id, id_tensorHom_id, Category.id_comp] using h.symm
  let g : M ⟶ (Mod.comap c).obj Q := Mod.homMk (closureLineMap l E X) (by
    change Mod.act M.X ≫ closureLineMap l E X =
      condensedRingObj (Profinite.continuousMapRingObj E.1) X ◁
          closureLineMap l E X ≫ c ▷ Q.X ≫ Mod.act Q.X
    simpa only [tensorHom_def', Category.assoc] using hact)
  exact ⟨Mod.extendHom c g, Mod.extendUnitHom_extendHom c g⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
