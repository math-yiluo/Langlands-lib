/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientCategory

/-! # Normalized diagonal coefficient diagrams

Source: blueprint main-20261015, sk-prop-diagonal-tower-coefficients.
(blueprint: def-sfb-diagonal-coefficient-maps).

## Main definitions

- `integralMap`, `zlLine`: the actual integral coefficient map and base line.
- `integralLineMap`, `rationalLineMap`, `closureLineMap`: the prescribed line maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

variable (l : ℕ) [Fact l.Prime]

/-- The bottom finite subextension, used only to write the actual Z_l Tate line
using the published root-limit construction. Source: blueprint coefficient convention
(blueprint: def-sfb-diagonal-coefficient-maps). -/
abbrev bottomField : PadicAlgCl.FiniteIntermediateField l := ⟨⊥, inferInstance⟩

/-- The actual condensed inclusion Z_l to O_E. Source: blueprint clause 1
(blueprint: def-sfb-diagonal-coefficient-maps). -/
def integralMap (E : PadicAlgCl.FiniteIntermediateField l) :
    Profinite.continuousMapRingObj.{u} ℤ_[l] ⟶ Profinite.padicIntegersRingObj.{u} l E.1 :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.padicIntCondensedRingToPadicIntegersCondensedRing l E.1)

/-- The inclusion is a map of ring objects. Source: blueprint clause 1
(blueprint: def-sfb-diagonal-coefficient-maps). -/
instance integralMap_isMonHom (E : PadicAlgCl.FiniteIntermediateField l) :
    IsMonHom (integralMap.{u} l E) := by
  dsimp only [integralMap]
  infer_instance

/-- The base-field integral Tate line, retaining the actual root-limit module and
restricting along the specified Z_l to O_Q_l identification. Source: blueprint
coefficient convention (blueprint: def-sfb-diagonal-coefficient-maps). -/
abbrev zlLine (X : Scheme.{u}) : Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X :=
  (Mod.comap (coefficientMap (integralMap l (bottomField l)) X)).obj
    (spIntegralTwist X l (bottomField l))

/-- The root-limit map for Z_l to O_E, fixed by all root projections in the
published integral transition. Source: blueprint clause 1
(blueprint: def-sfb-diagonal-coefficient-maps). -/
def integralLineMap (E : PadicAlgCl.FiniteIntermediateField l) (X : Scheme.{u}) :
    (zlLine l X).X ⟶ (spIntegralTwist X l E).X := by
  change (spIntegralTwist X l (bottomField l)).X ⟶ (spIntegralTwist X l E).X
  exact spIntegralTwistMap X l (E := bottomField l) (F := E)
    (bot_le : (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l)) ≤ E.1)

/-- The localization map on the Tate line is the actual balanced-tensor unit.
Source: blueprint clause 2 (blueprint: def-sfb-diagonal-coefficient-maps). -/
def rationalLineMap (E : PadicAlgCl.FiniteIntermediateField l) (X : Scheme.{u}) :
    (spIntegralTwist X l E).X ⟶ (spRationalTwist X l E).X :=
  Mod.extendUnitHom (padicIntegersToPadicSubfield X l E) (spIntegralTwist X l E)

/-- The finite-field leg in the sheafified colimit Tate line. Source: blueprint
clause 2 (blueprint: def-sfb-diagonal-coefficient-maps). -/
def closureLineMap (E : PadicAlgCl.FiniteIntermediateField l) (X : Scheme.{u}) :
    (spRationalTwist X l E).X ⟶ (spQbarTwist X l).X :=
  colimit.ι (spRationalTwistDiagram X l) E

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
