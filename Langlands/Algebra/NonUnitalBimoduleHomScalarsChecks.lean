import Langlands.Algebra.NonUnitalBimoduleHomScalarsComplex

set_option autoImplicit false
-- The types of complete polymorphic interfaces intentionally take maxima.
set_option linter.checkUnivs false

noncomputable section

open MulOpposite

namespace Langlands.Algebra.NonUnitalBimoduleHomScalars

universe uK uR uS uX uZ

private abbrev SourceActionInterface :=
  (k : Type uK) → {R : Type uR} → {S : Type uS} → {X : Type uX} → {Z : Type uZ} →
  [CommRing k] → [NonUnitalRing R] → [NonUnitalRing S] →
  [Module k R] → [IsScalarTower k R R] → [SMulCommClass k R R] → [Module k S] →
  [AddCommGroup X] → [AddCommGroup Z] →
  [NonUnitalModule R X] → [NonUnitalModule Sᵐᵒᵖ X] → [NonUnitalModule R Z] →
  (hR : IsIdempotented R) → (hX : ActionsCommute R S X) →
  (hRZ : IsNondegenerate R Z) → (hRX : IsNondegenerate R X) →
  SourceCompatible k hR hRX (S := S) →
  letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
  S →ₙₐ[k] Module.End k (NonUnitalModuleHom R X Z)

example : SourceActionInterface.{uK,uR,uS,uX,uZ} := @sourceActionHom.{uK,uR,uS,uX,uZ}
example : SourceActionInterface.{0,1,2,3,4} := @sourceActionHom.{0,1,2,3,4}
example : SourceActionInterface.{4,3,2,1,0} := @sourceActionHom.{4,3,2,1,0}

private abbrev RightSourceActionInterface :=
  (k : Type uK) → {R : Type uR} → {S : Type uS} → {Y : Type uX} → {Z : Type uZ} →
  [CommRing k] → [NonUnitalRing R] → [NonUnitalRing S] →
  [Module k R] → [Module k S] → [IsScalarTower k S S] → [SMulCommClass k S S] →
  [AddCommGroup Y] → [AddCommGroup Z] →
  [NonUnitalModule R Y] → [NonUnitalModule Sᵐᵒᵖ Y] → [NonUnitalModule Sᵐᵒᵖ Z] →
  (hS : IsIdempotented S) → (hY : ActionsCommute R S Y) →
  (hSZ : IsNondegenerate Sᵐᵒᵖ Z) → (hSY : IsNondegenerate Sᵐᵒᵖ Y) →
  RightSourceCompatible k hS hSY (R := R) →
  letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
  Rᵐᵒᵖ →ₙₐ[k] Module.End k (NonUnitalModuleHom Sᵐᵒᵖ Y Z)

example : RightSourceActionInterface.{uK,uR,uS,uX,uZ} :=
  @rightSourceActionHom.{uK,uR,uS,uX,uZ}
example : RightSourceActionInterface.{0,1,2,3,4} := @rightSourceActionHom.{0,1,2,3,4}
example : RightSourceActionInterface.{4,3,2,1,0} := @rightSourceActionHom.{4,3,2,1,0}

private abbrev SourcePartInclusionInterface :=
  (k : Type uK) → {R : Type uR} → {S : Type uS} → {X : Type uX} → {Z : Type uZ} →
  [CommRing k] → [NonUnitalRing R] → [NonUnitalRing S] →
  [Module k R] → [IsScalarTower k R R] → [SMulCommClass k R R] →
  [AddCommGroup X] → [AddCommGroup Z] →
  [NonUnitalModule R X] → [NonUnitalModule Sᵐᵒᵖ X] → [NonUnitalModule R Z] →
  (hR : IsIdempotented R) → (hS : IsIdempotented S) →
  (hX : ActionsCommute R S X) → (hRZ : IsNondegenerate R Z) →
  letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
  letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
  letI := sourcePartModule k hR hS hX hRZ
  nondegeneratePart hS (NonUnitalModuleHom R X Z) →ₗ[k] NonUnitalModuleHom R X Z

example : SourcePartInclusionInterface.{uK,uR,uS,uX,uZ} := @sourcePartInclusion.{uK,uR,uS,uX,uZ}
example : SourcePartInclusionInterface.{0,1,2,3,4} := @sourcePartInclusion.{0,1,2,3,4}
example : SourcePartInclusionInterface.{4,3,2,1,0} := @sourcePartInclusion.{4,3,2,1,0}

private abbrev SourcePartActionInterface :=
  (k : Type uK) → {R : Type uR} → {S : Type uS} → {X : Type uX} → {Z : Type uZ} →
  [CommRing k] → [NonUnitalRing R] → [NonUnitalRing S] →
  [Module k R] → [IsScalarTower k R R] → [SMulCommClass k R R] →
  [AddCommGroup X] → [AddCommGroup Z] →
  [NonUnitalModule R X] → [NonUnitalModule Sᵐᵒᵖ X] → [NonUnitalModule R Z] →
  (hR : IsIdempotented R) → (hS : IsIdempotented S) →
  (hX : ActionsCommute R S X) → (hRZ : IsNondegenerate R Z) →
  [Module k S] → (hRX : IsNondegenerate R X) → SourceCompatible k hR hRX (S := S) →
  letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
  letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
  letI := sourcePartModule k hR hS hX hRZ
  S →ₙₐ[k] Module.End k (nondegeneratePart hS (NonUnitalModuleHom R X Z))

example : SourcePartActionInterface.{uK,uR,uS,uX,uZ} := @sourcePartActionHom.{uK,uR,uS,uX,uZ}
example : SourcePartActionInterface.{0,1,2,3,4} := @sourcePartActionHom.{0,1,2,3,4}
example : SourcePartActionInterface.{4,3,2,1,0} := @sourcePartActionHom.{4,3,2,1,0}

private abbrev SourcePartModuleEqualityInterface :=
  (k : Type uK) → {R : Type uR} → {S : Type uS} → {X : Type uX} → {Z : Type uZ} →
  [CommRing k] → [NonUnitalRing R] → [NonUnitalRing S] →
  [Module k R] → [IsScalarTower k R R] → [SMulCommClass k R R] →
  [AddCommGroup X] → [AddCommGroup Z] →
  [NonUnitalModule R X] → [NonUnitalModule Sᵐᵒᵖ X] → [NonUnitalModule R Z] →
  (hR : IsIdempotented R) → (hS : IsIdempotented S) →
  (hX : ActionsCommute R S X) → (hRZ : IsNondegenerate R Z) →
  [Module k S] → [IsScalarTower k S S] → [SMulCommClass k S S] →
  (hRX : IsNondegenerate R X) → SourceCompatible k hR hRX (S := S) →
  letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
  letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
  NondegenerateScalars.module k hS
      (nondegeneratePart_isNondegenerate (M := NonUnitalModuleHom R X Z) hS) =
    sourcePartModule k hR hS hX hRZ

example : SourcePartModuleEqualityInterface.{uK,uR,uS,uX,uZ} := @sourcePartRecoveredModule_eq.{uK,uR,uS,uX,uZ}
example : SourcePartModuleEqualityInterface.{0,1,2,3,4} := @sourcePartRecoveredModule_eq.{0,1,2,3,4}
example : SourcePartModuleEqualityInterface.{4,3,2,1,0} := @sourcePartRecoveredModule_eq.{4,3,2,1,0}

private abbrev RightSourcePartInclusionInterface :=
  (k : Type uK) → {R : Type uR} → {S : Type uS} → {Y : Type uX} → {Z : Type uZ} →
  [CommRing k] → [NonUnitalRing R] → [NonUnitalRing S] →
  [Module k S] → [IsScalarTower k S S] → [SMulCommClass k S S] →
  [AddCommGroup Y] → [AddCommGroup Z] →
  [NonUnitalModule R Y] → [NonUnitalModule Sᵐᵒᵖ Y] → [NonUnitalModule Sᵐᵒᵖ Z] →
  (hR : IsIdempotented R) → (hS : IsIdempotented S) →
  (hY : ActionsCommute R S Y) → (hSZ : IsNondegenerate Sᵐᵒᵖ Z) →
  letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
  letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
  letI := rightSourcePartModule k hR hS hY hSZ
  nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z) →ₗ[k] NonUnitalModuleHom Sᵐᵒᵖ Y Z

example : RightSourcePartInclusionInterface.{uK,uR,uS,uX,uZ} := @rightSourcePartInclusion.{uK,uR,uS,uX,uZ}
example : RightSourcePartInclusionInterface.{0,1,2,3,4} := @rightSourcePartInclusion.{0,1,2,3,4}
example : RightSourcePartInclusionInterface.{4,3,2,1,0} := @rightSourcePartInclusion.{4,3,2,1,0}

private abbrev RightSourcePartActionInterface :=
  (k : Type uK) → {R : Type uR} → {S : Type uS} → {Y : Type uX} → {Z : Type uZ} →
  [CommRing k] → [NonUnitalRing R] → [NonUnitalRing S] →
  [Module k S] → [IsScalarTower k S S] → [SMulCommClass k S S] →
  [AddCommGroup Y] → [AddCommGroup Z] →
  [NonUnitalModule R Y] → [NonUnitalModule Sᵐᵒᵖ Y] → [NonUnitalModule Sᵐᵒᵖ Z] →
  (hR : IsIdempotented R) → (hS : IsIdempotented S) →
  (hY : ActionsCommute R S Y) → (hSZ : IsNondegenerate Sᵐᵒᵖ Z) →
  [Module k R] → (hSY : IsNondegenerate Sᵐᵒᵖ Y) → RightSourceCompatible k hS hSY (R := R) →
  letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
  letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
  letI := rightSourcePartModule k hR hS hY hSZ
  Rᵐᵒᵖ →ₙₐ[k] Module.End k (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z))

example : RightSourcePartActionInterface.{uK,uR,uS,uX,uZ} := @rightSourcePartActionHom.{uK,uR,uS,uX,uZ}
example : RightSourcePartActionInterface.{0,1,2,3,4} := @rightSourcePartActionHom.{0,1,2,3,4}
example : RightSourcePartActionInterface.{4,3,2,1,0} := @rightSourcePartActionHom.{4,3,2,1,0}

private abbrev RightSourcePartModuleEqualityInterface :=
  (k : Type uK) → {R : Type uR} → {S : Type uS} → {Y : Type uX} → {Z : Type uZ} →
  [CommRing k] → [NonUnitalRing R] → [NonUnitalRing S] →
  [Module k S] → [IsScalarTower k S S] → [SMulCommClass k S S] →
  [AddCommGroup Y] → [AddCommGroup Z] →
  [NonUnitalModule R Y] → [NonUnitalModule Sᵐᵒᵖ Y] → [NonUnitalModule Sᵐᵒᵖ Z] →
  (hR : IsIdempotented R) → (hS : IsIdempotented S) →
  (hY : ActionsCommute R S Y) → (hSZ : IsNondegenerate Sᵐᵒᵖ Z) →
  [Module k R] → [IsScalarTower k R R] → [SMulCommClass k R R] →
  (hSY : IsNondegenerate Sᵐᵒᵖ Y) → RightSourceCompatible k hS hSY (R := R) →
  letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
  letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
  NondegenerateScalars.module k hR.op
      (nondegeneratePart_isNondegenerate (M := NonUnitalModuleHom Sᵐᵒᵖ Y Z) hR.op) =
    rightSourcePartModule k hR hS hY hSZ

example : RightSourcePartModuleEqualityInterface.{uK,uR,uS,uX,uZ} := @rightSourcePartRecoveredModule_eq.{uK,uR,uS,uX,uZ}
example : RightSourcePartModuleEqualityInterface.{0,1,2,3,4} := @rightSourcePartRecoveredModule_eq.{0,1,2,3,4}
example : RightSourcePartModuleEqualityInterface.{4,3,2,1,0} := @rightSourcePartRecoveredModule_eq.{4,3,2,1,0}

section CompetingLeft

variable (k : Type uK) {R : Type uR} {S : Type uS} {X : Type uX} {Z : Type uZ}
  [CommRing k] [NonUnitalRing R] [NonUnitalRing S]
  [Module k R] [IsScalarTower k R R] [SMulCommClass k R R] [Module k S]
  [AddCommGroup X] [AddCommGroup Z]
  [NonUnitalModule R X] [NonUnitalModule Sᵐᵒᵖ X] [NonUnitalModule R Z]
  (hR : IsIdempotented R) (hX : ActionsCommute R S X)
  (hRZ : IsNondegenerate R Z) (hRX : IsNondegenerate R X)
  [otherX : Module k X] [otherZ : Module k Z]
  [otherHom : Module k (NonUnitalModuleHom R X Z)]

example (hc : letI := NondegenerateScalars.module k hR hRX; IsScalarTower k Sᵐᵒᵖ X) :
    letI := NondegenerateScalars.module k hR hRX
    letI := NondegenerateScalars.module k hR hRZ
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    S →ₙₐ[k] Module.End k (NonUnitalModuleHom R X Z) :=
  sourceActionHom k hR hX hRZ hRX hc

example (hS : IsIdempotented S) :
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    [_otherPart : Module k (nondegeneratePart hS (NonUnitalModuleHom R X Z))] →
    letI := NondegenerateScalars.module k hR hRX
    letI := NondegenerateScalars.module k hR hRZ
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := sourcePartModule k hR hS hX hRZ
    nondegeneratePart hS (NonUnitalModuleHom R X Z) →ₗ[k] NonUnitalModuleHom R X Z := by
  intro _otherPart
  exact sourcePartInclusion k hR hS hX hRZ

example (hS : IsIdempotented S)
    (hc : letI := NondegenerateScalars.module k hR hRX; IsScalarTower k Sᵐᵒᵖ X) :
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    [_otherPart : Module k (nondegeneratePart hS (NonUnitalModuleHom R X Z))] →
    letI := NondegenerateScalars.module k hR hRX
    letI := NondegenerateScalars.module k hR hRZ
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := sourcePartModule k hR hS hX hRZ
    S →ₙₐ[k] Module.End k (nondegeneratePart hS (NonUnitalModuleHom R X Z)) := by
  intro _otherPart
  exact sourcePartActionHom k hR hS hX hRZ hRX hc

example [IsScalarTower k S S] [SMulCommClass k S S] (hS : IsIdempotented S)
    (hc : letI := NondegenerateScalars.module k hR hRX; IsScalarTower k Sᵐᵒᵖ X) :
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    [_otherPart : Module k (nondegeneratePart hS (NonUnitalModuleHom R X Z))] →
    letI := NondegenerateScalars.module k hR hRX
    letI := NondegenerateScalars.module k hR hRZ
    letI := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
    letI := sourcePartModule k hR hS hX hRZ
    NondegenerateScalars.module k hS
        (nondegeneratePart_isNondegenerate (M := NonUnitalModuleHom R X Z) hS) =
      sourcePartModule k hR hS hX hRZ := by
  intro _otherPart
  exact sourcePartRecoveredModule_eq k hR hS hX hRZ hRX hc

example (hc : SourceCompatible k hR hRX (S := S)) (s : S) :
    sourceActionHom k hR hX hRZ hRX hc s 0 = 0 := map_zero _

example [Subsingleton Z] (hc : SourceCompatible k hR hRX (S := S))
    (s : S) (f : NonUnitalModuleHom R X Z) :
    sourceActionHom k hR hX hRZ hRX hc s f = 0 := by
  ext x
  exact Subsingleton.elim _ _

example [Subsingleton Z] (hS : IsIdempotented S)
    (hc : SourceCompatible k hR hRX (S := S)) (s : S) :
    letI := NonUnitalBimoduleHomActions.sourceAction (Z := Z) hX
    ∀ f : nondegeneratePart hS (NonUnitalModuleHom R X Z),
      sourcePartActionHom k hR hS hX hRZ hRX hc s f = 0 := by
  intro f
  apply Subtype.ext
  ext x
  exact Subsingleton.elim _ _

example [Subsingleton k] (hc : SourceCompatible k hR hRX (S := S))
    (s : S) (f : NonUnitalModuleHom R X Z) :
    sourceActionHom k hR hX hRZ hRX hc s f = 0 := by
  let := NondegenerateModuleHomScalars.homModule k hR hRZ (M := X)
  let := Module.subsingleton k (NonUnitalModuleHom R X Z)
  exact Subsingleton.elim _ _

end CompetingLeft

section CompetingRight

variable (k : Type uK) {R : Type uR} {S : Type uS} {Y : Type uX} {Z : Type uZ}
  [CommRing k] [NonUnitalRing R] [NonUnitalRing S]
  [Module k R] [Module k S] [IsScalarTower k S S] [SMulCommClass k S S]
  [AddCommGroup Y] [AddCommGroup Z]
  [NonUnitalModule R Y] [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule Sᵐᵒᵖ Z]
  (hS : IsIdempotented S) (hY : ActionsCommute R S Y)
  (hSZ : IsNondegenerate Sᵐᵒᵖ Z) (hSY : IsNondegenerate Sᵐᵒᵖ Y)
  [otherY : Module k Y] [otherZ : Module k Z]
  [otherHom : Module k (NonUnitalModuleHom Sᵐᵒᵖ Y Z)]

example (hc : letI := NondegenerateScalars.module k hS.op hSY; IsScalarTower k R Y) :
    letI := NondegenerateScalars.module k hS.op hSY
    letI := NondegenerateScalars.module k hS.op hSZ
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    Rᵐᵒᵖ →ₙₐ[k] Module.End k (NonUnitalModuleHom Sᵐᵒᵖ Y Z) :=
  rightSourceActionHom k hS hY hSZ hSY hc

example (hR : IsIdempotented R) :
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    [_otherPart : Module k (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z))] →
    letI := NondegenerateScalars.module k hS.op hSY
    letI := NondegenerateScalars.module k hS.op hSZ
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := rightSourcePartModule k hR hS hY hSZ
    nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z) →ₗ[k] NonUnitalModuleHom Sᵐᵒᵖ Y Z := by
  intro _otherPart
  exact rightSourcePartInclusion k hR hS hY hSZ

example (hR : IsIdempotented R)
    (hc : letI := NondegenerateScalars.module k hS.op hSY; IsScalarTower k R Y) :
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    [_otherPart : Module k (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z))] →
    letI := NondegenerateScalars.module k hS.op hSY
    letI := NondegenerateScalars.module k hS.op hSZ
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := rightSourcePartModule k hR hS hY hSZ
    Rᵐᵒᵖ →ₙₐ[k] Module.End k (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z)) := by
  intro _otherPart
  exact rightSourcePartActionHom k hR hS hY hSZ hSY hc

example [IsScalarTower k R R] [SMulCommClass k R R] (hR : IsIdempotented R)
    (hc : letI := NondegenerateScalars.module k hS.op hSY; IsScalarTower k R Y) :
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    [_otherPart : Module k (nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z))] →
    letI := NondegenerateScalars.module k hS.op hSY
    letI := NondegenerateScalars.module k hS.op hSZ
    letI := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
    letI := rightSourcePartModule k hR hS hY hSZ
    NondegenerateScalars.module k hR.op
        (nondegeneratePart_isNondegenerate (M := NonUnitalModuleHom Sᵐᵒᵖ Y Z) hR.op) =
      rightSourcePartModule k hR hS hY hSZ := by
  intro _otherPart
  exact rightSourcePartRecoveredModule_eq k hR hS hY hSZ hSY hc

example (hc : RightSourceCompatible k hS hSY (R := R)) (r : R) :
    rightSourceActionHom k hS hY hSZ hSY hc (op r) 0 = 0 := map_zero _

example [Subsingleton Z] (hc : RightSourceCompatible k hS hSY (R := R))
    (r : R) (f : NonUnitalModuleHom Sᵐᵒᵖ Y Z) :
    rightSourceActionHom k hS hY hSZ hSY hc (op r) f = 0 := by
  ext x
  exact Subsingleton.elim _ _

example [Subsingleton Z] (hR : IsIdempotented R)
    (hc : RightSourceCompatible k hS hSY (R := R)) (r : R) :
    letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := Z) hY
    ∀ f : nondegeneratePart hR.op (NonUnitalModuleHom Sᵐᵒᵖ Y Z),
      rightSourcePartActionHom k hR hS hY hSZ hSY hc (op r) f = 0 := by
  intro f
  apply Subtype.ext
  ext x
  exact Subsingleton.elim _ _

example [Subsingleton k] (hc : RightSourceCompatible k hS hSY (R := R))
    (r : R) (f : NonUnitalModuleHom Sᵐᵒᵖ Y Z) :
    rightSourceActionHom k hS hY hSZ hSY hc (op r) f = 0 := by
  let := NondegenerateModuleHomScalars.homModule k hS.op hSZ (M := Y)
  let := Module.subsingleton k (NonUnitalModuleHom Sᵐᵒᵖ Y Z)
  exact Subsingleton.elim _ _

end CompetingRight

section IntegerRegular

local instance : NonUnitalModule ℤ ℤ := NonUnitalModule.regular ℤ
local instance : NonUnitalModule ℤᵐᵒᵖ ℤ := NonUnitalModule.rightRegular ℤ

private theorem intRegularNondegenerate : IsNondegenerate ℤ ℤ :=
  fun m => ⟨⟨1, IsIdempotentElem.one⟩, one_mul m⟩

private theorem intRegularSourceCompatible :
    SourceCompatible ℤ (IsIdempotented.of_ring ℤ) intRegularNondegenerate (S := ℤ) := by
  have hm : NondegenerateScalars.module ℤ (IsIdempotented.of_ring ℤ)
      intRegularNondegenerate = (inferInstance : Module ℤ ℤ) := Subsingleton.elim _ _
  unfold SourceCompatible
  rw [hm]
  refine ⟨fun c s x => ?_⟩
  change x * (c * s.unop) = c * (x * s.unop)
  ring

example (a b : ℤ) :
    sourceActionHom ℤ (IsIdempotented.of_ring ℤ) (NonUnitalModule.regular_actionsCommute ℤ)
      intRegularNondegenerate intRegularNondegenerate intRegularSourceCompatible a
      (NonUnitalModuleHom.id ℤ ℤ) b = b * a := rfl

example : (NonUnitalModuleHom.id ℤ ℤ : NonUnitalModuleHom ℤ ℤ ℤ) ≠ 0 := by
  intro h
  exact one_ne_zero (congrArg (fun f : NonUnitalModuleHom ℤ ℤ ℤ => f 1) h)

local instance : NonUnitalModule ℤ (NonUnitalModuleHom ℤ ℤ ℤ) :=
  NonUnitalBimoduleHomActions.sourceAction (NonUnitalModule.regular_actionsCommute ℤ)

private def intIdentityPart :
    nondegeneratePart (IsIdempotented.of_ring ℤ) (NonUnitalModuleHom ℤ ℤ ℤ) :=
  ⟨NonUnitalModuleHom.id ℤ ℤ, ⟨⟨1, IsIdempotentElem.one⟩, by
    ext b
    exact mul_one b⟩⟩

example : intIdentityPart ≠ 0 := by
  intro h
  exact one_ne_zero (congrArg (fun f :
    nondegeneratePart (IsIdempotented.of_ring ℤ) (NonUnitalModuleHom ℤ ℤ ℤ) => f.val 1) h)

example (c : ℤ) :
    letI := NondegenerateModuleHomScalars.homModule ℤ (IsIdempotented.of_ring ℤ)
      intRegularNondegenerate (M := ℤ)
    letI := sourcePartModule ℤ (IsIdempotented.of_ring ℤ) (IsIdempotented.of_ring ℤ)
      (NonUnitalModule.regular_actionsCommute ℤ) intRegularNondegenerate
    ∀ (f : nondegeneratePart (IsIdempotented.of_ring ℤ) (NonUnitalModuleHom ℤ ℤ ℤ)) (b : ℤ),
      (@SMul.smul ℤ (nondegeneratePart (IsIdempotented.of_ring ℤ)
        (NonUnitalModuleHom ℤ ℤ ℤ))
        (sourcePartModule ℤ (IsIdempotented.of_ring ℤ) (IsIdempotented.of_ring ℤ)
          (NonUnitalModule.regular_actionsCommute ℤ) intRegularNondegenerate).toSMul c f).val b =
        c * f.val b := by
  let := NondegenerateModuleHomScalars.homModule ℤ (IsIdempotented.of_ring ℤ)
    intRegularNondegenerate (M := ℤ)
  let := sourcePartModule ℤ (IsIdempotented.of_ring ℤ) (IsIdempotented.of_ring ℤ)
    (NonUnitalModule.regular_actionsCommute ℤ) intRegularNondegenerate
  intro f b
  change NondegenerateScalars.scalarMul ℤ intRegularNondegenerate c (f.val b) = c * f.val b
  rw [NondegenerateScalars.scalarMul_eq ℤ (IsIdempotented.of_ring ℤ)
    intRegularNondegenerate c (f.val b) ⟨1, IsIdempotentElem.one⟩ (one_mul _)]
  change (c * 1) * f.val b = c * f.val b
  rw [mul_one]

end IntegerRegular

end Langlands.Algebra.NonUnitalBimoduleHomScalars
