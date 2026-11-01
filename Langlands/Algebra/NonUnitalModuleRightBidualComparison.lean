import Langlands.Algebra.NonUnitalModuleDualComparison
import Langlands.Algebra.NonUnitalModuleBidualEvaluation

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleRightBidual

open CategoryTheory MulOpposite NonUnitalModuleDual NonUnitalModuleDualComparison

universe uA uM uN

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]

section Original

variable {M : Type uM} [AddCommGroup M] [NonUnitalModule Aᵐᵒᵖ M]
  (hA : IsIdempotented A) (hM : IsNondegenerate Aᵐᵒᵖ M)

/-- The raw first right dual retains its specified double-opposite action. -/
abbrev rawFirstDualAction : NonUnitalModule Aᵐᵒᵖᵐᵒᵖ (Dual hA.op hM) :=
  dualAction hA.op hM

/-- Transport the first dual to its actual left action before dualizing again. -/
abbrev firstDualAction : NonUnitalModule A (Dual hA.op hM) :=
  fromDoubleOppositeAction (A := A) (M := Dual hA.op hM)

theorem firstDual_isNondegenerate :
    letI := firstDualAction hA hM
    IsNondegenerate A (Dual hA.op hM) :=
  fromDoubleOpposite_isNondegenerate (isNondegenerate hA.op hM)

/-- The actual second dual recovers scalars after the first action is transported. -/
abbrev RightBidual :=
  letI := firstDualAction hA hM
  Dual hA (firstDual_isNondegenerate hA hM)

@[instance_reducible]
def rightBidualAction : NonUnitalModule Aᵐᵒᵖ (RightBidual hA hM) :=
  letI := firstDualAction hA hM
  dualAction hA (firstDual_isNondegenerate hA hM)

theorem rightBidual_isNondegenerate :
    letI := rightBidualAction hA hM
    IsNondegenerate Aᵐᵒᵖ (RightBidual hA hM) :=
  letI := firstDualAction hA hM
  isNondegenerate hA (firstDual_isNondegenerate hA hM)

theorem genericRightBidual_eq_raw :
    Bidual hA.op hM = Dual hA.op.op (isNondegenerate hA.op hM) := rfl

theorem genericRightBidualAction_eq_raw :
    bidualAction hA.op hM =
      fromDoubleOppositeAction (A := Aᵐᵒᵖ)
        (M := Dual hA.op.op (isNondegenerate hA.op hM)) := rfl

/-- The complete first-dual canonical scalar equality needed for the actual composite. -/
theorem firstDualCanonicalModule_eq :
    letI := firstDualAction hA hM
    NondegenerateScalars.complexModule hA (firstDual_isNondegenerate hA hM) =
      NondegenerateScalars.complexModule hA.op.op (isNondegenerate hA.op hM) :=
  transportedCanonicalModule_eq_raw hA (isNondegenerate hA.op hM)

/-- Original right comparison from the published generic opposite-ring bidual. -/
def comparisonHom :
    letI := bidualAction hA.op hM
    letI := rightBidualAction hA hM
    NonUnitalModuleHom Aᵐᵒᵖ (Bidual hA.op hM) (RightBidual hA hM) :=
  dualComparisonHom hA (isNondegenerate hA.op hM)

def comparisonInvHom :
    letI := bidualAction hA.op hM
    letI := rightBidualAction hA hM
    NonUnitalModuleHom Aᵐᵒᵖ (RightBidual hA hM) (Bidual hA.op hM) :=
  dualComparisonInvHom hA (isNondegenerate hA.op hM)

theorem comparison_inverse_left :
    letI := bidualAction hA.op hM
    letI := rightBidualAction hA hM
    (comparisonInvHom hA hM).comp (comparisonHom hA hM) =
      NonUnitalModuleHom.id Aᵐᵒᵖ (Bidual hA.op hM) :=
  dualComparison_inverse_left hA (isNondegenerate hA.op hM)

theorem comparison_inverse_right :
    letI := bidualAction hA.op hM
    letI := rightBidualAction hA hM
    (comparisonHom hA hM).comp (comparisonInvHom hA hM) =
      NonUnitalModuleHom.id Aᵐᵒᵖ (RightBidual hA hM) :=
  dualComparison_inverse_right hA (isNondegenerate hA.op hM)

theorem comparisonHom_val (Φ : Bidual hA.op hM) :
    letI := firstDualAction hA hM
    (comparisonHom hA hM Φ).val =
      fullComparison hA (isNondegenerate hA.op hM) Φ.val := rfl

theorem comparisonHom_val_coe (Φ : Bidual hA.op hM) :
    ⇑(comparisonHom hA hM Φ).val = ⇑Φ.val := rfl

theorem comparisonInvHom_val (Φ : RightBidual hA hM) :
    letI := firstDualAction hA hM
    (comparisonInvHom hA hM Φ).val =
      (fullComparison hA (isNondegenerate hA.op hM)).symm Φ.val := rfl

theorem comparisonInvHom_val_coe (Φ : RightBidual hA hM) :
    ⇑(comparisonInvHom hA hM Φ).val = ⇑Φ.val := rfl

/-- The same equivalence for exactly the recovered original right scalar modules. -/
def comparisonLinear :
    letI := bidualAction hA.op hM
    letI := rightBidualAction hA hM
    letI := NondegenerateScalars.complexModule hA.op (bidual_isNondegenerate hA.op hM)
    letI := NondegenerateScalars.complexModule hA.op (rightBidual_isNondegenerate hA hM)
    Bidual hA.op hM ≃ₗ[ℂ] RightBidual hA hM :=
  dualComparisonCanonicalLinear hA (isNondegenerate hA.op hM)

theorem comparisonLinear_toAddMonoidHom :
    letI := bidualAction hA.op hM
    letI := rightBidualAction hA hM
    letI := NondegenerateScalars.complexModule hA.op (bidual_isNondegenerate hA.op hM)
    letI := NondegenerateScalars.complexModule hA.op (rightBidual_isNondegenerate hA hM)
    (comparisonLinear hA hM).toAddMonoidHom =
      (comparisonHom hA hM).toAddMonoidHom := rfl

variable {N : Type uN} [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
  (hN : IsNondegenerate Aᵐᵒᵖ N)

/-- Actual right double pullback: transport the first pullback before the second dual. -/
def rightDoublePullback (f : NonUnitalModuleHom Aᵐᵒᵖ M N) :
    letI := rightBidualAction hA hM
    letI := rightBidualAction hA hN
    NonUnitalModuleHom Aᵐᵒᵖ (RightBidual hA hM) (RightBidual hA hN) :=
  letI := firstDualAction hA hM
  letI := firstDualAction hA hN
  pullback hA (firstDual_isNondegenerate hA hN) (firstDual_isNondegenerate hA hM)
    (fromDoubleOppositeMap (pullback hA.op hM hN f))

theorem rightDoublePullback_val (f : NonUnitalModuleHom Aᵐᵒᵖ M N)
    (Φ : RightBidual hA hM) :
    letI := firstDualAction hA hM
    letI := firstDualAction hA hN
    (rightDoublePullback hA hM hN f Φ).val =
      fullPullback hA (firstDual_isNondegenerate hA hN) (firstDual_isNondegenerate hA hM)
        (fromDoubleOppositeMap (pullback hA.op hM hN f)) Φ.val := rfl

theorem genericRightDoublePullback_eq_raw (f : NonUnitalModuleHom Aᵐᵒᵖ M N) :
    letI := bidualAction hA.op hM
    letI := bidualAction hA.op hN
    doublePullback hA.op hM hN f =
      fromDoubleOppositeMap
        (pullback hA.op.op (isNondegenerate hA.op hN) (isNondegenerate hA.op hM)
          (pullback hA.op hM hN f)) := rfl

/-- Equality of entire original right intertwiners at independent carrier universes. -/
theorem comparison_naturality (f : NonUnitalModuleHom Aᵐᵒᵖ M N) :
    letI := bidualAction hA.op hM
    letI := bidualAction hA.op hN
    letI := rightBidualAction hA hM
    letI := rightBidualAction hA hN
    (rightDoublePullback hA hM hN f).comp (comparisonHom hA hM) =
      (comparisonHom hA hN).comp (doublePullback hA.op hM hN f) :=
  (dualComparison_cross_naturality hA (isNondegenerate hA.op hN)
    (isNondegenerate hA.op hM) (pullback hA.op hM hN f)).symm

end Original

section Categorical

/-- Exactly the actual right categorical composite of the two published dual functors. -/
abbrev actualRightBidualFunctor (hA : IsIdempotented A) :
    RightNondegenerateModuleCat.{uA,uM} A ⥤ RightNondegenerateModuleCat.{uA,uM} A :=
  (rightToLeftFunctor hA).rightOp ⋙ leftToRightFunctor hA

theorem actualRightBidualFunctor_eq (hA : IsIdempotented A) :
    actualRightBidualFunctor.{uA,uM} hA =
      (rightToLeftFunctor hA).rightOp ⋙ leftToRightFunctor hA := rfl

theorem actualRightBidualFunctor_obj_carrier (hA : IsIdempotented A)
    (M : RightNondegenerateModuleCat.{uA,uM} A) :
    ((actualRightBidualFunctor hA).obj M).obj.carrier = RightBidual hA M.property := rfl

theorem actualRightBidualFunctor_obj_action (hA : IsIdempotented A)
    (M : RightNondegenerateModuleCat.{uA,uM} A) :
    ((actualRightBidualFunctor hA).obj M).obj.isModule =
      rightBidualAction hA M.property := rfl

set_option maxHeartbeats 800000 in
theorem actualRightBidualFunctor_map_hom (hA : IsIdempotented A)
    {M N : RightNondegenerateModuleCat.{uA,uM} A} (f : M ⟶ N) :
    letI := rightBidualAction hA M.property
    letI := rightBidualAction hA N.property
    ((actualRightBidualFunctor hA).map f).hom =
      rightDoublePullback hA M.property N.property f.hom := rfl

def actualComparisonHom (hA : IsIdempotented A)
    (M : RightNondegenerateModuleCat.{uA,uM} A) :
    NonUnitalModuleHom Aᵐᵒᵖ ((bidualFunctor hA.op).obj M).obj
      ((actualRightBidualFunctor hA).obj M).obj :=
  comparisonHom hA M.property

def actualComparisonInvHom (hA : IsIdempotented A)
    (M : RightNondegenerateModuleCat.{uA,uM} A) :
    NonUnitalModuleHom Aᵐᵒᵖ ((actualRightBidualFunctor hA).obj M).obj
      ((bidualFunctor hA.op).obj M).obj :=
  comparisonInvHom hA M.property

theorem actualComparisonHom_eq (hA : IsIdempotented A)
    (M : RightNondegenerateModuleCat.{uA,uM} A) :
    letI := bidualAction hA.op M.property
    letI := rightBidualAction hA M.property
    actualComparisonHom hA M = comparisonHom hA M.property := rfl

theorem actualComparisonInvHom_eq (hA : IsIdempotented A)
    (M : RightNondegenerateModuleCat.{uA,uM} A) :
    letI := bidualAction hA.op M.property
    letI := rightBidualAction hA M.property
    actualComparisonInvHom hA M = comparisonInvHom hA M.property := rfl

set_option maxHeartbeats 800000 in
theorem actualComparison_naturality (hA : IsIdempotented A)
    {M N : RightNondegenerateModuleCat.{uA,uM} A} (f : M ⟶ N) :
    (((actualRightBidualFunctor hA).map f).hom).comp (actualComparisonHom hA M) =
      (actualComparisonHom hA N).comp (((bidualFunctor hA.op).map f).hom) :=
  comparison_naturality hA M.property N.property f.hom

set_option maxHeartbeats 800000 in
/-- Natural isomorphism from the published generic bidual to the actual right composite. -/
def comparisonNatIso (hA : IsIdempotented A) :
    bidualFunctor.{uA,uM} hA.op ≅ actualRightBidualFunctor hA :=
  NatIso.ofComponents (fun M =>
    { hom := ObjectProperty.homMk (actualComparisonHom hA M)
      inv := ObjectProperty.homMk (actualComparisonInvHom hA M)
      hom_inv_id := by
        apply ObjectProperty.hom_ext
        exact comparison_inverse_left hA M.property
      inv_hom_id := by
        apply ObjectProperty.hom_ext
        exact comparison_inverse_right hA M.property })
    (fun f => by
      apply ObjectProperty.hom_ext
      exact (actualComparison_naturality hA f).symm)

theorem comparisonNatIso_hom_app_hom (hA : IsIdempotented A)
    (M : RightNondegenerateModuleCat.{uA,uM} A) :
    ((comparisonNatIso hA).hom.app M).hom = actualComparisonHom hA M := rfl

theorem comparisonNatIso_inv_app_hom (hA : IsIdempotented A)
    (M : RightNondegenerateModuleCat.{uA,uM} A) :
    ((comparisonNatIso hA).inv.app M).hom = actualComparisonInvHom hA M := rfl

theorem comparisonNatIso_hom_app_val_coe (hA : IsIdempotented A)
    (M : RightNondegenerateModuleCat.{uA,uM} A)
    (Φ : ((bidualFunctor hA.op).obj M).obj) :
    ⇑(NonUnitalModuleHom.toAddMonoidHom ((comparisonNatIso hA).hom.app M).hom Φ).val =
      ⇑Φ.val := rfl

theorem comparisonNatIso_inv_app_val_coe (hA : IsIdempotented A)
    (M : RightNondegenerateModuleCat.{uA,uM} A)
    (Φ : ((actualRightBidualFunctor hA).obj M).obj) :
    ⇑(NonUnitalModuleHom.toAddMonoidHom ((comparisonNatIso hA).inv.app M).hom Φ).val =
      ⇑Φ.val := rfl

end Categorical

end Langlands.Algebra.NonUnitalModuleRightBidual
