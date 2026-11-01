import Langlands.Algebra.NonUnitalModuleDualComparison

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleDualComparison

open MulOpposite NonUnitalModuleDual

universe uA uM uN

/-! Assign complete unapplied declarations to independently specified interfaces. -/

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ M) →
    letI := fromDoubleOppositeAction (A := A) (M := M)
    Dual hA.op.op hM ≃+ Dual hA (fromDoubleOpposite_isNondegenerate hM) :=
  @dualComparison.{uA,uM}

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ M) →
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hM)
    NonUnitalModuleHom Aᵐᵒᵖ (Dual hA.op.op hM)
      (Dual hA (fromDoubleOpposite_isNondegenerate hM)) :=
  @dualComparisonHom.{uA,uM}

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ M) →
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hM)
    NonUnitalModuleHom Aᵐᵒᵖ (Dual hA (fromDoubleOpposite_isNondegenerate hM))
      (Dual hA.op.op hM) :=
  @dualComparisonInvHom.{uA,uM}

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ M) →
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := dualModule hA.op.op hM
    letI := dualModule hA (fromDoubleOpposite_isNondegenerate hM)
    Dual hA.op.op hM ≃ₗ[ℂ] Dual hA (fromDoubleOpposite_isNondegenerate hM) :=
  @dualComparisonLinear.{uA,uM}

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ M) →
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := comparisonSourceModule hA hM
    letI := comparisonTargetModule hA hM
    Dual hA.op.op hM ≃ₗ[ℂ] Dual hA (fromDoubleOpposite_isNondegenerate hM) :=
  @dualComparisonCanonicalLinear.{uA,uM}

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖᵐᵒᵖ M] →
    {N : Type uN} → [AddCommGroup N] → [NonUnitalModule Aᵐᵒᵖᵐᵒᵖ N] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ M) →
    (hN : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ N) →
    (f : NonUnitalModuleHom Aᵐᵒᵖᵐᵒᵖ M N) →
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fromDoubleOppositeAction (A := A) (M := N)
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hM)
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hN)
    (dualComparisonHom hA hM).comp
        (fromDoubleOppositeMap (pullback hA.op.op hM hN f)) =
      (pullback hA (fromDoubleOpposite_isNondegenerate hM)
        (fromDoubleOpposite_isNondegenerate hN) (fromDoubleOppositeMap f)).comp
          (dualComparisonHom hA hN) :=
  @dualComparison_cross_naturality.{uA,uM,uN}

/-! Both strict algebra/carrier universe directions, with entire interfaces. -/

example :
    {A : Type} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ M) →
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := comparisonSourceModule hA hM
    letI := comparisonTargetModule hA hM
    Dual hA.op.op hM ≃ₗ[ℂ] Dual hA (fromDoubleOpposite_isNondegenerate hM) :=
  @dualComparisonCanonicalLinear.{0,1}

example :
    {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ M) →
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := comparisonSourceModule hA hM
    letI := comparisonTargetModule hA hM
    Dual hA.op.op hM ≃ₗ[ℂ] Dual hA (fromDoubleOpposite_isNondegenerate hM) :=
  @dualComparisonCanonicalLinear.{1,0}

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖᵐᵒᵖ M] →
    {N : Type uN} → [AddCommGroup N] → [NonUnitalModule Aᵐᵒᵖᵐᵒᵖ N] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ M) →
    (hN : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ N) →
    (f : NonUnitalModuleHom Aᵐᵒᵖᵐᵒᵖ M N) →
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fromDoubleOppositeAction (A := A) (M := N)
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hM)
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hN)
    letI := comparisonSourceModule hA hM
    letI := comparisonSourceModule hA hN
    letI := comparisonTargetModule hA hM
    letI := comparisonTargetModule hA hN
    (dualComparisonCanonicalLinear hA hM).toLinearMap.comp
        (NondegenerateScalars.complexToLinearMap hA.op
          (fromDoubleOpposite_isNondegenerate (isNondegenerate hA.op.op hN))
          (fromDoubleOpposite_isNondegenerate (isNondegenerate hA.op.op hM))
          (fromDoubleOppositeMap (pullback hA.op.op hM hN f))) =
      (NondegenerateScalars.complexToLinearMap hA.op
        (isNondegenerate hA (fromDoubleOpposite_isNondegenerate hN))
        (isNondegenerate hA (fromDoubleOpposite_isNondegenerate hM))
        (pullback hA (fromDoubleOpposite_isNondegenerate hM)
          (fromDoubleOpposite_isNondegenerate hN) (fromDoubleOppositeMap f))).comp
            (dualComparisonCanonicalLinear hA hN).toLinearMap :=
  @dualComparison_linear_naturality.{uA,uM,uN}

example :
    {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖᵐᵒᵖ M] →
    {N : Type 2} → [AddCommGroup N] → [NonUnitalModule Aᵐᵒᵖᵐᵒᵖ N] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ M) →
    (hN : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ N) →
    (f : NonUnitalModuleHom Aᵐᵒᵖᵐᵒᵖ M N) →
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fromDoubleOppositeAction (A := A) (M := N)
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hM)
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hN)
    (dualComparisonHom hA hM).comp
        (fromDoubleOppositeMap (pullback hA.op.op hM hN f)) =
      (pullback hA (fromDoubleOpposite_isNondegenerate hM)
        (fromDoubleOpposite_isNondegenerate hN) (fromDoubleOppositeMap f)).comp
          (dualComparisonHom hA hN) :=
  @dualComparison_cross_naturality.{0,1,2}

example :
    {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 2} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖᵐᵒᵖ M] →
    {N : Type 0} → [AddCommGroup N] → [NonUnitalModule Aᵐᵒᵖᵐᵒᵖ N] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ M) →
    (hN : IsNondegenerate Aᵐᵒᵖᵐᵒᵖ N) →
    (f : NonUnitalModuleHom Aᵐᵒᵖᵐᵒᵖ M N) →
    letI := fromDoubleOppositeAction (A := A) (M := M)
    letI := fromDoubleOppositeAction (A := A) (M := N)
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hM)
    letI := fromDoubleOppositeAction (A := Aᵐᵒᵖ) (M := Dual hA.op.op hN)
    (dualComparisonHom hA hM).comp
        (fromDoubleOppositeMap (pullback hA.op.op hM hN f)) =
      (pullback hA (fromDoubleOpposite_isNondegenerate hM)
        (fromDoubleOpposite_isNondegenerate hN) (fromDoubleOppositeMap f)).comp
          (dualComparisonHom hA hN) :=
  @dualComparison_cross_naturality.{1,2,0}

end Langlands.Algebra.NonUnitalModuleDualComparison
