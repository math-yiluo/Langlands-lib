/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantCohomology
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicLiftedTransitionCanonicalTranspose

/-! # Transpose of the lifted finite perfect transition

Source: Stacks Project, Tags 06YY and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-lifted-transition-transpose).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived

/-- The lifted transition has invertible transpose for the derived restriction adjunction.

Source: Stacks Project, Tags 06YY and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-lifted-transition-transpose).

The transpose is computed by transporting the normalized transpose of the supplied tower
transition through the coefficient-universe lift and its scalar-restriction comparison.
Both transports are equivalences, so they preserve invertibility. -/
theorem finitePerfectAdicLiftedTransition_transpose_isIso
    {A : Type t} [CommRing A] {d : AdicCoefficientDatum A}
    (T : FinitePerfectAdicAlgebraTower d) (n : ℕ)
    {L : DerivedCategory (ModuleCat.{t + 1}
        (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1)))) ⥤
      DerivedCategory (ModuleCat.{t + 1}
        (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))}
    (adj : L ⊣ normalizationModuleRestrict
      (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))) :
    IsIso ((adj.homEquiv _ _).symm (finitePerfectAdicLiftedTransition T n)) := by
  let q : ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1)) →+*
      ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)) :=
    RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
  letI : (normalizationModuleRestrict q).IsRightAdjoint :=
    ModuleCat.derivedRestrictScalars_isRightAdjoint.{t + 1, 0} q
  let canAdj := Adjunction.ofIsRightAdjoint (normalizationModuleRestrict q)
  have hcan : IsIso ((canAdj.homEquiv _ _).symm
      (finitePerfectAdicLiftedTransition T n)) := by
    exact finitePerfectAdicLiftedTransition_canonical_transpose_isIso T n
  let e := canAdj.leftAdjointUniq adj
  let f := (adj.homEquiv _ _).symm (finitePerfectAdicLiftedTransition T n)
  let fcan := (canAdj.homEquiv _ _).symm (finitePerfectAdicLiftedTransition T n)
  have hef : e.hom.app _ ≫ f = fcan := by
    apply (canAdj.homEquiv _ _).injective
    rw [canAdj.homEquiv_unit]
    simp only [Functor.map_comp]
    dsimp only [e]
    rw [← Category.assoc, canAdj.unit_leftAdjointUniq_hom_app adj]
    dsimp only [f]
    rw [← adj.homEquiv_unit]
    simp only [Equiv.apply_symm_apply]
    dsimp only [fcan]
    rw [Equiv.apply_symm_apply]
  have hi : IsIso (e.hom.app _ ≫ f) := by
    rw [hef]
    infer_instance
  exact (isIso_comp_left_iff (e.hom.app _) f).mp hi

end AlgebraicGeometry.Scheme
