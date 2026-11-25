/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantCohomology
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicLiftedTransitionUniversal
import WeilConjectures.AlgebraicGeometry.Etale.EtaleNormalizationArrowUniversal

/-! # Sourcewise universality of the constant finite perfect transition

Source: Stacks Project, Tags 06YY, 093J and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-constant-normalization-universal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The explicit constant transition is universal after pullback to one etale source.

Source: Stacks Project, Tags 06YY, 093J and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-constant-normalization-universal).

Proof: the normalized algebraic transition is the transpose of an isomorphism under
the chosen derived scalar adjunction. Termwise coefficient lift and the constant
realization comparison transport this universal arrow to the displayed etale source
arrow. The coefficient mate for inverse image is an isomorphism, so transport along
it preserves initiality of the structured arrow. This is independent of coherence
between different etale sources and of any actual quotient or Isom sheaf.
-/
theorem finitePerfectAdicEtaleConstant_universal (Y : Scheme.{t})
    {A : Type t} [CommRing A] {d : AdicCoefficientDatum A}
    (T : FinitePerfectAdicAlgebraTower d) (n : ℕ) (U : Y.Etale) :
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk
      (etaleIsomorphismNormalizationArrow Y
        (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
        (finitePerfectAdicEtaleConstantTransition Y T n) U))) := by
  have h := finitePerfectAdicLiftedTransition_universal T n
  simpa [finitePerfectAdicEtaleConstantTransition] using
    (etaleNormalizationArrow_universal_of_constant Y
      (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
      (finitePerfectAdicLiftedTransition T n) h U)

end AlgebraicGeometry.Scheme
