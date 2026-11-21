# Twisted characters of finite external tensor products

Let `ι` be a finite index type, and for each `i` let `H i` be a Hausdorff,
locally compact, totally disconnected, second-countable topological group with an
admissible complex representation `ρ i` on `V i` and an endomorphism `A i`. The
Library's `FiniteTensor.external ρ` is the external tensor representation of the
product group `∀ i, H i` on `⨂[ℂ] i, V i`. It is admissible by
`FiniteTensor.isAdmissible_external`. `PiTensorProduct.map A` is the tensor
product of the endomorphisms.

The Prop `ExternalTensorTwistedCharacterStatement` (universes `uI`, `uG`, `uV`
of the index type, the groups and the representation spaces) quantifies over all
such data and states the conclusion below; `externalTensorTwistedCharacterStatement`
proves it at all universes by applying `hasTwistedCharacterValue_external`.

The main theorem `hasTwistedCharacterValue_external` states that if each `ρ i`
has twisted character value `c i` at `g i` for `A i` (the Library predicate
`HasTwistedCharacterValue`), then the external tensor product has twisted
character value `∏ i, c i` at `g` for `PiTensorProduct.map A`. When every `A i`
is the identity, `PiTensorProduct.map` of the identities is the identity, and
`hasTwistedCharacterValue_one_iff` turns the statement into the ordinary
character values. The twisted distributions are the Library's
`twistedDistribution`; no new character notion is introduced.

The block Levi `B.Levi E` of `GL_n(E)` is the product of the groups
`GL_{n_i}(E)`. On it, the normalized product induction uses the Levi tensor
representation of the block representations. This result therefore supplies the
product formula for the twisted character values of the inducing tensor
representation, written `Θ^B_Ξ` in Henniart–Lemaire (2011), II.4.5, printed
pp. 86–88 (PDF pp. 94–96). Applying it to that representation,
including any identification between the Levi tensor and
`FiniteTensor.external`, is left to the consumer.

## Supporting results

- `integratedAction_external_tprod`: for factor measures `μ i` (σ-finite and
  finite on compacts), the integrated action of the product measure `Measure.pi μ`
  on `piTensor f` sends `⨂ v i` to `⨂ (∫ f i · ρ i) (v i)`.
- `twistedDistribution_external_piTensor`: for left-invariant factor measures,
  the twisted distribution of the external tensor product at `piTensor f` is the
  product of the factor twisted distributions at `f i`.

## Proof implemented in Lean

1. *Integrated action.* The Library's integrated action is the finite algebraic
   integral of the simple function `x ↦ f x • ρ x v`. Partition each factor by
   the fibres of its action integrand. The product of these fibres gives an
   indicator presentation of the product integrand with pure-tensor values,
   using multilinearity to collect the scalars. Each fibre with nonzero value has
   finite measure, and a pure tensor with a zero factor vanishes, so the
   presentation satisfies the finiteness condition of
   `Hecke.integratedAction_eq_sum_of_presentation`. The product measure of a
   product of sets is the product of the factor measures (`Measure.pi_pi`).
   Expanding the pure tensor of the factor sums by multilinearity
   (`MultilinearMap.map_sum_finset`) gives the same finite sum.
2. *Trace.* The finite-rank operator of the external representation composed
   with the tensor endomorphism agrees on pure tensors, hence everywhere, with
   `FiniteRankEnd.piTensorMap` of the factor operators. Its finite-rank trace is
   the product of the factor traces by `FiniteRankEnd.trace_piTensorMap`.
3. *Local value for the product measure.* Choose compact open neighbourhoods
   `K i ⊆ U i` of `g i` inside the factor neighbourhoods where the factor values
   hold. Their product is an open neighbourhood of `g`. A test function `f`
   supported in it equals `f` times the pure tensor of the characteristic
   functions of the `K i`. By `span_piTensor`, `f` is a finite combination of
   pure tensors, and multiplication by that characteristic function sends each
   pure tensor to a pure tensor whose factors are supported in the `K i`. On
   such pure tensors, step 2, the factor values, and the product formula for
   integrals over `Measure.pi` (`integral_fintype_prod_eq_prod`) give
   `Θ = (∏ c i) ∫ · dμ`. Both sides are linear, so the identity holds for `f`.
4. *All Haar measures.* `HasTwistedCharacterValue` quantifies over all Haar
   measures for the Borel σ-algebra. With second-countable factors, that
   σ-algebra on the finite product is the product σ-algebra (`Pi.borelSpace`),
   and the product of the factor Haar measures is a Haar measure. Every Haar
   measure is a positive scalar multiple of it
   (`Measure.isMulLeftInvariant_eq_smul`). Rescaling the measure by `r`
   multiplies both the integrated action and the integral by `r`, so local
   values do not change.

Second countability is used only for the Borel σ-algebra of the product and for
the uniqueness of Haar measure.
