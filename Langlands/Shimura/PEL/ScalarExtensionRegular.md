# Regular source modules and the Harris similitude group

This internal comparison connects two published constructions. In
`ScalarExtension`, a rational algebra `A` acts on the scalar extension
`R ⊗[ℚ] V` through `A ⊗[ℚ] R`. In `TraceSimilitudesTopology`, regular-module
similitudes are linear for the algebra `R ⊗[ℚ] A` acting on itself by left
multiplication. When `V = A` is the regular left module, these describe the
same operators after commuting the tensor factors. The module proves that
comparison algebraically and topologically, then applies it to the existing
Harris trace form. It introduces no new geometric or nondegeneracy input.

Let `A` be a ring with a rational algebra structure and `R` a commutative
rational algebra. Write `c : A ⊗[ℚ] R ≃ₐ[ℚ] R ⊗[ℚ] A` for the tensor
commutation equivalence. The theorem `scalarExtensionRegular_smul` states
that the published `scalarExtensionAlgebraModule A A R` satisfies

`a • x = c(a) * x`.

The proof uses induction on both tensor arguments, the published
pure-tensor action formula, and multiplication of pure tensors. Additivity
handles sums. Thus an operator is linear for this extended action exactly
when it is linear for the regular left action of `R ⊗[ℚ] A`.

`scalarExtensionRegularOperator` is the resulting multiplicative
equivalence between the two groups of linear automorphisms. Its forward
and backward maps retain the same function and inverse function; only
their linearity proofs change. For forward linearity, apply the original
linearity equation to `c⁻¹(a)` and use `c(c⁻¹(a)) = a`. For backward
linearity, apply regular linearity to `c(a)`. Both inverse laws and the
multiplication law follow by pointwise extensionality.

For any rational bilinear form `ψ` on `A`,
`scalarExtensionRegularSimilitudesEquiv` restricts this operator
equivalence to a group equivalence

`ScalarExtensionSimilitudes A A R ψ ≃*`
`bilinearSimilitudes (R ⊗[ℚ] A) (ψ.baseChange R)`.

The multiplier and the equation expressing preservation of the form up to
that multiplier are unchanged. The `_apply`, `_inverse_apply`,
`_symm_apply` and `_multiplier` lemmas identify the actual operators in
both directions and the multiplier. This comparison requires neither
finite dimensionality nor nondegeneracy of `ψ`.

When `R` is a topological space, equip `R ⊗[ℚ] A` with its canonical
`R`-module topology. The source named carrier
`ScalarExtensionSimilitudePoints` has the published initial topology for
its forward operator, inverse operator and unit multiplier. On the target
use the independently published `regularBilinearTopology` with the same
tensor-module topology. The coordinates are identical under the preceding
equivalence, so `scalarExtensionRegularContinuousEquiv` is a continuous
group equivalence. Both continuity proofs use continuity into an induced
topology and continuity of its inducing coordinate map. No ring-continuity
or topological-group assumption is needed for this general comparison.

For the Harris specialization, retain the actual
`CentralSimpleUnitaryData E K A n`, including the number fields, CM and
totally real assumptions, algebra structures and scalar towers in Lean.
Let `β : Aˣ` satisfy `D.involution β = -β`. Put

`τ = D.skewTwist β hβ`,
`ψ = τ.tracePairing β⁻¹`.

These are the published auxiliary involution and inverse-unit rational
trace form; their normalization and relation to the original involution
are inherited from `TraceSimilitudesBaseChange` and
`TraceSimilitudesTopology`. In particular the extended form is exactly
`ψ.baseChange R`, definitionally the trace form used by
`D.HarrisBilinearPoints β hβ R`.

`harrisScalarExtensionBilinearContinuousEquiv` specializes the general
regular-module comparison to give

`ScalarExtensionSimilitudePoints A A R ψ ≃ₜ*`
`D.HarrisBilinearPoints β hβ R`.

Its forward and backward operator formulas and multiplier formula are
definitional. This part still needs only a topology on `R`.

For a topological rational algebra `R`, composition with the published
`harrisTraceSimilitudesContinuousEquiv` gives
`harrisScalarExtensionContinuousEquiv`:

`(D.toSecondKindInvolution.rationalInvolution.Points R)ᵐᵒᵖ ≃ₜ*`
`ScalarExtensionSimilitudePoints A A R ψ`.

The source retains its existing module, units, subgroup and opposite
topologies. The opposite is essential: the actual operator attached to
`g` is `x ↦ x * g.unop.val.1`. The `_apply` theorem identifies this
operator, and `_multiplier` identifies its multiplier with the original
involution group's multiplier. Nondegeneracy and the right-adjoint
identity required by this second comparison are the proved results used
by the imported Harris comparison; this module does not assume them as
new fields.

The definitions `harrisFiniteAdelicScalarExtensionContinuousEquiv` and
`harrisPrimeToScalarExtensionContinuousEquiv` specialize to the actual
`FiniteAdeles ℚ` and `PrimeToFiniteAdeles m`. The latter allows every
natural modulus and supplies the prime-to-p case at a prime modulus.
These are the scalar-extension carriers used by the full and away Weil
level towers when the rational source module is `A` with the form `ψ`.

The provenance is internal: the new comparisons follow from the
published tensor action, the two existing operator topologies, and the
published Harris trace comparison. This unit does not construct a new
PEL input, a polarization, a compatible frame or a moduli functor. It
does not choose compact-open subgroups or assert nonemptiness of any
level set.
