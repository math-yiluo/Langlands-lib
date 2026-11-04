# Actual smooth sections over every representative in a unitary twist orbit

`Langlands.Plancherel.productInducedSmoothTensorOrbitEquiv` identifies diagonal
invariant smooth tensors with coherent actual normalized product-induced
sections on every irreducible admissible representative in a fixed unitary
unramified twist orbit. Restriction to the literal parameter representatives
is proved to be a linear equivalence. Its inverse is actual inducing
transport, independent of the chosen parameter and inducing equivalence.

## Source and provenance

This is a derived construction for J.-L. Waldspurger, *La formule de Plancherel
pour les groupes p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2
(2003), 235–333, DOI 10.1017/S1474748003000082, VI.1, printed pp.295–296
(PDF pp.61–62). The registered source is `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

The passage first constructs canonical transport between equivalent inducing
representatives by vector transport and inverse pullback on functionals. It
then defines sections compatible with that transport, tests smoothness in a
fixed compact picture on the unitary character cover, and identifies the
section space with diagonal invariant tensors. The present construction makes
the representative descent explicit, using the actual product-induced fibers
of `ProductInducedTransport` and the smooth parameter-family model of
`ProductInducedSmoothFamilies`. The generic subgroup setting and explicit
finite-coordinate smoothness convention are derived content. No abstract
bijection or desired descent assertion is supplied as an assumption.

## Data and scope

The group `G` is locally compact and nonarchimedean. The actual subgroups
`P`, `M`, `U` have a supplied semidirect decomposition `h`. The subgroup `U`
is closed. These data suffice for the raw all-representative section space
and its actual inducing transport. The smooth comparison also retains:

- a compact open subgroup `K` and closed `P`;
- continuity of the positive characters `ν : I → (M →* ℝ≥0ˣ)`;
- continuity of the Levi projection `h.projection`;
- an actual factorization `G = P K`;
- a finite type `J` and a supplied multiplicative equivalence
  `e : unitaryUnramifiedCharacters ν ≃* (J → Circle)`.

The fixed inducing representation `π` is a canonical complex
`IrreducibleAdmissibleRep`. Every representative index uses that same carrier
universe `uV`; all representatives in that universe are included. The ambient
group, positive-character index, representation carrier and torus-index
universes are independent. The representatives are actual smooth objects,
not merely names for quotient classes. No irreducibility of parabolic
induction, Hermitian structure, norm on the coefficient space, second
countability or finiteness of the stabilizer is assumed.

The result concerns the unitary twist orbit of this fixed object. No
square-integrability premise is needed for this construction. Comparison
with discrete-series classes and the source's full stabilizer, and the
rational reductive realization of the subgroup hypotheses, remain separate.
The smoothness convention is finite scalar-smooth sums in the supplied
coordinates, tested after actual compact restriction. Invariance under other
coordinate systems or changes of the fixed base representation is not
asserted here. The normalized induction is the existing full-parabolic
positive Haar half-character normalization; its comparison with the source's
Levi-inflated normalization remains separate. There is no analytic
Plancherel, formal-degree, normalized-intertwiner or wave-packet assertion.

## All representatives and their actual fibers

Write `Xᵤ = unitaryUnramifiedCharacters ν`, let `ι` be its literal inclusion
into all unramified characters, and write `χ_z = ι(e.symm z)`.
`UnitaryOrbitRepresentative ν π` is the subtype of all actual canonical
irreducible admissible objects `A` satisfying

\[
  \exists\chi\in X_u,\quad [\pi\otimes\iota(\chi)]=[A].
\]

The equality is in the canonical `SmoothDualClass` quotient and therefore
means actual categorical isomorphism. `unitaryOrbitParameterRepresentative`
sends `z` to the literal twisted object `π ⊗ χ_z` with its orbit membership
proof. The raw dependent section space `ProductInducedOrbitSections` is

\[
  \prod_{A\in\operatorname{UnitaryOrbitRepresentative}(\pi)} H(A),
  \qquad H(A)=\operatorname{productInducedCoefficientObject}(h,h_U,A).
\]

These are actual normalized induced functions on `G × G` with values in the
vector tensor the actual smooth contragredient of `A`.
`coherentProductInducedOrbitSections` is the submodule defined by

\[
  q(B)=T_a(q(A))
  \quad\text{for every actual equivalence }a:A\simeq B,
\]

where `T_a = productInducedCoefficientTransport h hU a` is pointwise vector
transport tensored with inverse functional pullback. Linearity of that
transport proves closure under zero, addition and scalar multiplication.
`productInducedOrbitPullback` evaluates a section at the literal parameter
representatives, giving the dependent family `F(z)=q(π ⊗ χ_z)`.

## Independence of the parameter and equivalence

`exists_unitaryStabilizer_of_parameter_equiv` proves the required relation
between parameters. Given an actual equivalence between the representatives
at `z` and `w`, put `χ=e.symm z` and `η=e.symm w`. Equality of their canonical
classes and cancellation of the existing character action show that
`χ⁻¹ η` belongs to the actual unitary class stabilizer `S`. In the torus
coordinates this gives `w=z τ(s)`, with `τ(s)=e(s)`.

`productInducedSmoothFamily_transport` combines this relation with the proved
stabilizer covariance of a smooth parameter family. The canonical transport
can be replaced by any actual equivalence between the same parameter
representatives, by admissible Schur on the twisted inducing source. Thus

\[
  F(w)=T_a(F(z))
\]

holds for every actual equivalence `a : π ⊗ χ_z ≃ π ⊗ χ_w`.

For an arbitrary representative `A`, `unitaryOrbitRepresentativeParameter`
chooses a parameter `z_A` from its actual membership witness.
`unitaryOrbitRepresentativeEquiv` obtains an actual equivalence
`b_A : π ⊗ χ_(z_A) ≃ A` from the canonical quotient equality.
`productInducedOrbitExtension` defines the linear extension

\[
  (\operatorname{Ext}F)(A)=T_{b_A}(F(z_A)).
\]

The theorem `productInducedOrbitExtension_of_equiv` proves the stronger formula

\[
  (\operatorname{Ext}F)(A)=T_a(F(z))
  \quad\text{for every }z\text{ and every }a:\pi\otimes\chi_z\simeq A.
\]

Its implemented proof applies parameter-family compatibility to
`a.trans b_A.symm`, composes the actual transports, and applies inducing
Schur to replace the resulting equivalence by `a`. Consequently neither
choice affects the resulting section. Composition of actual transport
proves `productInducedOrbitExtension_coherent`. Evaluation at a literal
parameter representative using the identity equivalence proves
`productInducedOrbitPullback_extension`. The theorem
`productInducedOrbitExtension_unique` proves uniqueness among all coherent
sections with this pullback, even before imposing a smoothness condition.

The pointwise theorem `productInducedOrbitExtension_eval_of_equiv` retains
actual induced-function evaluation: for every `x : G × G`,

\[
  (\operatorname{Ext}F)(A)(x)
    =(a\otimes(a^{-1})^*)\bigl(F(z)(x)\bigr).
\]

Here the displayed tensor operator is literally `productCoefficientLeviEquiv a`
on the actual smooth dual, not an independently specified operator.

## Smooth sections and the tensor model

Let `W = ProductInducedCompactPicture h K π.obj` and let `R` be the actual
pointwise compact restriction equivalence of `ProductInducedSmoothFamilies`.
`productInducedSmoothOrbitSections` is the intersection of the coherent
section submodule with the preimage of `finiteSmoothFamilies J W` under
`R ∘ productInducedOrbitPullback`. Its smoothness condition means an actual
finite sum of fixed compact sections times scalar functions whose real-angle
lifts are `ContDiff ℝ ∞`.

`productInducedSmoothOrbitPullback` maps these sections to
`productInducedSmoothFamilies`. Coherence supplies exactly the required
canonical stabilizer covariance; the finite smooth condition is already in
the definition. Conversely, `productInducedSmoothOrbitExtension` has coherent
values by the theorem above and has smooth restrictions because its pullback
is exactly the given smooth family. The two inverse identities give
`productInducedSmoothOrbitFamilyEquiv`, with actual pullback as its forward
linear map. The other inverse identity uses coherence with the chosen
realizing equivalence at each representative.

Finally, `productInducedSmoothTensorOrbitEquiv` composes the existing tensor-to-
parameter-family equivalence with this extension. It proves

\[
 [\,C^\infty(J\to\mathrm{Circle})\otimes_{\mathbb C}W\,]^S
 \simeq_{\mathbb C}
 \operatorname{productInducedSmoothOrbitSections}.
\]

The action on the left is the genuine diagonal action already constructed:
inverse translation of scalar functions together with the possibly
nontrivial actual coefficient self-twist action on `W`.
`productInducedSmoothTensorOrbitEquiv_apply_of_equiv` gives the value at any
representative by any realizing parameter and equivalence. The parameter
value is the existing actual normalized extension of the compact tensor
evaluation, including its normalized `p k` formula.
`productInducedSmoothTensorOrbitEquiv_restriction` proves that pullback and
compact restriction of the resulting section recover the literal tensor
evaluation. Its `_symm_evaluation` theorem recovers, in the inverse direction,
the actual compact restriction of the original section at each parameter.
