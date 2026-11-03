# Representative transport on actual product induction

This module constructs transport between the actual product-induced coefficient
spaces of equivalent inducing representations. It applies the vector
equivalence and inverse smooth-dual pullback to every induced function value.
It proves preservation of the diagonal contraction, the actual coefficient
function and coefficient image, together with identity, composition and
independence of the chosen equivalence for an irreducible admissible inducing
representation.

## Source and provenance

The source is J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI 10.1017/S1474748003000082, registered as
`waldspurger-2003-plancherel`.

VI.1, printed pp.295–296 (PDF pp.61–62), first chooses an equivalence of
representatives, induces the corresponding equivalence of contragredients, and
then induces an equivalence of
`L(omega,P) = I_(P × P)^(G × G)(E ⊗ Echeck)`. The source asserts that this last
equivalence is independent of the initial choice and uses it in its
representative compatibility condition on families. The displayed example on
printed p.296 explicitly has the vector map tensored with the transpose of its
inverse. The original passages and that formula were read directly.

The construction here implements that pointwise map using
`coefficientTensorCongr` on the actual product Levi and
`normalizedInductionEquivOfEquiv` on the actual product parabolic. The proof
of choice independence imports the existing admissible Schur result on the
inducing representation. The coefficient-preservation argument uses the proved
diagonal integral in `ProductInducedCoefficients`. These generic
actual-subgroup results, the composition laws and the full contraction
identity are derived adapters, rather than additional assertions attributed
verbatim to the source.

## Objects and assumptions

For the product-Levi construction, `G : Type uG` is a topological group,
`M : Subgroup G`, and

```lean
A : SmoothRep.{0, uG, uV} ℂ M
B : SmoothRep.{0, uG, uW} ℂ M
e : A.representation.Equiv B.representation
```

The three universes are independent. Composition allows a third inducing
carrier in an independent universe `uX`. All duals are actual smooth
contragredients on the canonical `SmoothRep` framework, and the pairing is
complex bilinear.

For the induced transport, `G` is locally compact and nonarchimedean.
Actual subgroups `P`, `M`, `U`, an
`h : IsSemidirectDecomposition P M U` and closed `U` are explicit.
Write `I(A)` for `(normalizedInductionFunctor h hU).obj A` and `L(A)`
for `productInducedCoefficientObject h hU A`. The latter is the actual
normalized induction from the literal `P.prod P` with values in
`A ⊗ A.contragredient`, using `h.prod h` and the canonical Haar half-character.

The construction, pointwise evaluation, contraction preservation, identity,
composition and product-action intertwining need no admissibility or
irreducibility. Choice independence additionally requires
`hA : A.IsAdmissible` and `A.representation.IsIrreducible`.
It does not require irreducibility of `I(A)` or of any product induction.

## The actual pointwise transport

`productCoefficientLeviEquiv e` has underlying linear equivalence
`coefficientTensorCongr e`. On pure tensors its theorem
`productCoefficientLeviEquiv_tmul` reads

\[
 v\otimes\ell\longmapsto e(v)\otimes(\ell\circ e^{-1}).
\]

The product-Levi intertwining law follows by applying
`coefficientTensorCongr_action` through the actual product-subgroup
identification `HaarModulus.subgroupProdEquiv M M`. Thus the two coordinates
act on the vector and smooth-functional factors respectively.

`productCoefficientLeviEquiv_pairing` proves preservation of the contraction
`ev(v ⊗ ell) = ell(v)` on every tensor. Tensor induction reduces the pure
case to `ell(e.symm(e(v))) = ell(v)`; the sum case uses the linearity of both
the tensor map and the contraction.

`productInducedCoefficientTransport h hU e` is the representation equivalence
obtained by applying `normalizedInductionEquivOfEquiv` to that product-Levi
equivalence. Its evaluation theorem
`productInducedCoefficientTransport_eval` is the literal pointwise identity

\[
 (T_e F)(x)=(e\otimes(e^{-1})^*)F(x)
 \qquad(x\in G\times G).
\]

It holds definitionally on the actual normalized induced functions.
`productInducedCoefficientTransport_action` evaluates the representation
equivalence's intertwining law on any `F`; it concerns the full actual
`G × G` action.

`productInducedCoefficientIntegrand_transport` applies the evaluation identity
at `(k*g,k)` and then the contraction-preservation theorem. Consequently

\[
 J_g(T_e F)(k)=J_g(F)(k)
\]

for every `F`, `g` and `k`. This pointwise result uses no measure, compact
quotient, second countability or admissibility.

## Composition, choice independence and tensor comparison

`productInducedCoefficientTransport_refl` is the identity law, and
`productInducedCoefficientTransport_trans` states
`T_(e.trans f)(F) = T_f(T_e(F))`. Their proofs use extensionality of the
actual induced functions and the existing coefficient-tensor identity and
composition laws on every value.

`productInducedCoefficientTransport_independent` proves equality of the
representation equivalences `T_e = T_f` when `A` is irreducible admissible.
The imported `coefficientTensorCongr_eq_of_admissible` applies Schur to the
common inducing source `A`, expressing the two inducing equivalences as scalar
multiples. The scalar on vectors cancels inverse pullback on functionals.
Equality of the product-Levi maps then gives equality of their pointwise
normalized inductions. No assertion about irreducibility of parabolic
induction enters the proof.

The theorem `productInducedCoefficientTransport_tensor` additionally assumes
second countability of `G` and compactness of the actual left quotient
`Induction.LeftQuotient P`, as required by the proved product-induction
comparison. If `Q_A` denotes `normalizedProductInductionTensorEquiv` and
`I(e)` denotes `normalizedInductionEquivOfEquiv`, it states

\[
 T_e Q_A(f\otimes f^\vee)
   =Q_B\bigl(I(e)f\otimes I((e^{-1})^*)f^\vee\bigr).
\]

The proof evaluates both induced functions at each point and applies the
proved pure-tensor evaluation laws. This compatibility uses no integral
duality, admissibility or irreducibility.

## Preservation of coefficients and images

The last two theorems use exactly the hypotheses needed to define the
actual product-induced coefficient maps:

- `G` is Hausdorff, second countable and has its Borel measurable structure;
- `P` is closed and has a locally compact subgroup instance, and its actual
  left quotient is compact;
- `hG : ∀ g, Measure.modularCharacter g = 1`;
- the displayed parabolic modulus identity
  `Measure.modularCharacter q =
   (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0)`;
- the Levi projection `h.projection` is continuous;
- `hA : A.IsAdmissible` and `hB : B.IsAdmissible`.

Admissibility of `B` can also be obtained from `hA` and `e` by the imported
`isAdmissible_of_equiv`. The results hold for any proofs of these predicates.
Irreducibility of the inducing representations is not needed for coefficient
preservation or equality of images.

Both coefficient maps use the same
`normalizedInductionBruhatMeasure hP hG`, fixed independently of the inducing
object. `productInducedCoefficientMap_transport` rewrites each coefficient as
the integral of its actual diagonal contraction. The pointwise integrand
equality gives

\[
 E_{P,B}(T_e F)=E_{P,A}(F)
\]

as locally constant functions on `G`. Integrability is already proved in the
imported coefficient module; this argument does not postulate a pairing or a
coefficient identity.

`range_productInducedCoefficientMap_of_equiv` proves equality of the two
linear-map ranges. One inclusion transports an actual induced function by
`e`, and the other by `e.symm`, using the coefficient equality in each case.

## Remaining scope

This module implements the equivalence-of-representatives portion of VI.1
and its compatibility with the actual coefficient construction. It does not
construct compact pictures, smooth twist families, stabilizer descent or an
orbit-family space. Reductive rational-point realization, the
full-parabolic versus Levi-inflated modulus specialization, absolute
manuscript Haar normalization and the analytic Plancherel conclusions retain
their separate obligations. Choice independence here concerns equivalences
with a fixed source and target representation; it does not assert that a
self-twist acts trivially under a different compact-picture identification.
