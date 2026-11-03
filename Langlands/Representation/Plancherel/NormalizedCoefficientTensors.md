# Normalized induced coefficient tensors and choice independence

This module specializes the canonical coefficient tensor to the existing
actual Haar-normalized induction and proves independence of its transport
from the chosen equivalence of irreducible admissible inducing
representations. All declarations are in `Langlands.Plancherel`.

## Source and scope

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI [10.1017/S1474748003000082](https://doi.org/10.1017/S1474748003000082),
V.1, printed p.288 (PDF p.54), defines `L(ω,P)` using product induction,
identifies it with the tensor of normalized induction and its smooth
contragredient, and defines the coefficient by `ℓ(π(g)v)`.

VI.1, printed pp.295–296 (PDF pp.61–62), says that an isomorphism of
equivalent irreducible inducing representations gives a canonical
isomorphism of these coefficient spaces, independent of the initial
isomorphism. The subsequent stabilizer example acts on the tensor by
`A ⊗ transpose(A⁻¹)` and need not act trivially.

This is a derived internal construction for the **tensor side** of these
passages. It uses the previously defined `CoefficientTensor`,
`coefficientTensorMap`, and `coefficientTensorCongr`. It proves the
isomorphism-choice independence after actual normalized induction. The
comparison of this tensor with the source's product-induced definition of
`L(ω,P)` remains a separate obligation. In particular the module does not
replace that comparison by a definition or assert a new induction-duality
theorem.

## Existing normalized induction and hypotheses

Let `G : Type uG` be a locally compact nonarchimedean group.
`NonarchimedeanGroup G` includes its topological-group structure. The
inputs are actual subgroups `P`, `M`, and `U`, a proof
`h : Aubert.General.IsSemidirectDecomposition P M U`, and
`hU : IsClosed (U : Set G)`. The decomposition says that both factors
lie in `P`, that `P` normalizes `U`, and that the factors are complements
inside `P`. No existence of such subgroups or realization for every
reductive rational-point group is proved here.

For a canonical smooth complex `M`-representation `A`, write

`I(A) = (Aubert.General.normalizedInductionFunctor h hU).obj A`.

This existing functor inflates along `h.projection : P →* M`, twists by
the actual Haar-modulus character
`HaarModulus.closedHalfCharacter U hU P h.le_normalizer`, and takes smooth
induction. Its functions satisfy
`v(p g) = δ_P(p)^(1/2) A.representation (h.projection p) (v(g))`;
the ambient group acts by right translation. The modulus is the existing
Haar construction, rather than a freely selected normalizing parameter.

The module reuses
`Aubert.General.normalizedInductionEquivOfEquiv h hU e` for an inducing
equivalence `e`. This equivalence applies `e` pointwise to induced
functions, as its imported evaluation theorem states; its inverse is
pointwise application of `e.symm`.

The group universe and the independent inducing-carrier universes
`uV`, `uW`, and `uX` are preserved. Induced carriers live in
`Type (max uG uV)`, and similarly for the other carriers. The complex
field has universe zero. The scalar-cancellation helper separately works
over any commutative ring in an independent universe `uR`.

## Coefficient map and transport

`NormalizedCoefficientTensor h hU A` abbreviates

`I(A) ⊗[ℂ] SmoothDual I(A).representation`.

`normalizedCoefficientMap h hU A` is the existing tensor coefficient
map specialized to `I(A)`. Its codomain is the actual space of locally
constant functions `LocallyConstant G ℂ`. The theorem
`normalizedCoefficientMap_tmul` proves

`normalizedCoefficientMap h hU A (v ⊗ ℓ) g = ℓ.val (I(A).representation g v)`.

`normalizedCoefficientMap_biInvariant` specializes the generic
bi-invariance theorem: every tensor coefficient is invariant on both
sides under one open subgroup of `G`. Compactness of this subgroup is
not asserted.

`normalizedCoefficientTransport h hU e` is
`coefficientTensorCongr (normalizedInductionEquivOfEquiv h hU e)`.
It is an actual complex linear equivalence of the two induced coefficient
tensors. `normalizedCoefficientTransport_tmul` states its pure-tensor
formula: the induced equivalence acts on the vector, and inverse
pullback through that equivalence acts on the actual smooth dual.

`normalizedCoefficientMap_transport` proves equality of the resulting
locally constant coefficient functions. `normalizedCoefficientTransport_action`
proves that transport intertwines the existing external `G × G` tensor
actions. These two theorems specialize the corresponding generic
coefficient-tensor laws and require no irreducibility or admissibility.

## Implemented choice-independence proof

`coefficientTensorCongr_eq_of_scalar` is a generic algebraic helper for
canonical smooth representations over a commutative ring. Suppose
`e,f : A.representation.Equiv B.representation` and
`f v = c • e v` for all `v`. Applying `e` and the inverse identities
proves

`c • f.symm w = e.symm w`.

Consequently, by evaluation on `w` and linearity of a smooth functional,

`c • contragredientMap f.symm.toIntertwiningMap ℓ =
  contragredientMap e.symm.toIntertwiningMap ℓ`.

On a pure tensor, the scalar on `f v` can be moved to the second tensor
factor by the balanced tensor relation and then canceled using this
equality. Tensor induction extends the identity to every tensor, and
linear-equivalence extensionality gives
`coefficientTensorCongr f = coefficientTensorCongr e`.
There is no division and no separate nonzero-scalar hypothesis.

`admissibleEquiv_exists_scalar` assumes that the source complex
representation `A.representation` is admissible and irreducible. It
applies the existing proved `Langlands.admissibleSchur_scalarEndomorphism`
to the endomorphism `e.symm ∘ f`. Evaluating the scalar-endomorphism
identity and applying `e` gives `f v = c • e v`.
`coefficientTensorCongr_eq_of_admissible` combines this with the generic
cancellation lemma to prove choice independence on the source
coefficient tensor.

For actual normalized induction,
`normalizedInductionEquivOfEquiv_scalar` proves pointwise that the same
scalar relation holds between the induced equivalences. Extensionality
through the two function subtypes reduces this directly to the inducing
scalar relation at each function value.

`normalizedCoefficientTransport_independent` applies the Schur argument
to the **inducing Levi representation** `A.representation`, lifts the
scalar relation through normalized induction, and applies the generic
tensor cancellation. It concludes equality of the actual linear
equivalences `normalizedCoefficientTransport h hU e` and
`normalizedCoefficientTransport h hU f`. Only the inducing source has
admissibility and irreducibility premises. In particular, the proof does
not assume irreducibility of either normalized induced representation.

## Coherence and remaining obligations

`normalizedCoefficientTransport_refl` proves identity transport.
`normalizedCoefficientTransport_trans` proves that transport along
`e.trans f` equals successive transport along `e` and `f`. In each
case the normalized-induction equivalences agree pointwise; the generic
tensor identity and composition laws then give the result.

These constructions and laws do not yet construct compact models,
smooth families over twist orbits, or descent by a stabilizer action.
Choice independence of an equivalence between fixed inducing objects
does not assert that self-twist stabilizers act trivially on a fixed
compact model. The source's product-induction/contragredient comparison,
analytic properties of coefficients, wave packets, and Plancherel
inversion remain downstream obligations.

The imports reuse the canonical `SmoothRep` and actual smooth dual,
the coefficient-tensor construction, the existing normalized-induction
carrier transport, and the published admissible Schur proof. The helper
lemmas above are internal consequences of these constructions rather
than additional assertions attributed verbatim to Waldspurger.
