# Integrability of the expanded adjacent-rank transformed coefficient

This internal helper proves compact support and integrability for the right
integrand of `AdjacentRankModelStarStatement`. It does not prove the integral
identity. The Fourier action remains `adjacentRankRho0 psi nu hself` throughout.
`adjacentRankTransformedIntegrand` names the expanded scalar integrand for an
arbitrary input tensor. In the model-star target that input is the full
plus-Fourier transform on the Schwartz factor tensored with the identity.

The compact-support theorem assumes a canonical p-adic field in universe uF,
an original complex module in independent universe uV, a smooth representation
sigma of GL_(r+1), every standard-character functional ell, every rectangular
Schwartz function Phi and every vector W in the actual coefficient image.
It includes r=0, zero functionals and reducible representations. Its conclusion
is compact support of

```text
h |-> Phi(adjacentRankKernelMatrix h)
       * W(w_(r+1) * inverseTranspose (h^(-1))).
```

The implementation chooses an original vector v representing W in the actual
coefficient image. The Weyl-translated functional on
`inverseTransposePullback sigma` has inverse standard character by the published
`dualFunctional` construction. The identity
`standardCharacter_scale_neg_one` lets it be viewed as a standard functional
for the nontrivial unitary character `psi.scale(-1)` without changing its
linear functional. The resulting coefficient of v is exactly
`a |-> W(w_(r+1) * inverseTranspose a)`, as follows by the representation's
multiplication law. Applying `adjacentRankPure_hasCompactSupport` to that
coefficient and the smooth pullback representation proves the conclusion.
This character change is used only for the coefficient support argument.

The integrability theorem allows any whole algebraic test tensor Psi and
ambient k in GL_(r+2), any supplied scalar additive Haar nu with
`IsSelfDual psi nu`, and any continuous quasicharacter chi. It asserts
integrability, against exactly `generalLinearHaar F.Carrier r`, of

```text
h |-> adjacentRankTestEvaluation psi sigma ell
        (adjacentRankRho0 psi nu hself sigma ell k Psi)
        (adjacentRankKernelMatrix h)
        (w_(r+1) * inverseTranspose (h^(-1)))
      * chi^(-1)(det h) * |det h|^(r/2).
```

For a pure tensor, the rho0 action gives another Schwartz function.
The preceding theorem gives compact support of its product with the
transformed coefficient. The kernel, coefficient argument, smooth coefficient,
quasicharacter and canonical determinant weight are continuous.
The shared Haar is finite on compact sets, so
`Continuous.integrable_of_hasCompactSupport` applies. Tensor induction and
linearity of the action and evaluation extend integrability to every test
tensor. No topology or norm on the original carrier or coefficient model is used.

The provenance is internal and derived. The helper specializes the already
published unconditional convergence support argument and the actual dual
coefficient construction to the character-separated right integrand of the
published model-star target. That target explains its relation to JPSS
Section 6.2 Proposition (1), printed p.431, and the Section 6.1 conventions.
The present proof imports only the unchanged target and convergence proof;
it does not assume a scalar Fourier identity, an image theorem, a growth
condition, irreducibility, or a factor-existence result.
