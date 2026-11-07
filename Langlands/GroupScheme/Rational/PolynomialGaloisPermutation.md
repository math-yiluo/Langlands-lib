# Galois conjugation with permuted polynomial coordinates

This internal construction supports descent of parametrized closed subsets.
It extends the existing coefficient-only `PolynomialGalois.conjugate` to
coordinate permutations. The ground field `k`, extension field `K`, coordinate
type `I` and universe are arbitrary.

For a `k`-automorphism `σ` of `K` and a permutation `e` of `I`,
`conjugatePermute k K I σ e` is an actual `k`-algebra endomorphism of
`MvPolynomial I K`. It first conjugates coefficients by `σ`, then renames
`X i` as `X (e i)`. It sends a constant `C c` to `C (σ c)`.
The coefficient action and the variable permutation commute. The implemented
identity and composition proofs check the two generating families, constants
and variables, by polynomial ring-homomorphism extensionality.

For any supplied permutation action
`ρ : (K ≃ₐ[k] K) →* Equiv.Perm I`, `orbitAction` bundles these maps as a
monoid homomorphism. Its multiplication law applies `τ` first and `σ` second
for the element `σ * τ`, both on coefficients and on coordinate indices.
Thus inverses in the Galois group also act as inverse polynomial maps.
Neither the construction nor its action laws require a finite extension,
a finite coordinate type or Galoisness of the extension.

The kernel results concern an arbitrary commutative `k`-algebra `A` and a
supplied coordinate pullback

```lean
f : K ⊗[k] A →ₐ[k] MvPolynomial I K.
```

Their explicit equivariance hypothesis is

```lean
f (TensorGaloisPoint.coefficientConjugate k K A σ x) =
  orbitAction k K I ρ σ (f x).
```

If `x` lies in the actual ideal `RingHom.ker f.toRingHom`, this equation
sends `f x = 0` to zero under a polynomial algebra homomorphism.
`coefficientConjugate_mem_ker` therefore proves stability of this kernel
under every coefficient automorphism on `K ⊗[k] A`.
When `[IsGalois k K]` is supplied, `map_groundIdeal_ker_eq` applies the
published arbitrary-Galois tensor-ideal descent theorem: the kernel equals
the extension of its contraction along `A → K ⊗[k] A`. No finite-degree,
perfectness or infinitude assumption is used.

The provenance is internal. The implementation combines Mathlib's
polynomial coefficient and renaming maps with the Library's
`PolynomialGalois.conjugate`, `TensorGaloisPoint.coefficientConjugate` and
`GaloisIdealDescent.map_groundIdeal_eq`. It asserts no new
literature-specific theorem. In the intended ordinary Steinberg product
application, `I` will index simple roots and `ρ` their ordinary Galois
permutation. The consumer must still construct that actual action, establish
the displayed equivariance for the actual coordinate pullback, and identify
its kernel with the defining ideal of the intended closed image. This unit
does not supply those geometric facts, root representatives, a cross-section,
or a rational lifting theorem.
