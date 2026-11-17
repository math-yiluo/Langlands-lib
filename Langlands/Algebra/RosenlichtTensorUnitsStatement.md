# Rosenlicht's tensor-unit statement

Worker 287, 17 November 2026.

`Langlands.Algebra.RosenlichtTensorUnitsStatement.{u,v,w}` is the affine
coordinate-ring reformulation of James S. Milne, *Algebraic Groups: The Theory
of Group Schemes of Finite Type over a Field* (2017), Proposition 12.48,
printed p.246, with proof on p.247 (PDF pages 262–263). The registered source
is `milne-2017-algebraic-groups`, content SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The registered official 2017 errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` contains no correction to
Proposition 12.48.

The proposition quantifies over an algebraically closed field `k : Type u`
and commutative `k`-algebras `A : Type v` and `B : Type w`, each a domain
and of finite type. For every actual unit `z : (A ⊗[k] B)ˣ`, it asserts
the existence of actual units `a : Aˣ` and `b : Bˣ` such that

```text
(z : A ⊗[k] B) = (a : A) ⊗ₜ[k] (b : B).
```

The three universes are independent. There are no additional hypotheses
giving rational points, normality, geometric integrality, divisors, or
compactifications. The equality is in Mathlib's algebra tensor product.
The declaration is a `Prop`-valued definition stating the result; this
module does not prove it.

For the source comparison, set `X = Spec(A)` and `Y = Spec(B)`. A domain
is nonzero, reduced, and has irreducible spectrum. An affine scheme is
separated, and the finite-type algebra hypotheses make `X` and `Y` varieties
of finite type over `k`. Their product over `Spec(k)` is represented by
`Spec(A ⊗[k] B)`. A regular map from an affine scheme `Spec(R)` to the
multiplicative group corresponds to a unit of `R`. Thus Milne's
factorization of a regular map `X × Y → Gₘ` into one map from each factor
says that the unit is the product of the images of `a` and `b` under the
two tensor-factor maps. This product equals `a ⊗ b`, giving the displayed
conclusion. This is the affine case of the source proposition; the
passage to arbitrary irreducible varieties is a separate obligation.

The Lean module imports only
`Mathlib.FieldTheory.IsAlgClosed.Basic`, `Mathlib.RingTheory.FiniteType`,
and `Mathlib.RingTheory.TensorProduct.Basic`, for the field condition,
finite-type condition, and tensor-product ring operations and notation.
It has no dependency on the scheme-level product-units statement.
