# Inverse-transpose transport to normalized opposite induction

Author: Worker 470.

This module constructs an equivalence on the actual function spaces of normalized
block induction. Its public constructor is
`Langlands.PadicField.TopologicalData.inverseTransposeProductToOppositeEquiv`.
For a prime `p`, any `F : PadicField.{uF} p`, supplied `T : F.TopologicalData`,
rank `n`, and block shape `B`, let `θ_r` be the published automorphism
`GeneralLinear.inverseTranspose r F.Carrier`. For any dependent family of complex
modules `V : Fin B.length → Type uV` and representations `σ_i` on these modules,
the constructor has type

```text
Representation.Equiv
  ((T.normalizedProductInduced B σ).comp θ_n.toMonoidHom)
  (T.normalizedOppositeParabolicInduced B
    (B.blockTensor (fun i => (σ i).comp θ_(B.size i).toMonoidHom)))
```

The field universe `uF` and module universe `uV` are independent. Every function
space uses `T.topology` and `T.generalLinearTopologicalGroup n`. Values belong to
the existing `PiTensorProduct ℂ V`; the block index set and the order of whole
blocks are unchanged. No smoothness or other representation-theoretic condition
on the factors is required.

The forward map and inverse are both precomposition with `θ_n`:

```text
E(f)(x)       = f(θ_n(x)),
E.symm(h)(x)  = h(θ_n(x)).
```

The laws `inverseTransposeProductToOppositeEquiv_eval` and
`inverseTransposeProductToOppositeEquiv_symm_eval` express these formulas with
`Induction.eval` on the precise published source and target carriers. They refer
to this same constructor. Inverse transpose is involutive, so double
precomposition is the identity. Linearity is pointwise. With right translation
as the induced action, the equivariance identity is
`E(ρ_upper(θ_n(g)) f) = ρ_opposite(g) E(f)`: evaluation of its two sides at `x`
gives `f(θ_n(x) * θ_n(g))` and `f(θ_n(x * g))`. Multiplicativity proves equality.
These properties are the fields of the actual `Representation.Equiv`.

## Covariance from the actual matrix and normalization definitions

`GeneralLinear.BlockShape.oppositeToUpperInverseTranspose` is an actual group
equivalence from the opposite parabolic to the upper parabolic. Both its maps
are the restriction of inverse transpose. Membership follows from
`inverseTranspose_mem_oppositeParabolic_iff` and involutivity, and its group laws
are inherited from the matrix automorphism.

The lemma `leviProjection_oppositeToUpperInverseTranspose` proves at each block
index `i` that

```text
leviProjection(θ_n(q))(i) = θ_(B.size i)(oppositeLeviProjection(q)(i)).
```

Its proof applies the lower Levi projection's inverse law and then evaluates
matrix entries. Both sides have entry `(a,b)` equal to the `(B.index i b,
B.index i a)` entry of `q⁻¹`. This derives the geometric compatibility from the
published diagonal-block definitions.

`TopologicalData.determinantNorm_inverseTranspose` uses `Matrix.det_transpose`
and the determinant homomorphism's inverse law, followed by the genuine
normalized absolute value on units. Thus
`determinantNorm(θ_r(g)) = determinantNorm(g)⁻¹`.
`leviModulus_inverseTranspose` substitutes this identity into the explicit
product over pairs `i < j`. Each quotient of determinant powers inverts; the
finite product therefore inverts. The proof does not permute its indices.
`leviHalfModulus_inverseTranspose` applies the homomorphisms on units induced by
the canonical nonnegative square root and the complex embedding. Both preserve
inversion. The derived law
`parabolicHalfModulus_oppositeToUpperInverseTranspose` identifies the positive
upper half modulus of `θ_n(q)` with the opposite half modulus of `q`.

`BlockShape.blockTensor_inverseTranspose` is an equality of linear maps on the
entire actual `PiTensorProduct` carrier. It unfolds the factorwise external
tensor action: applying the original factors to inverse-transposed blocks is
definitionally the same as applying the pulled-back factors to the original
blocks. `blockTensor_leviProjection_inverseTranspose` combines this fact with
the geometric projection law. Finally `inverseTransposeProductInducing` combines
the tensor and half-modulus equalities into equality of the full normalized
inducing linear maps. This equality proves covariance of precomposition. None
of these identities is a premise to the public constructor.

## Uniform open right stabilizers

The reusable helper `Induction.precomposeSmoothFunction` takes a bicontinuous
automorphism `θ : G ≃ₜ* G`, an actual subgroup equivalence `e : Q ≃* P` satisfying
`e(q) = θ(q)` in `G`, and compatible inducing representations. It sends a smooth
`P`-covariant function `f` to `f ∘ θ`. Covariance uses multiplicativity and the
matching inducing actions.

A smooth induced function comes with one open subgroup `K` fixing the whole
function under right translation. The helper constructs the actual open
subgroup `K.comap θ.toMonoidHom θ.continuous`. For every element `k` of this
comap and every `x`,

```text
(f ∘ θ)(x * k) = f(θ(x) * θ(k)) = f(θ(x)).
```

Here `θ(k) ∈ K`, so the same original uniform stabilizer law applies for every
`x`. The inverse helper uses the comap under `θ.symm`, whose continuity is part
of the supplied bicontinuous automorphism. This constructs uniform open
stabilizers in both directions, without replacing smoothness by pointwise local
constancy.

`Induction.precomposeSmoothInducedEquiv` packages these maps as an equivalence
from the original smooth induced action pulled back by `θ` to the target smooth
induced action. It proves pointwise additivity and scalar compatibility, the
two inverse identities, and ambient equivariance. Its `_eval` and `_symm_eval`
laws expose evaluation. Its `_stabilizer` and `_symm_stabilizer` laws give the
uniform stabilizer calculation in each direction for any chosen original open
stabilizer.

The two specialized laws
`inverseTransposeProductToOppositeEquiv_stabilizer` and
`inverseTransposeProductToOppositeEquiv_symm_stabilizer` apply these facts to the
public p-adic constructor. In both laws the transported open subgroup is the
comap under the continuous `θ_n`, because this automorphism equals its inverse.

## Scope, edge cases and provenance

All statements quantify over every natural rank and every block shape, including
rank zero and the empty block family. The matrix proofs use universal entry
identities and never choose an index. The tensor equality uses the actual
indexed tensor map, including the empty tensor. Modulus inversion uses finite
products, including empty products. No nonempty, positive-rank, irreducibility,
admissibility, finite-length or classification hypothesis is introduced.

This is an internal construction from the published modules
`Group.GL.Maps`, `Group.GL.ReverseBlocks`, `Group.GL.OppositeBlocks`,
`Group.GL.BlockModulus`, `Representation.Induction.Definitions`,
`Representation.Induction.BlockFactors`, `Representation.Induction.OppositeParabolic`
and `Representation.Tensor.Finite`, together with Mathlib's determinant,
homomorphism and unit laws. The continuous-comap method follows the existing
`Representation.Smooth.Transfer.PullbackProof` approach to smooth vectors.
The square-root calculation unfolds the existing positive character into its
unit homomorphisms. No new claim about original literature is made.

This module implements neither opposite-to-upper block reversal nor tensor
reindexing, determinant twists or finite-order clauses. It supplies the
inverse-transpose-to-opposite transport that can be composed with those separate
constructions. It changes no existing Library pair.
