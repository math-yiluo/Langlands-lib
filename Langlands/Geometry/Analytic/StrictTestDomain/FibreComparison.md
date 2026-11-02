# Fibres of strict-test representations

Author: Worker 1010.

Fix a normed field K with ultrametric absolute value. Presented strict
affinoid algebras over K are the published `PresentedStrictAffinoidAlgebra K`.
Bounded maps are the published `BoundedAlgHom K`. For a point x of a Banach
spectrum, `CompletedResidueField K x` is the published completed residue field
H(x), and `completedResidueMap K x` is the published bounded map from the
algebra to H(x). Its norm at a is the value `x a`
(`norm_completedResidueMap`).

Most results below assume the published proposition
`Langlands.Analysis.NonarchimedeanCompletedTensorStatement` at universe u as a
hypothesis `hT`. They do not prove it. They also assume that the
absolute value of K is nontrivial, as a hypothesis `hK : ∃ c : K, 1 < ‖c‖`.

## Tensor products of normed field extensions

- `FieldTensor.exists_embedding` restates `hT` for normed fields. Let F be a
  complete ultrametric normed field with an element of norm greater than one.
  Let E and E' be ultrametric normed fields with F-algebra structures whose
  algebra maps preserve norms. Then there are a complete ultrametric normed
  commutative F-algebra W and an injective F-algebra map τ from `E ⊗[F] E'` to
  W with `‖τ (e ⊗ e')‖ ≤ ‖e‖ * ‖e'‖`. The proof builds the nontrivially normed
  field and normed algebra structures from these hypotheses and applies `hT`.
- `FieldTensor.norm_le_of_tmul_eq`: let τ be an F-algebra map from
  `E ⊗[F] E'` to a nontrivial normed ring W with this bound on pure tensors.
  If `h ⊗ 1 = 1 ⊗ h'`, then `‖h‖ ≤ ‖h'‖`. No point of W is used. For h ≠ 0,
  `1 = τ(h⁻¹ ⊗ 1) * τ(1 ⊗ h')`. Hence `1 ≤ ‖1_W‖ ≤ ‖h‖⁻¹ * ‖h'‖`.
- `FieldTensor.mem_range_of_tmul_eq`: for a field extension E of F, if
  `h ⊗ 1 = 1 ⊗ h` in `E ⊗[F] E`, then h lies in the image of F. Suppose h is
  not in the F-span of 1. Then there is an F-linear functional f on E with
  `f 1 = 0` and `f h ≠ 0`. Apply `f ⊗ id` followed by `F ⊗[F] E ≅ E` to both
  sides. The left side gives `f h • 1` and the right side gives 0, which is a
  contradiction.

## Common denominators in residue fields

`BanachSpectrum.exists_common_denominator`: let x be a point of the Banach
spectrum of a normed commutative K-algebra A, let `z : Fin m → H(x)` and let
ε > 0. Then there are g in A and `f : Fin m → A` with `x g > 0` and

  ‖g(x) · z k - f k (x)‖ < ε · x g for every k.

Here `g(x)` is `completedResidueMap K x g`. The image of the published
residue fraction field is dense in H(x)
(`denseRange_residueCompletionMap`). So choose fractions w k at distance less
than ε from z k. Mathlib's `IsLocalization.exist_integer_multiples_of_finite`
gives a common denominator b in the published residue domain `A / ker x` with
`b · w k = r k`. Then lift b to g and r k to f k in A. The element b is a
nonzero divisor, so `x g > 0`. Then `f k (x) = g(x) · w k`. The estimate
follows because the norm of H(x) is multiplicative.

## The fibre embedding

Let `i : P → Q` be a bounded map of presented strict affinoid algebras. Let y
be a point of the spectrum of Q, and let x be a point of the spectrum of P with
`hy : comap i y = x`.

- `StrictTestDomain.fibreEmbedding i hy : H(x) → H(y)` is the published
  `completedResidueLift` of `completedResidueMap K y ∘ i`. This map is
  contractive with respect to x because y restricts to x.
- `StrictTestDomain.norm_fibreEmbedding`: it preserves norms, by the published
  `isometry_completedResidueLift`.
- `StrictTestDomain.fibreEmbedding_map`: it sends `a(x)` to `(i a)(y)` for a
  in P.
- `StrictTestDomain.fibreAlgebra i hy` is the `Algebra H(x) H(y)` structure
  given by this embedding.

## Temkin's Proposition 2.1

The remaining results assume that K is complete. They also assume that i
represents a subset U of the spectrum of P for strict tests, in the sense of
the published `StrictTestDomain.Represents`.

- `StrictTestDomain.tmul_eq_of_represents`: let y and y' be points of the
  spectrum of Q over the same point x. Take any `Algebra H(x) H(y)` and
  `Algebra H(x) H(y')` instances whose algebra maps equal the fibre
  embeddings. Then for every q in Q,

    q(y) ⊗ 1 = 1 ⊗ q(y') in H(y) ⊗[H(x)] H(y').

  Proof. A point of K of norm greater than one gives an element of H(x) of
  norm greater than one. By `FieldTensor.exists_embedding` and the isometric
  fibre embeddings, there is an injective τ from this tensor product to a
  complete ultrametric normed algebra W. W becomes a normed K-algebra through
  H(x). The maps `u q = τ(q(y) ⊗ 1)` and `v q = τ(1 ⊗ q(y'))` are bounded
  K-algebra maps from Q to W, with bound one. They agree after composition
  with i, because for a in P both `(i a)(y) ⊗ 1` and `1 ⊗ (i a)(y')` equal
  the image of `a(x)` in the tensor product. By the epimorphism property
  `StrictTestDomain.eq_of_comp_eq` of the module `PairTest`, `u = v`. Injectivity of τ gives the claim.
- `StrictTestDomain.comap_injective_of_represents`: restriction of points
  along i is injective. Suppose y and y' restrict to the same point. For each
  q, the previous result with the fibre algebras gives `q(y) ⊗ 1 = 1 ⊗ q(y')`.
  The tensor product of two field extensions is nontrivial (Mathlib's
  `Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain`), so
  W is nontrivial, and `FieldTensor.norm_le_of_tmul_eq` gives `y q ≤ y' q`.
  By symmetry the two points are equal.
- `StrictTestDomain.mem_range_of_represents`: for y over x and q in Q, the
  value `q(y)` lies in the image of the fibre embedding of H(x). This is the
  case `y = y'` of the tensor identity together with
  `FieldTensor.mem_range_of_tmul_eq`.
- `StrictTestDomain.exists_fraction_approximation`: for a point y of the
  spectrum of Q, a finite family `t : Fin m → Q` and ε > 0, there are g in P
  and `f : Fin m → P` with `(comap i y) g > 0` and

    y (i g * t k - i (f k)) < ε · (comap i y) g for every k.

  Write each `t k (y)` as the image of some z k in H(x), where x is the
  restriction of y. Apply `exists_common_denominator` at x, then transport
  the estimate through the isometric fibre embedding.

## Provenance

Temkin, "A new proof of the Gerritzen–Grauert theorem", Math. Ann. 333
(2005), Proposition 2.1 states the following for a monomorphism of affinoid
spaces `ϕ : Y → X` and a point y of Y with `x = ϕ(y)`. The fibre `ϕ⁻¹(x)` is
`{y}`, and `H(x) → H(y)` is an isomorphism. The Lean results are versions of
these statements for maps representing a subset for strict tests; such maps
are epimorphisms of algebras towards complete targets (`eq_of_comp_eq`), the
algebraic form of Temkin's monomorphism hypothesis.

- Injectivity is `comap_injective_of_represents`.
- The isomorphism of completed residue fields is replaced by two weaker
  facts. Every value `q(y)` lies in the image of H(x)
  (`mem_range_of_represents`). These values are approximated by fractions
  with a common denominator (`exists_fraction_approximation`).

The proof follows Temkin's tensor argument. The completed tensor product
`H(y) ⊗̂_{H(x)} H(y')` is replaced by an injective target given by the
assumed statement `NonarchimedeanCompletedTensorStatement` (Gruson–van der
Put, Lemma 5.2(2)). The universal property is applied through the pair test
algebra. The field-theoretic lemmas and the common-denominator lemma are
internal supporting results.
