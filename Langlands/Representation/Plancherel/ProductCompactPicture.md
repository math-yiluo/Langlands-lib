# Actual product induction in a fixed compact picture

This module constructs `Langlands.Plancherel.productInducedCompactEquiv`.
For every unramified character, it identifies the actual normalized
product-induced coefficient space of the twisted representation with one fixed
compact section space. The equivalence intertwines the actual right action of
`K × K`. Its forward map restricts the function and retains the underlying
vectors and linear functionals; its inverse extends by normalized covariance.

The ambient group, character-index type, and coefficient-carrier universes are
independent. Representative naturality also permits a different target-carrier
universe.

## Source and provenance

The source is J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI 10.1017/S1474748003000082, VI.1, printed pp.295–296, especially p.296
(PDF pp.61–62). The registered source is `waldspurger-2003-plancherel`, with
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

Waldspurger defines the product-induced coefficient spaces using a
representation and its smooth contragredient. He identifies the spaces for its
unitary unramified twists with a fixed compact picture by restriction, and uses
that picture to define smooth families. This module supplies that comparison
on actual smooth induced functions and their actual smooth duals. The generic
subgroup formulation, its extension to all unramified characters, contraction
identity, inverse evaluation and representative naturality are derived content.
Their proofs use the canonical smooth-dual twist equivalence and the previously
constructed normalized compact restriction.

The self-twist action, its independence of an intertwiner, smooth families and
the stabilizer-invariant tensor description in VI.1 remain subsequent work.
In particular, this module does not assert that a self-twist acts trivially on
the fixed compact picture.

## Data and retained hypotheses

Let `G` be a locally compact nonarchimedean group. Let `P`, `M`, `U` be actual
subgroups with `h : IsSemidirectDecomposition P M U`. The canonical projection
`h.projection : P →* M` is used throughout. Let `K` be an actual open subgroup.
The main equivalence retains:

- closedness of `P` and `U`;
- compactness of `K`;
- the actual factorization `∀ g, ∃ p : P, ∃ k : K, g = p * k`;
- continuity of `h.projection`;
- continuity of each supplied positive character `ν i : M →* ℝ≥0ˣ`.

Here `χ : unramifiedCharacters ν` is a continuous complex-unit character
trivial on the common kernel of the `ν i`. The imported open-kernel theorem
makes its actual twist a canonical `SmoothRep`. No assumption of unitarity of
`χ` is needed for this comparison. In the reductive application the positive
characters must be specialized to the intended rational-character norms;
this module does not supply that specialization or a rational-point Iwasawa
realization.

Only nonarchimedeanness is needed for the initial tensor comparisons. The
factorization lemma is purely algebraic. The representative map on compact
sections itself does not use compactness, closedness or factorization.
No admissibility, irreducibility, second countability, compact quotient,
Hermitian structure or integration measure is required by the main comparison.

Normalization is the existing canonical full-parabolic positive Haar
half-character used by `Aubert.General.normalizedInduction`. Its compact
restriction is removed by the proved `normalizedInductionCompactEquiv`.
The comparison of that normalization with the source's Levi-inflated
normalization remains separate.

## Removing the actual smooth-dual twist

Write `Aχ` for the actual `SmoothRep` twist of `A` by `χ`. Its coefficient
tensor is `Aχ ⊗[ℂ] SmoothDual Aχ.representation`.
The imported `smoothContragredientTwistEquiv` sends a smooth functional for the
twisted action to the same underlying linear functional with the inverse
character twist of the original contragredient action. Consequently
`productCompactTwistTensorEquiv` is the linear equivalence

`Dχ : CoefficientTensor Aχ ≃ₗ[ℂ] CoefficientTensor A`

given by the identity on vectors tensored with that functional-preserving
equivalence. The pure-tensor evaluation is definitional. This is a linear
equivalence of the underlying tensors, rather than an intertwiner for the full
`M × M` action.

`productCompactTwistTensorEquiv_pairing` proves that `Dχ` preserves the full
bilinear contraction on every tensor. Tensor induction reduces this to the
unchanged functional evaluation on pure tensors and linearity on sums.
There is no conjugation in this pairing.

`productCompactTwistTensorEquiv_natural` says that `Dχ` commutes with
`coefficientTensorCongr e` after twisting a supplied actual representation
equivalence `e : A.representation.Equiv B.representation`. That transport uses
`e` on vectors and inverse pullback on smooth functionals. The proof again
uses tensor induction; on pure tensors both routes retain the same underlying
functional composed with `e.symm`.

## Compact intersection and the fixed section space

`ProductInducedCompactPicture h K A` is literally
`CompactInductionPicture (h.prod h) (K.prod K)
  (productLeviObject A A.contragredient)`.
Its functions take values in `CoefficientTensor A`, satisfy covariance for
the actual intersection of `P × P` with `K × K`, and have one open subgroup
fixing the entire function under right translation.
`productInducedCompactRepresentation` is the existing `smoothInduced`
representation on this carrier. The fixed target depends on `A`, `h` and `K`;
it does not depend on `χ`.

The private character-triviality lemma specializes
`unramifiedPullback_eq_one_of_mem_conjOpenSubgroup` to `x = 1` and the actual
projection. For every `p ∈ P ∩ K`, it proves `χ(h.projection p) = 1` from the
displayed closedness, compactness and continuity hypotheses.

`productCompactTwistInducingEquiv` proves that `Dχ` intertwines the two actual
compact-intersection actions. On a pure tensor the vector action contributes
`χ(h.projection p₁)` and the transported contragredient action contributes
`χ(h.projection p₂)⁻¹`. The two coordinates are independent. The preceding
compact-triviality lemma removes each factor separately. Tensor
extensionality then gives the bundled representation equivalence.

## Restriction, inverse and naturality

`product_compact_factorization` obtains the `P × P`, `K × K` factorization by
factoring each coordinate of `G × G`. The main
`productInducedCompactEquiv` composes:

1. `normalizedInductionCompactEquiv` for the actual product semidirect
   decomposition and the actual product subgroups;
2. smooth induction of `productCompactTwistInducingEquiv` on the intersection.

Thus, for every actual product-induced function `F` and `k ∈ K × K`,
`productInducedCompactEquiv_eval` gives

`(productInducedCompactEquiv χ A F)(k) = Dχ(F(k))`.

The inverse formula `productInducedCompactEquiv_symm_mul` states, for every
`p ∈ P × P` and `k ∈ K × K`,

`(productInducedCompactEquiv χ A).symm(f)(p*k) =
  inducingRepresentation(Aχ)(p)(Dχ.symm(f(k)))`.

Here `inducingRepresentation(Aχ)` means the actual normalized product action
displayed explicitly in Lean. The generic restriction construction proves
independence of the factorization, global smoothness and both inverse laws.
The bundled type of the main equivalence includes right `K × K` equivariance.

`productCompactRepresentativeEquiv` is pointwise `coefficientTensorCongr e`
on the fixed compact picture. Its evaluation law is definitional.
`productInducedCompactEquiv_natural` proves that actual product-induced
transport by `twistEquiv χ e` followed by compact comparison equals compact
comparison followed by this fixed representative map. Extensionality reduces
the assertion to the already proved tensor naturality at every compact point.

These are constructions and identities on the actual canonical carriers.
Smooth parameter dependence, self-twist descent, compatibility of all source
normalizations and the analytic Plancherel theorem remain distinct obligations.
