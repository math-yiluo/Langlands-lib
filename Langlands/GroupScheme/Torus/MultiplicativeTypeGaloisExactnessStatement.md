# Finite Galois character exactness for groups of multiplicative type

This file declares
`Langlands.GroupScheme.MultiplicativeTypeGaloisExactnessStatement`.
It is a proposition awaiting proof.

## Actual groups and splitting data

Let `L/k` be a finite Galois extension of fields in universe `u`. Let `N`, `E`
and `Q` be actual commutative group schemes over `Spec k`, and let

```text
i : N → E,        q : E → Q.
```

The hypotheses supply finitely generated abelian groups `M_N`, `M_E`, `M_Q`
and actual isomorphisms of commutative group schemes

```text
N_L ≅ D_L(M_N),   E_L ≅ D_L(M_E),   Q_L ≅ D_L(M_Q).
```

Here `D_L(M)` is the published spectrum-of-group-algebra construction
`Diagonalizable.groupScheme`. The common extension and the splitting models
are explicit hypotheses. Finite generation ensures finite type; the models
also ensure that the three groups are affine and of multiplicative type
after descent. The statement adds no smoothness, connectedness, freeness,
characteristic or positive-rank hypothesis. Torsion, including characteristic
torsion, is allowed in every model.

## The equivalence

Write `X(H_L) = characterLattice H_L = Hom(H_L, Gm_L)`. These are the actual
characters with their additive group law, whose addition is pointwise
multiplication of characters. Base change is the published scheme pullback
functor `BC = CommGroupScheme.baseChange (algebraBaseMap k L)`. Define

```text
pullQ : X(Q_L) → X(E_L),    χ ↦ q_L ≫ χ,
pullN : X(E_L) → X(N_L),    χ ↦ i_L ≫ χ.
```

Categorical composition is written in diagrammatic order. Bilinearity of
composition in `CommGroupScheme` makes these functions additive and hence
`ℤ`-linear. The declaration uses their underlying functions for the
injectivity, exactness and surjectivity predicates.

The left side says that `i` is a closed immersion and that `q` satisfies
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q`, after passing to
the underlying group-scheme morphisms. By the published definitions this means

- the underlying morphism of schemes of `q` is flat, surjective and locally
  of finite presentation;
- the range of its actual scheme-theoretic kernel inclusion equals the
  range of `i` as subgroup functors on every test scheme over `Spec k`.

Together with the closed immersion, this identifies `N` with the full
scheme-theoretic kernel and says that `Q` is the represented fppf sheaf
quotient. Surjectivity on each original test scheme's group of points is not
required. In particular, nonreduced tests and nonsmooth kernels are retained.

The right side says that the sequence

```text
0 → X(Q_L) --pullQ→ X(E_L) --pullN→ X(N_L) → 0
```

is short exact and that both maps commute with the canonical
`characterLattice.galoisRepresentation k L` actions of `Gal(L/k)`.
Concretely, `Function.Exact pullQ pullN` means that, for every character
`χ` of `E_L`, `pullN χ = 0` if and only if `χ` is in the image of `pullQ`.
The outer conditions are injectivity of `pullQ` and surjectivity of `pullN`.
Thus the right side is exactness of the actual character modules with their
Galois actions. The actions come from transport of the actual base-changed
groups, rather than from independently supplied representations.
Equivariance records naturality of character pullback for the given
ground-field morphisms.

No separate hypothesis `i ≫ q = 0` is imposed: the kernel condition on the
left and character exactness on the right enforce the trivial composite.
For example, the scope includes the characteristic-`p` Kummer sequence with
kernel `μ_p`; its character sequence is multiplication by `p` on `ℤ`
followed by the quotient to `ℤ/pℤ`. No primitivity restriction is imposed.

## Source and derived formulation

The source is the registered `milne-2017-algebraic-groups`, J. S. Milne,
*Algebraic Groups* (2017), SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The relevant original passages are:

- Definition 5.5, printed p.99 (PDF p.115), defines a quotient map by
  faithful flatness and explicitly distinguishes it from surjectivity on
  each algebra's points.
- Theorem 5.39 and Definition 5.41, printed p.108 (PDF p.124), give the
  faithfully flat / closed immersion factorization and the meaning of
  an embedding. Proposition 5.43, printed p.109 (PDF p.125), identifies
  quotient maps with locally liftable points and with injectivity of the
  structure-sheaf map.
- Theorem 5.62 and Corollary 5.63, printed p.115 (PDF p.131), give the
  abelian categories of commutative and affine commutative algebraic groups.
  Paragraph 5.73, printed p.118 (PDF p.134), describes the represented
  quotient in terms of sheaves and its kernel.
- Theorem 12.9(b) and its proof, printed pp.233–234 (PDF pp.249–250),
  identify short exact sequences of finitely generated abelian groups with
  the reversed short exact sequences of diagonalizable groups.
- Theorem 12.23 and its proof, printed p.240 (PDF p.256), extend this
  correspondence to groups of multiplicative type and continuous absolute
  Galois modules. Its convention for the action is given on printed p.239
  (PDF p.255). The proof of Corollary 12.25, printed p.240, explicitly
  uses a common finite Galois splitting extension.

This is a derived formulation at a specified finite splitting extension.
Over `L`, the supplied models reduce the equivalence to Theorem 12.9(b).
Their character groups remain unchanged under further separable extension,
so this is the character exactness of Theorem 12.23, with its action
factoring through `Gal(L/k)`. Closed immersion, faithful flatness and the
kernel identification descend along the faithfully flat field extension.
Morphisms between the affine finite-type groups here are locally of finite
presentation over the noetherian field base, so the additional explicit
local-finite-presentation clause in the Library's fppf predicate imposes
no stronger restriction. Equality of the represented subgroup functors is
the all-test form of the kernel identification.

The original passages were read, together with the complete retained official
2017 errata snapshot of 2 November 2026. No correction there affects these
passages. This statement supplies a finite-Galois exactness interface for
given actual groups and morphisms. It does not construct an assembled
absolute-Galois categorical equivalence, or provide a proof of this
proposition. Those remain separate mathematical obligations.
