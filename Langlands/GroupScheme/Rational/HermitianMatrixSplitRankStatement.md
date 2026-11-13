# Split rank from an actual all-test Hermitian matrix presentation

`Langlands.GroupScheme.HermitianMatrixSplitRankStatement` is an unproved
proposition. It identifies the split rank of a group scheme already
presented as a special unitary matrix functor with the attained maximum
dimension of its actual totally isotropic submodules. It does not
construct such a presentation from a Tits index.

## Inputs and scalar convention

The fields `K L : Type u` have a separable quadratic extension structure.
Write `c = SU3Root.fieldInvolution K L`. The natural representation has
dimension `n + 1`, where `n ≥ 2`. The group scheme `G` over `Spec K` is
affine and locally of finite type. An actual invertible matrix

```text
J ∈ GL_(n+1)(L),   (J.map c.bar).transpose = J
```

is supplied. Invertibility is carried by the matrix unit itself. On
`V = Fin (n + 1) → L`, the associated full pairing in the convention of
the Hermitian coordinate lemmas is

```text
h_J(a,b) = dotProduct (fun i => c.bar (b i)) (J.mulVec a)
         = ∑ i, c.bar (b i) * ∑ j, J i j * a j.
```

Thus the first vector is linear and the second conjugate-linear. The
Hermitian matrix equation gives `c.bar (h_J(a,b)) = h_J(b,a)`.
Total isotropy of a submodule means vanishing for every ordered pair
of its elements, not just self-pairing vanishing.

## Actual all-test presentation

For every `T : Over (Spec K)`, write

```text
A_T = SpecialLinear.WeilRoot.tensorAlgebra K L T,
c_T = SU3Root.SchemeModel.coefficientInvolution K L T,
J_T = J.map (algebraMap L A_T).
```

The supplied data are monoid homomorphisms
`ρ T : (T ⟶ G.X) →* GL_(n+1)(A_T)` with three properties:

1. Each `ρ T` is injective.
2. A matrix `g` is in its range exactly when
   `(g.map c_T.bar).transpose * J_T * g = J_T` and
   `Matrix.GeneralLinearGroup.det g = 1`.
3. For every test morphism `a : T' ⟶ T` and every point `x`, the matrix
   of `ρ T' (a ≫ x)` is the entrywise image of `ρ T x` under
   `SpecialLinear.WeilRoot.tensorMap K L a`.

These are the actual determinant-one isometry equations over every
test scheme, with the existing tensor coefficient involution and
restriction maps. In particular, the hypothesis is stronger than an
abstract identification of `K`-rational points. The predicate is stated
directly with existing Library names so it can be used independently
of any later packaging of general Hermitian matrix functors.

## Conclusion

The proposition asserts both of the following:

- There is an actual totally isotropic `L`-submodule `W` of `V` with
  `(finrank L W : ℕ∞) = splitRank G`.
- Every actual totally isotropic `L`-submodule `W` of `V` has
  `(finrank L W : ℕ∞) ≤ splitRank G`.

Together they say that the split rank is precisely the attained
maximum isotropic dimension, the usual Witt index. The maximum is
expressed directly through actual submodules; no decomposition,
maximality witness, or comparison theorem is stored in the input
data. The cast is explicit because the Library defines `splitRank`
in `ℕ∞` as the supremum of dimensions of actual closed split subtori.
The attained equality also asserts finiteness of that split rank.

## Source and derived formulation

The source is J. Tits, *Classification of algebraic semisimple groups*
(1966), Table II, printed pp.54–55 / PDF pp.59–60, source
`tits-1966-classification-algebraic-semisimple`, PDF SHA-256
`962203f9e47e9c3c43fc1049a38e28c751aa42beb7ee5250a095a132e215a5d4`.
The explanation on printed p.54 identifies `r` with relative rank. The
outer-type-A entry on printed p.55 describes a special unitary group of
a nondegenerate Hermitian form of index `r`; when the division algebra
has degree one, this is a Hermitian form over the quadratic extension.
The source is stated over general fields without a characteristic
restriction.

This proposition is a derived scheme formulation of that rank formula
for degree one and absolute rank at least two. Tits explicitly describes
rational points of one representative per strict isogeny class. The
present statement instead supplies the full natural matrix presentation
on every test scheme as a hypothesis and uses the Library's actual
closed-split-subtorus definition of rank. The proof must justify this
comparison; no result about an arbitrary group's Tits index or an
unconstructed scheme model is inferred from rational points.

There is no assumption that the rank or Witt index is one, no
anisotropic-middle hypothesis, and no use of a rank-one classification
or Kneser–Tits consumer. The later outer-A identification will consume
this general rank comparison after obtaining its actual all-test
Hermitian presentation.
