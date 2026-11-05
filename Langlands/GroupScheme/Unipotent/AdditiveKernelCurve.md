# Additive curves in separated-variable polynomial kernels

Author: Worker 864.

This is a derived polynomial input to the reverse unipotent woundness
criterion. It implements the degree-reduction argument in
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Lemma B.1.7, printed pp.563–564, one-based PDF pp.589–590. Registered
source: `conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The internal coordinate formulas make the source's triangular changes
explicit. The final conclusion extracts an additive polynomial curve;
it does not state the source's stronger coordinate-factor conclusion.

Let `k` be any field and `ι` any finite index type. Their universes are
independent. Each `f i` is a univariate additive polynomial, where the
published predicate `OneDimensional.IsAdditive` expresses the polynomial
identity in two variables, and consequently additivity on every
commutative `k`-algebra. The final theorem `exists_additive_kernel_curve`
says that, if a tuple `φ` satisfies

`∑ i, (f i).comp (φ i) = 0`

and some `φ i` has positive degree, then the same equation admits a
nonzero tuple `ψ` whose coordinates are additive polynomials. Here
nonzero means `ψ ≠ 0` as a function. Because additive polynomials have
zero constant coefficient, such a tuple has a positive-degree
coordinate. The field need not be infinite or perfect, and may have any
characteristic. There is no nonemptiness assumption on `ι`; the
nonconstant-curve premise supplies it when needed.

`polynomialShear j q` sends a tuple `φ` to the tuple with coordinates

- `(q j).comp (φ j)` at `j`;
- `φ i + (q i).comp (φ j)` at every other index.

When `q j = C a * X` with `a ≠ 0`, `polynomialShearInverse` is an
explicit two-sided inverse: divide coordinate `j` by `a`, and subtract
`q i` evaluated there from each other coordinate. The shear preserves
additive tuples. Both directions preserve zero constant coefficients,
and both send zero to zero when the `q i` are additive.
`sum_comp_polynomialShear` proves that substituting the shear in the
separated-variable equation replaces only `f j`, by
`∑ i, (f i).comp (q i)`.

The degree-reduction lemmas use an exponential characteristic `p` and
write each nonzero additive coordinate degree as `p ^ m i`, using the
published one-dimensional degree theorem. Given a nonzero principal-part
zero `b`, choose `j` of maximal `m j` among the nonzero coordinates of
`b`, and put

`q i = C (b i) * X ^ (p ^ (m j - m i))`.

For a nonzero `b i`, maximality shows that the substituted term has
degree `p ^ m j` and its coefficient at that degree is
`(f i).leadingCoeff * b i ^ (f i).natDegree`. A zero `b i` contributes
the zero polynomial. The principal-part equation cancels the sum's
coefficient at degree `p ^ m j`, while its degree is bounded by that
number. Since this number is positive, the degree is strictly smaller
than the old degree of `f j`. Also `q j = C (b j) * X` with `b j ≠ 0`,
so the shear is invertible.

The private induction helper uses strong induction on the sum of the
coordinate degrees. If some `f j` is zero, the tuple with `X` at `j`
and zero elsewhere supplies the desired curve. Otherwise the published
principal-part extraction theorem applied to the pointed input curve
provides `b`. The shear strictly reduces the degree sum. Applying its
inverse to the input curve preserves pointedness and nonzeroness, so
induction applies to the transformed equation. Applying the shear to
the resulting additive curve returns a nonzero additive curve in the
original kernel. `exists_additive_kernel_curve_of_pointed` exposes this
case. The final theorem subtracts each original coordinate's constant
coefficient. The subtracted constant tuple also satisfies the kernel
equation, by evaluating the original equation at zero. Additivity then
preserves the relation, and a nonconstant coordinate prevents the
normalized tuple from vanishing.

The printed source assumes positive characteristic. This development
uses `ringExpChar k`, including `p = 1` in characteristic zero; the
same degree classification, monomial shears and induction remain valid.
This characteristic-zero extension and the explicit polynomial
interfaces are derived content.

No coordinate presentation for an arbitrary group scheme, closed
immersion of the extracted curve, vector-factor decomposition, or full
woundness equivalence is asserted here. Those require separate
structural and actual-scheme arguments.
