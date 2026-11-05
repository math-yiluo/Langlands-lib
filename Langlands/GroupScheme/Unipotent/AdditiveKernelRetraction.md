# Split additive curves in separated-variable kernels

Author: Worker 864.

This derived polynomial input strengthens `AdditiveKernelCurve` by tracing a
left inverse through its degree-reduction argument. Its source is
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Lemma B.1.7 and proof, printed pp.563–564, one-based PDF pp.589–590.
Registered source: `conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The source constructs a vector coordinate factor in the kernel. The internal
predicate here records an additive polynomial section and an additive
polynomial retraction, which can be obtained by retaining one coordinate
of the source's composite inverse. The evaluation lemmas are direct
consequences of the polynomial identities.

Let `k` be any field and `ι` any finite index type, with independent
universes. `HasSplitAdditiveKernelCurve f` is the proposition that there
are tuples `ψ r : ι → k[X]` such that every coordinate of both tuples is
additive and

- `∑ i, (f i).comp (ψ i) = 0`;
- `∑ i, (r i).comp (ψ i) = X`.

Additivity uses the published `OneDimensional.IsAdditive` polynomial
identity, so it holds on every commutative coefficient algebra. The second
identity is a polynomial left inverse. In particular, it ensures that the
section remains injective after evaluation on every commutative
`k`-algebra, including finite fields and rings with nilpotents.

`hasSplitAdditiveKernelCurve_of_pointed` takes additive `f i` and a nonzero
tuple `φ` with zero constant coefficients and
`∑ i, (f i).comp (φ i) = 0`, and proves this predicate.
`hasSplitAdditiveKernelCurve_of_nonconstant` replaces pointedness and
nonzeroness by the assumption that some `φ i` has positive degree. Neither
the field nor the finite index type has any additional restriction. The
empty index case has an impossible input-curve premise. There is no
perfectness, infinitude, or characteristic assumption.

The helper `polynomialShearInverseCoordinates j a q` has coordinate
`C a⁻¹ * X` at `j`, and `-(q i).comp (C a⁻¹ * X)` elsewhere.
`polynomialShearInverse_eq_shear` expresses the existing inverse shear as
the shear with these coordinates. This equality is valid for arbitrary
`a` and `q`; the two-sided inverse identities used later additionally
require `a ≠ 0` and `q j = C a * X`. When all `q i` are additive, all
inverse coordinates are additive by composition, scalar multiplication,
and negation.

The private proof uses strong induction on the sum of the coordinate
natural degrees, as in `AdditiveKernelCurve`. If some `f j = 0`, take both
`ψ` and `r` to have coordinate `X` at `j` and zero elsewhere. Their
composition sum is `X`, and the kernel sum vanishes. Otherwise the
pointed nonzero input curve supplies a nonzero principal-part zero.
The existing degree-reducing shear replaces `f j` by
`g = ∑ i, (f i).comp (q i)`, with strictly smaller degree, and leaves all
other equation coordinates unchanged. Applying the inverse shear to the
input curve preserves its zero constant coefficients and nonzeroness.
The substitution identity proves its transformed kernel relation, so
induction gives an additive section `ψ'` and an additive row `r'` for the
transformed equation.

Apply the forward shear to `ψ'` to obtain `ψ`. To transform the retraction,
write the inverse shear using the inverse coordinates above and replace
only row coordinate `r' j` by the sum of the `r' i` composed with those
inverse coordinates. The substitution identity then identifies the new
row on `ψ` with `r'` on the inverse shear of `ψ`, which equals `r'` on
`ψ'`. Its value is `X` by induction. The same substitution identity gives
the original kernel relation. Every coordinate remains additive.
The nonconstant theorem first applies the existing curve-extraction
theorem to obtain a nonzero additive curve, whose constant coefficients
are zero, and then applies the pointed theorem.

The source assumes positive characteristic. The implementation chooses
`ringExpChar k`; exponential characteristic `1` covers characteristic
zero, where the imported degree theorem says that nonzero additive
polynomials have degree one. The same degree induction works. This
characteristic-zero case and the explicit retraction interface are
derived content.

For a commutative `k`-algebra `R` in a third independent universe,
`sum_aeval_aeval` identifies evaluation of a composition sum with
`∑ i, aeval (aeval x (ψ i)) (r i)` by preservation of finite sums and
`aeval_comp`. `sum_aeval_aeval_eq_zero` evaluates the kernel relation.
`aeval_tuple_leftInverse` evaluates the retraction identity to show that
the row `y ↦ ∑ i, aeval (y i) (r i)` is a left inverse to
`x ↦ (i ↦ aeval x (ψ i))`. `aeval_tuple_injective` follows from this
left inverse. These evaluation lemmas do not require additive coordinates;
the identities alone suffice.

This unit does not construct an actual group-scheme morphism or prove its
closed-immersion property, an actual vector-factor decomposition, a
coordinate presentation for arbitrary group schemes, or the full
woundness criterion. Those comparisons and structural results remain
separate obligations.
