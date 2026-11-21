# Bounded character separation

`Langlands.TraceFormula.boundedCharacterSeparation` proves
`BoundedCharacterSeparationStatement` with independent universes `u`, `v`,
and `w`. [Published statement](BoundedCharacterSeparationStatement.md).

## Proof

Fix a reference index `i₀`. For a coordinate `p = (x, h)` with `h : H x`,
the proof forms `d = h + algebraMap ℂ (H x) (-χ i₀ x h)`. Thus `χ i x d`
is the difference of the two character values at `h`. Let `C` bound
`‖χ i x d‖` uniformly in `i`, put `D = C² + 1`, and choose an element `d'`
whose values are the conjugates of those of `d`. The element
`1 + algebraMap ℂ (H x) (-(D : ℂ)⁻¹) * (d * d')` then has character values
given by the real numbers

$$
q_p(i) = 1 - \frac{\lVert \chi_i(x)(d)\rVert^2}{D}.
$$

They lie in `[0, 1]`, with `q_p(i) = 1` exactly when the two values at `h`
agree. The identity `Complex.mul_conj'` accounts for the squared norm.

The finite-place tests form a submonoid of the functions `ι → ℂ` under
pointwise multiplication. For two tests, extend both families by units to
the union of their sets of places, then multiply the local elements at
each place. The resulting test has the product of the two values because
each character is multiplicative. A singleton place realizes each `q_p`,
so for any finite set `S` of coordinates and `n : ℕ`, the function
`i ↦ (∏ p ∈ S, q_p(i)) ^ n` is also a finite-place test.

Use `atTop` on `Finset (Sigma H) × ℕ`, ordered by inclusion and by the
usual order on `ℕ`. On the fibre the test is always one. Outside the fibre,
extensionality of algebra homomorphisms gives a coordinate `p` where the
values differ. Eventually `p ∈ S`, so the nonnegative test is bounded by
`q_p(i)^n`, which tends to zero. This proves pointwise convergence to the
indicator of the full fibre.

After multiplication by `c i`, the norms of the summands are bounded by
`‖c i‖`. Mathlib's `Summable.norm` gives summability of this bound using
finite real dimension of `ℂ`. Tannery's theorem,
`tendsto_tsum_of_dominated_convergence`, gives convergence of the weighted
sums to the sum of the fibre indicator times `c`. Every approximating sum
is zero by hypothesis, so uniqueness of the limit gives a zero fibre sum.
Finally `tsum_subtype` identifies the indicator sum with the subtype sum,
and `Summable.subtype` gives the required `HasSum`.

## Source correspondence

Henniart–Lemaire vary the spherical Hecke functions outside `S` in (2)
and retain terms with the same local trace functionals in (3). This
theorem supplies the separation of the absolutely summable coefficient
families in that step under the hypotheses of the published statement.
The normalized tests and limit argument above are derived for that
statement. See *Changement de base et induction automorphe pour GL(n)
en caractéristique non nulle* (2011), II.6.10, printed pp. 125–126,
especially p. 126 (PDF p. 134).

Arthur–Clozel first use finiteness at fixed level and infinitesimal
character and then apply a character-independence argument in their
Hecke setting. See *Simple Algebras, Base Change, and the Advanced Theory
of the Trace Formula* (1989), Chapter 1, Lemma 4.10, printed p. 45 (PDF p. 59).

Jacquet–Langlands' definition of an ample test subalgebra illustrates
the use of involution-closed test algebras. See *Automorphic Forms on
GL(2)* (1970), §16, preceding Lemma 16.1.1, retypeset p. 260 (PDF p. 264).
