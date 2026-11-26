# Diagonal sign changes on a Hilbert space

`Langlands.Renard.CompactRepresentation.continuousUnitaryNonsmoothCounterexample`
proves [`ContinuousUnitaryNonsmoothCounterexampleStatement`](ContinuousUnitaryNonsmoothCounterexampleStatement.md).
The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, IV.2.2, opening paragraph, printed p. 97
(PDF p. 103). Registered source `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The book asserts that for a t.d. group continuous unitary representations
are in general not smooth, and gives no example. The proof supplies an
explicit one.

## The group and the Hilbert space

The group is `ℕ → ℤˣ`, the product of countably many copies of the group of
integer units, which has the two elements \(1,-1\). Each factor carries
Mathlib's topology on units, which is discrete because `ℤ` is discrete; the
group carries the product topology. The Hausdorff, totally disconnected and
locally compact instances required by the statement are Mathlib's instances
for this product. For local compactness the proof first records that `ℤˣ` is
finite (it is the image of `Bool`), so each factor is compact; by Tychonoff
the product is in fact compact.

The Hilbert space is `lp (fun _ : ℕ => ℂ) 2`, that is \(\ell^2(\mathbb N,\mathbb C)\)
with Mathlib's inner product. A sign sequence \(g\) acts by
\((g\cdot v)_n = g_n v_n\). Multiplication by a sign preserves each coordinate
norm, so the image is again square-summable. The coordinate formulas give a
linear map for each \(g\), the identity for \(g=1\), and composition for products,
so this is a `Representation ℂ (ℕ → ℤˣ) (lp (fun _ : ℕ => ℂ) 2)`.

## Preservation of the inner product

The inner product on \(\ell^2\) is the sum of the coordinate inner products
(`lp.inner_eq_tsum`). Multiplying both entries of a coordinate by the same sign
\(\pm 1\) leaves its inner product unchanged, so the sums agree term by term.

## Strong continuity

Fix \(v\), a sign sequence \(g\) and \(\varepsilon>0\). By `lp.hasSum_single`, the
finite truncations of \(v\) converge to \(v\), so there is a finite set \(s\) of
coordinates whose truncation \(w\) lies within \(\varepsilon/2\) of \(v\). The
set of sign sequences that agree with \(g\) at every coordinate of \(s\) is a
neighbourhood of \(g\), being a finite intersection of preimages of points
under the continuous coordinate projections into a discrete space. For \(h\) in
it, \(h\cdot w = g\cdot w\). Since each element acts isometrically (the linear map
preserving the inner product is an isometry), \(\|h\cdot v - g\cdot v\| \le
\|h\cdot v - h\cdot w\| + \|g\cdot w - g\cdot v\| = 2\|v-w\| < \varepsilon\).

## A vector fixed by no open subgroup

The vector \(x\) with coordinates \(x_n = (1/2)^n\) lies in \(\ell^2\) because the
squared norms form the geometric series \(\sum_n (1/4)^n\). Suppose an open
subgroup \(K\) fixes \(x\). Let \(f_n\) be the sign sequence equal to \(-1\) at
coordinate \(n\) and to \(1\) elsewhere. The sequence \(f_n\) converges to the
identity in the product topology, since every fixed coordinate of \(f_n\) equals
\(1\) once \(n\) exceeds it. As \(K\) is an open neighbourhood of the identity,
some \(f_n\) lies in \(K\). Comparing coordinate \(n\) of \(f_n\cdot x = x\) gives
\(-x_n = x_n\), contradicting \(x_n \ne 0\). Hence the representation is not
smooth, and applying the negated universal implication of the statement to this
group, space and representation gives the theorem.
