# Local rational neighbourhoods of strictly represented subsets: proof

Author: Worker 1010.

`Langlands.Analytic.StrictTestDomain.localRationalNeighborhood` proves the
published proposition `StrictTestDomain.LocalRationalNeighborhoodStatement` at
universe `u`. Fix a complete ultrametric field K with an element of norm greater
than one, a bounded map i : P → Q of presented strict affinoid K-algebras, and a
subset U of M(P) with `Represents K i U`. Fix a point x of U. We must find
rational data whose locus lies in U and is a neighbourhood of x in U.

The proof uses the completed-tensor theorem
`Langlands.Analysis.nonarchimedeanCompletedTensor` (through the fibre comparison
results), lying over, the finiteness criterion from close approximations, and the
idempotent quotient test. It uses no reduction theory and no Weierstrass theory.

## Auxiliary results in this file

- `PresentedStrictAffinoidAlgebra.equivOfEq_coordinate`: the bounded equivalence
  induced by an equality of presentations sends coordinates to coordinates.
- `BanachSpectrum.apply_smul`: x(c • a) = ‖c‖ x(a) for a point x of the spectrum
  of a normed K-algebra.
- `StrictTestDomain.exists_comap_eq_of_finite_of_one_lt`: the published lying-over
  theorem `BanachSpectrum.exists_comap_eq_of_finite` for presented strict
  affinoid algebras, with the nontrivially normed field structure on K built
  from the hypothesis `∃ c, 1 < ‖c‖`.
- `RationalData.coordinate_castAdd` and `RationalData.coordinate_natAdd`: the
  first coordinates of the rational quotient `d.algebra` are the images under
  `d.baseMap` of the coordinates of P, and the last coordinates are the fraction
  coordinates `d.fraction j`.

## Step 1: approximating rational data (`RationalData.exists_approx_data`)

Write x = comap i y with y in M(Q); this is possible because U is the image of
the spectrum map. Let t_k be the coordinates of Q.

1. The published fibre approximation `exists_fraction_approximation` (with
   ε = 1) gives g and f_k in P with y(i g) > 0 and
   y(i g · t_k − i f_k) < y(i g) for every k.
2. Choose a in K with 0 < ‖a‖ < y(i g); a power of c⁻¹ works. Let d₁ be the
   rational data with denominator g and numerators a·1 and f_k. Its locus is
   {x' | ‖a‖ ≤ x'(g) and x'(f_k) ≤ x'(g) for all k}. The numerator a·1 never
   vanishes, so d₁ has no common zero.
3. Let G be the open set of points y' of M(Q) with ‖a‖ < y'(i g) and
   y'(i g · t_k − i f_k) < y'(i g) for all k. It contains y. If y' is in G,
   then comap i y' lies in the locus of d₁. Indeed y'(i g · t_k) ≤ y'(i g),
   because coordinates have norm at most one. The strong triangle inequality of
   spectrum points (`BanachSpectrum.isNonarchimedean`) then gives
   y'(i f_k) ≤ y'(i g).
4. The complement of G is compact, so its image under comap i is compact and
   closed. The image does not contain x, because comap i is injective
   (`comap_injective_of_represents`, Temkin's Proposition 2.1). By the rational
   neighbourhood basis (`RationalData.exists_locus_mem_nhds_subset`) there is
   rational data L whose locus is a neighbourhood of x and avoids that image.
   So every y' with comap i y' in the locus of L lies in G.
5. Take d = d₁ ∩ L (`RationalData.inter`). On the locus of d, g is positive and
   dominates every f_k. Every y' over the locus of d lies in G. Finally,
   U ∩ L.locus ⊆ d.locus ∩ U by step 3, so d.locus ∩ U is a neighbourhood of x
   in U.

## Step 2: finiteness (`RationalData.finite_comparison_of_approx`)

Let A₃ = d.algebra and B₃ = (d.pullback i).algebra, and let
i₃ = d.comparison i : A₃ → B₃ be the comparison map. Every point of M(A₃) lies
over the locus of d, so it is positive on the image of g. Hence that image is a
unit of A₃ (`isUnit_iff_forall_spectrum_ne_zero`); let v be its inverse. The coordinates of B₃
are the images of the t_k and the fraction coordinates. Take as approximations
a_k = (image of f_k)·v for the first ones, and the fraction coordinates of A₃
for the others.

- Every point of M(A₃) is at most 1 on a_k, because f_k ≤ g on the locus of d.
  It is at most 1 on the fraction coordinates, because coordinates have norm at
  most one.
- For a point y₃ of M(B₃), let y' be its restriction to Q. Then y' lies over the
  locus of d, so y' is in G. The identity
  (t_k − i₃ a_k)·(i g) = i g · t_k − i f_k in B₃ gives
  y₃(t_k − i₃ a_k) < 1. For the fraction coordinates the difference is zero
  (`comparison_fraction`).

The finiteness criterion `finite_of_spectrum_coordinate_sub_lt_one` then shows
that i₃ is finite.

## Step 3: cutting out U (`RationalData.exists_locus_eq_inter_of_finite`)

The comparison map i₃ represents U₃, the inverse image of U in M(A₃)
(`RationalData.represents_comparison`). Since i₃ is finite, lying over shows
that every point of M(A₃) killing the kernel of i₃ lies in U₃. The quotient test
`exists_idempotent_of_zeroLocus_subset` gives an idempotent e of A₃ with
U₃ = {x₃ | x₃(e) = 0}. Every spectrum value of e is 0 or 1.

Fractions with powers of the denominator g₃ of d are dense in A₃
(`RationalData.dense_fractionSubalgebra`). So there are z, r and q with
g₃^r z = q in A₃ (images of elements of P) and ‖e − z‖ < ‖c‖⁻¹. Replacing r by
r + 1 and q by g₃ q makes the exponent positive. For points x₃ of M(A₃), the
strong triangle inequality gives:

- x₃(e) = 0 implies x₃(z) < ‖c‖⁻¹;
- x₃(z) ≤ ‖c‖⁻¹ implies x₃(e) < 1, hence x₃(e) = 0.

The new rational data have denominator g₃^{r+1} and numerators c · g₃ q and the
(r+1)-th powers of the numerators of d. Its locus is the set of points of the
locus of d with ‖c‖ x'(g₃ q) ≤ x'(g₃)^{r+1}. Each point x' of the locus of d is
the restriction of a point x₃ of M(A₃) (`range_comap_baseMap`), with
x₃(g₃)^{r+1} x₃(z) = x'(g₃ q) and x₃(g₃) > 0. So the inequality says exactly
x₃(z) ≤ ‖c‖⁻¹, that is x₃ ∈ U₃, that is x' ∈ U. Hence the new locus is
d.locus ∩ U.

## Conclusion

Steps 1–3 give rational data whose locus is d.locus ∩ U. This set lies in U, and
by Step 1 it is a neighbourhood of x in U.

## Provenance

The overall route follows the local reduction in M. Temkin, "A new proof of the
Gerritzen–Grauert theorem", Math. Ann. 333 (2005), 261–269: injectivity and the
residue-field approximation of his Proposition 2.1, followed by a closed
immersion over a rational neighbourhood. In Temkin's text the closed-immersion
step uses reduction theory. Here it is replaced by the elementary finiteness
criterion, lying over and the idempotent quotient test, as described above. The
final rational presentation of d.locus ∩ U by density of fractions is internal
to this Library.
