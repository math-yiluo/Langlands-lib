# Stalk dimension at closed points of smooth schemes over fields

`Langlands.AlgebraicGeometry.fieldSmoothClosedPointStalkDimension.{u}` proves
exactly the published proposition
`Langlands.AlgebraicGeometry.FieldSmoothClosedPointStalkDimensionStatement.{u}`:
for any field `k`, any scheme `X` smooth of relative dimension `g` over `k`,
and every closed point `x` of `X`,

```lean
ringKrullDim (X.presheaf.stalk x) = (g : WithBot ℕ∞)
```

The universe `u` is arbitrary. The proof retains Mathlib's
`SmoothOfRelativeDimension` and the original closed-point hypothesis. It
assumes no global finiteness, connectedness, separatedness, regularity,
perfection or algebraic closedness. The dimension is that of the actual stalk.

## Implemented algebraic calculation

The private lemma `maximal_height_standardSmooth` proves that, for any field
`k`, any standard-smooth `k`-algebra `S` of relative dimension `n`, and every
maximal ideal `P` of `S`, the ideal height is `P.height = n` in `ℕ∞`. The
field and algebra may lie in different universes. Its inputs are pinned
Mathlib results and the following fully proved private lemmas.

1. `height_eq_under_of_flat_quasiFinite` proves preservation of prime height
   under contraction along a flat quasi-finite algebra. The induced map on
   prime spectra is strictly monotone on comparable points: equality of
   contractions would force equality of the primes by
   `Algebra.QuasiFinite.eq_of_le_of_under_eq`. Flat going-down, via
   `Ideal.exists_ideal_lt_liesOver_of_lt`, lifts every smaller prime below a
   contraction to a smaller prime below the chosen prime. Apply
   `Order.height_eq_of_strictMono`, then identify order height with ideal
   height using `PrimeSpectrum.height_eq_orderHeight`.
2. `maximal_height_mvPolynomial` proves height `n` for every maximal ideal
   in `MvPolynomial (Fin n) k`. The proof is by induction on `n`. At zero
   variables use `MvPolynomial.isEmptyRingEquiv` to reduce to a field. For
   the successor, `MvPolynomial.finSuccEquiv` identifies the ring with a
   univariate polynomial ring over the ring in `n` variables. The Jacobson
   property makes contraction of the maximal ideal along the polynomial
   coefficient map maximal. `Polynomial.height_eq_height_add_one` and the
   induction hypothesis finish the calculation. Ring equivalences preserve
   height through `RingEquiv.height_map`.
3. `maximal_under_of_finiteType` proves maximal contraction for a finite-type
   map out of a Jacobson ring. Quotient the target by its maximal ideal;
   the quotient is a field and finite type over the base. The existing
   `finite_of_finite_type_of_isJacobsonRing` makes it module-finite and hence
   integral. Contract the zero maximal ideal using
   `Ideal.isMaximal_under_of_isIntegral_of_isMaximal`, then identify the
   contraction with the inverse image of the original maximal ideal using
   the quotient kernel.
4. For the standard-smooth algebra, use
   `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`
   to choose an étale map from `MvPolynomial (Fin n) k` to `S`. It is flat,
   quasi-finite and finite type. By steps 1 and 3 the maximal ideal has the
   same height as its maximal contraction in the polynomial ring. Step 2
   gives height `n`.

## Scheme stalk calculation

The paired helper module
`Langlands.AlgebraicGeometry.FieldSmoothClosedPointStalkDimensionGeometry`
contains `fieldSmoothClosedPointStalkDimension_of_maximalHeight`, which
reduces the scheme target to precisely the standard-smooth maximal-height
assertion just proved. The final theorem supplies
`maximal_height_standardSmooth` to this adapter with both universes equal to
`u`; its conclusion has exactly the published proposition as its type.

For completeness, the geometric reduction chooses a standard-smooth affine
chart around `x` from the supplied relative-smoothness instance. The base
open contains `f x` and is therefore the whole spectrum of the field. Via
`Scheme.ΓSpecIso`, its section ring is a field, and the given chart map makes
`Γ(X,V)` a standard-smooth algebra over that field of relative dimension `g`.
The ideal corresponding to `x` is maximal by
`IsAffineOpen.primeIdealOf_isMaximal_of_isClosed`, using the given closed-point
hypothesis. `IsAffineOpen.isLocalization_stalk` identifies the actual stalk as
the localization at this ideal. `IsLocalization.AtPrime.ringKrullDim_eq_height`
expresses its dimension as the ideal height, cast into `WithBot ℕ∞`. The
algebraic result gives height `g`; applying the cast yields the conclusion.

## Provenance and scope

This is an internal derived proof using the project's pinned Mathlib,
commit `5ed2965256430c3649e86755f9576b54eca72435` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. The original statement's source
provenance is retained in
`FieldSmoothClosedPointStalkDimensionStatement.md`. The implemented proof
uses ideal height directly rather than the differential-rank and local
topological dimension route described there. Every algebraic and geometric
step is proved in these two modules or imported from Mathlib; there is no
unproved comparison premise in the final theorem.

The proof imports the unchanged published statement through the geometric
helper module. Its other direct imports are
`Mathlib.RingTheory.KrullDimension.Polynomial`,
`Mathlib.RingTheory.Jacobson.Ring`,
`Mathlib.RingTheory.Unramified.LocalStructure`, and
`Mathlib.RingTheory.Smooth.Flat`. It has no dependence on Picard-origin
dimension, reducedness, identity-component smoothness, or chosen-dual
smoothness results. The target statement and its imports are unchanged.

Worker 669 developed the algebraic proof and final assembly. Worker 399
authored the geometric adapter. Worker 1001 supplied provisional advisory
pointers to the étale-chart, quasi-finite and going-down route through Worker
432; the algebraic steps here were independently implemented and compiled.
