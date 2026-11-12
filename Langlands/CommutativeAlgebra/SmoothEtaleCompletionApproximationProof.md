# Finite-order etale specialization of a smooth algebra

`Langlands.CommutativeAlgebra.smoothEtaleCompletionApproximation.{u}`
proves the unchanged
`Langlands.CommutativeAlgebra.SmoothEtaleCompletionApproximationStatement.{u}`.
For every commutative Noetherian local ring `R : Type u`, smooth
`R`-algebra `B : Type u`, completion-valued algebra map `f`, and natural
number `N`, it supplies an etale `R`-algebra `E : Type u` and maps
`B → E → AdicCompletion m R` whose composite agrees with `f` under the
canonical projection to `R / m^N`. Here `m` is the maximal ideal of `R`.
All witnesses remain in the same universe.

The internal proof strengthens the polynomial-specialization construction
in the published `PointedEtaleLocalSections` module from preserving a
residue-field point to preserving a specified quotient-valued point.
`exists_etale_factor_of_polynomial_quotient` handles any ideal `I` and an
algebra `S` etale over `Q = R[X₁, …, Xₙ]`. Lift the finitely many parameter
values of `S → R / I` to `R`, obtaining `Q → R`. The base change
`E = R ⊗[Q] S` is etale over `R`. Its tensor-product universal property
gives `S → E → R / I` with exactly the specified composite.

For positive `N`, `isNilpotent_ker_factor_pow` proves that the kernel of
`R / I^N → R / I` is nilpotent by identifying it with the image of `I`
and taking its `N`th power. `factor_evalₐ` proves that the canonical
completion projections commute with this quotient map, using a Cauchy
sequence representative and its compatibility at indices `1 ≤ N`.
`exists_lift_quotient` then lifts the residue of an etale-algebra point
`E → R / I^N` to `AdicCompletion I R` using Mathlib's
`Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq`.
Mathlib's `Algebra.FormallyUnramified.lift_unique_of_ringHom` identifies
the resulting finite-order point with the original point, since their
residues agree and the reduction kernel is nilpotent.

`exists_etale_approximation_of_smooth_pos` selects the prime of `B`
defined by the residue of `f`. Mathlib's
`Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial` supplies a
localization `B[1/b]` etale over a finite polynomial algebra. The residue
of `f(b)` is nonzero. The maximal-ideal completion is local, so the
surjective local residue map reflects units and `f` extends to `B[1/b]`.
Apply polynomial specialization modulo `m^N` and the preceding etale
lifting lemma, then precompose with `B → B[1/b]`.

At order zero, retain the witnesses constructed at order one; the
comparison is automatic because `R / m^0` is a subsingleton. The proof
requires no reducedness or domain hypothesis and imposes neither locality
of `E` nor injectivity of its completion-valued map.

This is the smooth-source auxiliary result. It proves no arithmetic
G-ring or Popescu theorem and does not provide a smooth factorization
for an arbitrary finite-type algebra. Those inputs are still required
for `FiniteTypeIntEtaleCompletionApproximationStatement`.
