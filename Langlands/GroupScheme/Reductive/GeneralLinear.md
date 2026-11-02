# `GL_n` is reductive

This module proves that the Library general linear group scheme
`GeneralLinear.groupScheme n R` is reductive in the sense of
`Langlands.GroupScheme.Reductive.Basic`:

- `hasTrivialUnipotentRadical_generalLinear K n`: over every field `K`, every unipotent closed
  subgroup of `GL_n` with normal image is trivial. The closed-immersion, smoothness and
  connectedness hypotheses on the subgroup are not used.
- `isPseudoReductive_generalLinear k n` and `isConnectedReductive_generalLinear k n`: over every
  field `k`.
- `isReductive_generalLinear n R`: over every commutative ring `R`.

The route is Milne, *Algebraic groups* (2017), Lemma 19.16 and Example 19.19 (printed p. 401).
The implemented proof is described below.

## Linear algebra

`eq_top_of_forall_GL_mulVec_mem`: a nonzero subspace `W ⊆ Kⁿ` stable under `GL_n(K)` is all of
`Kⁿ`. Pick `v ∈ W` with `v p ≠ 0`. For `q ≠ r`, applying the transvection `1 + E_{qr}` to
`x ∈ W` and subtracting `x` gives `x r · e_q ∈ W`. Applied to `v`, this gives `e_q ∈ W` for every
`q ≠ p`. Then `e_p ∈ W` comes from one more transvection, or, if `n` has one element, from
`v = v p · e_p`. This works over every field, including `𝔽₂`.

## The unipotent radical

Let `i : H ⟶ GL_n` with `H` unipotent and `range i` normal. Regard `i` as a matrix
representation of `H`.

- `GeneralLinear.constantMatrixPoint T g` is the point of `GL_n` over `T` given by a matrix `g ∈ GL_n(K)`.
- `mulVec_mem_fixedSubmodule`: if `v` is fixed by `H`, so is `g v`. For a point `h` of `H` over
  `T`, normality gives `h'` with `i(h') = ḡ⁻¹ i(h) ḡ`, where `ḡ` is the constant point. Then
  `i(h) (ḡ v) = ḡ (i(h') v) = ḡ v`.
- `hasTrivialUnipotentRadical_generalLinear`: if `n` is empty, `GL_n` is trivial. Otherwise
  `IsUnipotent H` gives a nonzero fixed vector. The fixed submodule is then `GL_n(K)`-stable, so
  it is everything. Every standard basis vector `e_b` is fixed. So every column of the matrix of
  `i(h)` is the corresponding column of the identity, and `i(h) = 1` on every test scheme.

## Connectedness

`determinantPolynomial_ne_zero`: the determinant of the generic matrix is a nonzero polynomial,
since it evaluates to `1` at the identity matrix. So the Library's `DeterminantLocalization n K`
is a domain. Through `determinantLocalizationEquiv`, so is the coordinate ring
(`isDomain_coordinateRing`). `connectedSpace_generalLinear` follows, because the spectrum of a
domain is irreducible.

## Isomorphisms and base change

- `HasTrivialUnipotentRadical.of_iso` and `IsPseudoReductive.of_iso` transfer the conditions
  along isomorphisms of group schemes. A closed subgroup `i` of `G` gives the closed subgroup
  `i ≫ e.hom` of `G'`. Normality of its range follows from `MonObj.mul_comp` and
  `GrpObj.inv_comp`. Since the range of `i ≫ e.hom` is trivial, composing with `e.inv` shows
  that the range of `i` is trivial. The underlying morphism of an isomorphism of group schemes
  is an isomorphism of schemes (`isIso_left_of_iso`). So smoothness, affineness and
  connectedness transfer.
- `GeneralLinear.baseChangeIso n b`: for every `b : Spec R' ⟶ Spec R`, the base change of `GL_n`
  over `R` along `b` is isomorphic to `GL_n` over `R'`. On points over `T`,
  `GeneralLinear.baseChangeGLPointsEquiv` composes the Library's `baseChangePointsEquiv`,
  `GeneralLinear.pointsEquiv n R` and the inverse of `GeneralLinear.pointsEquiv n R'`. It is
  natural in `T` (`GeneralLinear.baseChangeGLPointsEquiv_naturality`), and the isomorphism is
  built from it with `isoOfPoints`.

## Assembly

Smoothness is the Library theorem `GeneralLinear.smoothStatement`, and affineness is the
Library instance `isAffineHom_groupScheme`. `isConnectedReductive_generalLinear` applies
`HasTrivialUnipotentRadical.of_iso` to the base change along `toAlgebraicClosure k`.
`isReductive_generalLinear` applies `IsPseudoReductive.of_iso` to the base change along each
geometric point `geometricPoint (Spec R) s`, together with `isPseudoReductive_generalLinear` over
`AlgebraicClosure κ(s)`.

## Provenance and authorship

The linear algebra, the unipotent radical and connectedness follow Milne's argument. The
base-change isomorphism and the transfer along isomorphisms are internal steps, not taken from
the cited sources.

Worker 1107 wrote this module and its explanation, first shared as revision 1 of the proof
task's public draft. Worker 1173 rechecked the module unchanged in Lean. They added to this
Markdown the unused closed-immersion hypothesis, the final step of the isomorphism transfer,
`isIso_left_of_iso` and the point equivalence behind `GeneralLinear.baseChangeIso`.
