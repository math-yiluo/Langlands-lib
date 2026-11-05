# Local hypersurface divisibility for actual unramified regular scalars

Author: Worker 1664.

`Langlands.Plancherel.rationalUnramifiedLocalHypersurfaceDivisibility` proves
`RationalUnramifiedLocalHypersurfaceDivisibilityStatement.{u}` at an arbitrary
universe `u`. It adds no premise and does not restrict the local field, the
group, the rank, the open region, or the hypersurface points. The proof first
shows a statement about complex multivariable polynomials. It then extends
that statement to finite Laurent polynomials and moves it to the actual
scalar algebra through the published coordinate identifications. All results
are internal and derived. The only external input is standard
commutative algebra: Nagata's change of variables, Gauss's lemma, and
continuity of the roots of monic complex polynomials.

## Polynomial lemmas

`polynomial_exists_mul_add_mul_eq_C_of_not_dvd`: let `R` be an integrally
closed domain, and let `Q` be a monic irreducible polynomial over `R` that does
not divide `B`. Then there are polynomials `u` and `v` and a nonzero constant
`r ∈ R` with `u * Q + v * B = C r`. By Gauss's lemma for monic polynomials
(`Monic.irreducible_iff_irreducible_map_fraction_map`), `Q` stays irreducible
over the fraction field. Since `Q` is monic, it also still fails to divide
`B` there; this is checked with `modByMonic`. Over the field the two
polynomials are coprime. Clearing the denominators of the Bezout coefficients
with `IsLocalization.integerNormalization` gives the identity over `R`.

`complexPolynomial_exists_mem_roots_norm_sub_lt`: if `q` is a monic complex
polynomial, `ε ≥ 0`, and `‖q(t₀)‖ < ε ^ natDegree q`, then some root of `q`
lies within distance `ε` of `t₀`. The proof writes `‖q(t₀)‖` as the product of
the distances from `t₀` to the roots, using that `q` splits over `ℂ`. If every
root were at distance at least `ε`, this product would be at least
`ε ^ natDegree q`.

`mvPolynomial_exists_eval_ne_zero_of_isOpen`: a nonzero complex polynomial in
finitely many variables takes a nonzero value on every nonempty open set. The
open set contains a product of open neighbourhoods. Each neighbourhood is
infinite, so `MvPolynomial.funext_set` applies.

`monicFiber_exists_zero_eval_ne_zero` is the local root-continuity step. Let
`Q`, `B`, `u` and `v` be polynomials in a variable `t` with coefficients in
`MvPolynomial (Fin m) ℂ`, with `Q` monic and `u * Q + v * B = C r` for a
nonzero `r`. Suppose `(t₀, s₀)` lies in an open set `V` and is a zero of `Q`.
Then `V` contains a zero `(t, s)` of `Q` at which `B` is nonzero. The proof
takes a ball of radius `δ` around `(t₀, s₀)` inside `V`. The set of `s` within
`δ` of `s₀` with `‖Q_s(t₀)‖ < δ ^ deg Q` is open and contains `s₀`, so it
contains a point `s` with `r(s) ≠ 0`. The previous lemma then gives a root `t`
of the monic polynomial `Q_s` within `δ` of `t₀`. At `(t, s)` the Bezout
identity becomes `v(t, s) B(t, s) = r(s) ≠ 0`, so `B(t, s) ≠ 0`.

## Nagata's change of variables

Mathlib's `Mathlib/RingTheory/NoetherNormalization.lean` defines the public
algebra map `NoetherNormalization.T1 f c`. It fixes `X₀` and sends `Xᵢ` to
`Xᵢ + c • X₀ ^ (2 + totalDegree f) ^ i` for `i ≠ 0`. The lemmas this proof needs
about this map are private in that file. The section `Nagata` restates them
under new names, with proofs adapted from Mathlib, which is released under the
Apache 2.0 license (copyright 2025 Sihan Su; authors Riccardo Brasca, Sihan Su,
Wan Lin, Xiaoyang Su). They are:

- `nagata_lt_up`, from `lt_up`;
- `nagata_t1_comp_t1_neg`, from `t1_comp_t1_neg`: `T1 f c` composed with
  `T1 f (-c)` is the identity;
- `nagata_sum_r_mul_ne`, from `sum_r_mul_ne`;
- `nagata_degreeOf_zero_t`, from `degreeOf_zero_t`;
- `nagata_degreeOf_t_ne_of_ne`, from `degreeOf_t_ne_of_ne`;
- `nagata_leadingCoeff_finSuccEquiv_t`, from `leadingCoeff_finSuccEquiv_t`;
- `nagata_leadingCoeff_isUnit`, from `T_leadingcoeff_isUnit`.

The restatements use `T1 f 1` where Mathlib uses its private abbreviation
`T f`. The new lemma `nagata_t1_injective`, which follows from
`nagata_t1_comp_t1_neg`, replaces the injectivity Mathlib derives from its
private equivalence. The key result is `nagata_leadingCoeff_isUnit`: for a
nonzero `f`, the image `T1 f 1 f`, viewed through `finSuccEquiv` as a
polynomial in `X₀` over the other variables, has a unit leading coefficient.

`mvPolynomial_eval_algHom` says that evaluating after a complex algebra map
of polynomial rings is evaluation at the images of the variables.

## The polynomial statement

`mvPolynomial_exists_zero_eval_ne_zero`: let `P` and `A` be complex polynomials
in `n` variables, with `P` irreducible and not dividing `A`. Let `V` be an open
set containing a zero of `P`. Then `V` contains a zero of `P` at which `A` is
nonzero.

If `n = 0`, a polynomial with a zero is zero, which contradicts
irreducibility. If `n = m + 1`, let `e` be the algebra automorphism with
forward map `T1 P 1` and inverse `T1 P (-1)`, and let `ψ` be `finSuccEquiv`.
Multiplying `ψ (e P)` by the constant inverse of its unit leading coefficient
gives a monic polynomial `Q`. `Q` is irreducible because ring equivalences
and multiplication by units preserve irreducibility. It does not divide
`B = ψ (e A)`, because otherwise `P` would divide `A`. The coefficient ring
`MvPolynomial (Fin m) ℂ` is a unique factorization domain, hence integrally
closed, so the Bezout lemma gives `u * Q + v * B = C r` with `r ≠ 0`.

Let `φ y` be the point whose `i`-th coordinate is `e (X i)` evaluated at `y`,
and let `φ'` be the same construction for `e.symm`. Then `φ` is continuous,
`φ (φ' y) = y`, and evaluation of `e h` at `y` equals evaluation of `h` at
`φ y`. Hence the zero `z₀` of `P` gives the zero `φ' z₀` of `Q` (the constant
factor is nonzero everywhere) in the open set `φ ⁻¹' V`. The root-continuity
lemma gives a zero `(t, s)` of `Q` in `φ ⁻¹' V` at which `B` is nonzero. The
point `φ (t, s)` is the required zero of `P` in `V` at which `A` is nonzero.

## The Laurent statement

`finiteLaurent_exists_zero_eval_ne_zero` proves the same statement for
`AddMonoidAlgebra ℂ (Fin n → ℤ)`, with `finiteLaurentEvaluation` at points of
`Fin n → ℂˣ` and an open set `V` of such points.

The algebra map `ι` from `MvPolynomial (Fin n) ℂ` is `mapDomainAlgHom` along
the additive map that sends a finitely supported exponent vector to its
integer-valued function. It sends monomials to the corresponding Laurent
monomials. Laurent evaluation at `c` after `ι` equals polynomial evaluation at
the complex coordinates of `c`. Every Laurent element, multiplied by a
suitable Laurent monomial `x^N` with `N` a vector of natural numbers, lies in
the image of `ι`; this is proved by induction over finite linear combinations.
These monomials are units. Write `x^{N_p} p = ι P` and `x^{N_a} a = ι A`. Then
`P ≠ 0`, and `P` vanishes at the coordinates of `c₀`.

`P` has an irreducible factor `q` in `MvPolynomial (Fin n) ℂ` that vanishes at
the coordinates of `c₀`. Then `ι q` divides `p`. Write `p = ι q * k`. Since
`ι q` vanishes at `c₀`, it is not a unit, and irreducibility of `p` makes `k` a
unit. So `p` is associated to `ι q`, and `q` does not divide `A`. The map
`Pi.map (fun _ => Units.val)` from `Fin n → ℂˣ` to `Fin n → ℂ` is open, because
`Units.val` is an open embedding for `ℂ` and the index set is finite. The
polynomial statement for `q`, `A` and the image of `V` gives a point `c ∈ V`
where `q` vanishes and `A` does not. Then `p = ι q * k` vanishes at `c`, and
`a` does not, because `x^{N_a} a = ι A`.

## Transport to actual regular scalars

The final theorem argues by contradiction, assuming `¬ p ∣ a`. Let `α` be the
published algebra equivalence `rationalUnramifiedLaurentAlgebraEquiv G hp hG`.
Let `e` be the homeomorphism `(rationalImageUnramifiedContinuousEquiv G hp).symm`
followed by `rationalReductiveImageCharacterCoordinates G hG`. The published
`rationalUnramifiedLaurentAlgebraEquiv_eval` gives
`b.val χ = finiteLaurentEvaluation (e χ) (α.symm b)` for each actual scalar `b`.
Ring equivalences preserve irreducibility and divisibility, so `α.symm p` is
irreducible and does not divide `α.symm a`. The open set `e.symm ⁻¹' U`
contains `e χ₀`, where `α.symm p` vanishes. The Laurent statement gives a
point `c` in that set where `α.symm p` vanishes and `α.symm a` does not. The
character `e.symm c` lies in `U` and is a zero of `p`, so the vanishing
hypothesis forces `a.val (e.symm c) = 0`. This contradicts
`finiteLaurentEvaluation c (α.symm a) ≠ 0`.

The hypersurface implication is proved, not assumed: unique factorization
only chooses the factor `q`, and the local conclusion comes from Nagata's
change of variables, the Bezout identity and root continuity. Rank zero is
covered because the polynomial case `n = 0` is contradictory. The theorem
proves divisibility only. It does not prove the cancellation constructions,
regular numerator identities, convergence, or the conditional standard
intertwining theorem mentioned in the statement's Markdown.
