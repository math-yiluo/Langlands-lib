# Closed orbits whose stabilizer is a prescribed matrix group

This module is an internal derivation. It constructs, for a suitable matrix
group `H`, a representation `π` of `GL n 𝕜` and a vector `w` such that:

- `π` is compatible with conjugate transpose;
- the orbit of `w` is closed;
- the stabilizer of `w` is exactly `H`.

The construction uses polynomial invariant theory. It combines the published
canonical Reynolds operator (`Langlands.Algebra.CanonicalReynolds`) with
Mathlib's Nullstellensatz. Composing the result with the published minimal-vector
theorem (`Langlands.Group.MinimalVector.exists_conj_star_mem_stabilizer`) shows
that `H` has a conjugate stable under conjugate transpose.

Background: the statement that a reductive subgroup is the stabilizer of a
vector with closed orbit belongs to the Matsushima–Richardson circle of results
in geometric invariant theory. Those results are background only. The module
formalizes no specific literature theorem, and its hypotheses are the concrete
algebraic conditions below, not reductivity.

Throughout, `𝕜` is an `RCLike` field in an arbitrary universe, and `n : Type`
is finite with decidable equality (it may be empty). Everything is in the
namespace `Langlands.Group.ClosedOrbit`. Polynomial rings are
`MvPolynomial (Index n) 𝕜`, and the topology on `EuclideanSpace 𝕜 m` is its
usual norm topology.

## Coordinates on a matrix and its inverse

- `Index n := (n × n) ⊕ (n × n)`. A vector `z : Index n → 𝕜` has a first matrix
  `fst z` (from the left summand) and a second matrix `snd z` (from the right
  summand). `ext_fst_snd` says that these two matrices determine `z`.
- `point g` is the coordinate vector of `g : GL n 𝕜`, with
  `fst (point g) = g` and `snd (point g) = g⁻¹`. Suppose
  `fst z * snd z = 1`. Then `unitOf z hz` is the unit with these two matrices,
  and `point_unitOf` gives `point (unitOf z hz) = z`.
- `leftMatrix g` is the block-diagonal Kronecker matrix
  `fromBlocks (g ⊗ₖ 1) 0 0 (1 ⊗ₖ (g⁻¹)ᵀ)`, and `rightMatrix h` is
  `fromBlocks (1 ⊗ₖ hᵀ) 0 0 (h⁻¹ ⊗ₖ 1)`. Acting on coordinate vectors they
  send `(X, Y)` to `(g X, Y g⁻¹)` and to `(X h, h⁻¹ Y)` respectively. The
  lemmas `fst_leftMatrix_mulVec`, `snd_leftMatrix_mulVec`,
  `fst_rightMatrix_mulVec` and `snd_rightMatrix_mulVec` state these formulas.
  The supporting lemmas `kronecker_one_mulVec_apply` and
  `one_kronecker_mulVec_apply` evaluate the Kronecker factors.
- Consequences:
  - `leftMatrix_mulVec_point`: `leftMatrix g *ᵥ point x = point (g * x)`.
  - `rightMatrix_mulVec_point`: `rightMatrix h *ᵥ point x = point (x * h)`.
  - Composition laws `leftMatrix_mulVec_mulVec` and
    `rightMatrix_mulVec_mulVec` (right translation composes in reverse order).
  - `rightMatrix_one_mulVec`.
  - `leftMatrix_rightMatrix_comm`: left and right translations commute.
  - `leftMatrix_mul` and `leftMatrix_one`: `leftMatrix` is multiplicative.
  - `conjTranspose_leftMatrix`: `(leftMatrix g)ᴴ = leftMatrix (star g)`.
- `coordinateIndex` sends the published coordinates
  `Langlands.GroupScheme.GeneralLinear.Coordinate n` (matrix entries and inverse
  entries) to `Index n`. With it, `point_comp_coordinateIndex` and
  `eval_rename_point` show that `rename coordinateIndex` turns the polynomials
  of `Langlands.Group.AlgebraicMatrixPowers.IsPolynomiallyDefined` into
  polynomials on `Index n` with the same values at `point g`.

## Polynomial functions and right translation

- `subst M` is the algebra endomorphism of `MvPolynomial (Index n) 𝕜` that
  substitutes the linear form `∑ j, M i j • X j` for each variable `X i`.
  `eval_subst` gives `eval z (subst M p) = eval (M *ᵥ z) p`, using the general
  identity `eval_bind₁_eq`.
- `rightRep 𝕜 n` is the representation of `GL n 𝕜` on polynomials given by
  `h ↦ subst (rightMatrix h)`, so `(h • p)(X, Y) = p(X h, h⁻¹ Y)`. Its axioms
  are checked by polynomial function extensionality (`MvPolynomial.funext`,
  available since `𝕜` is infinite). `rightRep_apply` unfolds it.
- `subgroupRep H` is its restriction to a subgroup `H`, with unfolding lemma
  `subgroupRep_apply`.
- `isMultiplicative_subgroupRep`: `subgroupRep H` acts by algebra maps.
- `eval_point_mul_of_mem_invariants`: an invariant polynomial `f` satisfies
  `f(point (x * h)) = f(point x)` for `h ∈ H`.
- `subst_leftMatrix_subgroupRep`: substitution by `leftMatrix g` commutes
  with `subgroupRep H`.
- `isStable_homogeneousSubmodule`: each homogeneous component is stable, since
  the substituted variables are linear forms.
- `relation i j` is the polynomial `(X Y - 1)ᵢⱼ`. `eval_relation` computes
  it as `(fst z * snd z - 1) i j`, and `eval_relation_point` shows that it
  vanishes at every `point g`. `relation_mem_invariants` shows that it is
  invariant under all right translations, because
  `(X h)(h⁻¹ Y) = X Y`.

## Padded words and the tensor-power representation

- `letter` sends a variable to itself and the padding letter (`Sum.inr ()`)
  to the constant `1`. `Word n D` is `Fin D → Index n ⊕ Unit`, and
  `wordMonomial e` is `∏ k, letter (e k)`.
- `exists_wordMonomial_eq`: every monomial `monomial α 1` with
  `α.degree ≤ D` is a word monomial of length `D`. The proof is by induction
  on `D`. If `α = 0`, use the all-padding word. Otherwise remove one variable
  `i` with `α i ≠ 0` and prepend the letter `i`.
- `mem_span_wordMonomial`: every polynomial of total degree at most `D` lies
  in the `𝕜`-span of the word monomials of length `D`.
- `extendedMatrix g := fromBlocks (leftMatrix g) 0 0 1` is left translation
  extended by the identity on the padding letter.
  `kroneckerPower D M` is the matrix on `Fin D → ι` with entries
  `∏ k, M (e k) (e' k)`. Lemmas:
  - `kroneckerPower_mul` (via `Finset.prod_univ_sum`) and
    `kroneckerPower_one`;
  - `conjTranspose_kroneckerPower`;
  - `extendedMatrix_mul`, `extendedMatrix_one` and `extendedMatrix_star`
    (`extendedMatrix (star g) = (extendedMatrix g)ᴴ`).
- `tensorHom 𝕜 n D : GL n 𝕜 →* Matrix (Word n D) (Word n D) 𝕜` is
  `g ↦ kroneckerPower D (extendedMatrix g)`. `tensorRep 𝕜 n D` is the same
  homomorphism with values in `GL (Word n D) 𝕜`, and `coe_tensorRep` gives its
  underlying matrix.
- `tensorRep_star`: `tensorRep 𝕜 n D (star g) = star (tensorRep 𝕜 n D g)`.
- `subst_letter` and `subst_wordMonomial`: substitution by `leftMatrix g`
  sends each word monomial `wordMonomial e` to
  `∑ e', tensorHom 𝕜 n D g e e' • wordMonomial e'`.

## Generators, the orbit vector and its stabilizer

In this section `H : Subgroup (GL n 𝕜)` satisfies
`[Representation.IsSemisimpleRepresentation (subgroupRep H)]`. This is
semisimplicity of right translation by `H` on the whole polynomial algebra
in the entries of a matrix and of its inverse.

- `generator H e := reynolds (subgroupRep H) (wordMonomial e)` is the
  canonical Reynolds image of a word monomial. By
  `generator_mem_invariants`, it is invariant.
- `exists_adjoin_generator_eq`: for some `D`, the generators of length `D`
  generate the invariant subalgebra `invariantSubalgebra
  (isMultiplicative_subgroupRep H)`. Hilbert's finiteness theorem
  `invariantSubalgebra_fg` applies to the grading by homogeneous components,
  whose degree-zero part consists of the constants. It gives a finite set `T`
  of generators. Take `D` to be the largest total degree in `T`. Each
  `t ∈ T` is invariant and lies in the span of word monomials of length `D`.
  The Reynolds operator fixes `t`, so `t` lies in the span of the
  generators.
- `orbitPoint D g : Word n D → 𝕜` is the vector of values
  `eval (point g) (generator H e)`.
- `tensorHom_mulVec_orbitPoint`:
  `tensorHom 𝕜 n D g *ᵥ orbitPoint D x = orbitPoint D (g * x)`. Substitution
  by `leftMatrix g` commutes with right translation. By naturality of the
  Reynolds operator (`map_reynolds`), it therefore sends each generator to the
  same linear combination of generators as it does for word monomials.
- `act_tensorRep`: on Euclidean space,
  `MinimalVector.act (tensorRep 𝕜 n D) g (toLp (orbitPoint D 1))` equals
  `toLp (orbitPoint D g)`.
- `mem_of_forall_eval_eq` (assumes `[IsAlgClosed 𝕜]` and
  `IsPolynomiallyDefined H`): if every invariant polynomial takes the same
  value at `point g` and at `point 1`, then `g ∈ H`. The proof argues by
  contradiction. Let `I x` be the vanishing ideal of the set of points
  `point (x * h)` with `h ∈ H`.
  1. Each `I x` is stable under right translation and contains the relations.
  2. If `I 1 ⊔ I g ≠ ⊤`, the ideal lies in a maximal ideal. By the
     Nullstellensatz (`eq_vanishingIdeal_singleton_of_isMaximal`) that
     maximal ideal is the vanishing ideal of a point `z`.
  3. The relations give `fst z * snd z = 1`, so `z = point a`.
  4. The defining polynomials of `H`, renamed to `Index n`, lie in `I 1`.
     The same polynomials after substitution by `leftMatrix g⁻¹` lie in
     `I g`. Hence `a ∈ H` and `g⁻¹ * a ∈ H`, so `g ∈ H`, a contradiction.
  5. So `I 1` and `I g` are comaximal. Separation by invariants
     (`exists_invariant_mem_sub_one_mem`) gives an invariant `f` with
     `f(point 1) = 0` and `f(point g) = 1`, against the hypothesis.
- `stabilizer_tensorRep` (assumes `[IsAlgClosed 𝕜]`, `IsPolynomiallyDefined H`
  and a `D` from `exists_adjoin_generator_eq`): the stabilizer
  `MinimalVector.stabilizer (tensorRep 𝕜 n D) (toLp (orbitPoint D 1))` equals
  `H`.
  - If `g` fixes the vector, then all generators agree at `point g` and
    `point 1`. Hence so does the algebra they generate, which is every
    invariant, so `g ∈ H` by `mem_of_forall_eval_eq`.
  - Conversely, elements of `H` fix it by `eval_point_mul_of_mem_invariants`.
- `range_orbitPoint_eq` (assumes `[IsAlgClosed 𝕜]` and the same `D`): the set
  of all `orbitPoint D g` equals the common zero set of all polynomials on
  `Word n D → 𝕜` that vanish on it. Let `x` be such a common zero.
  1. The surjection `Φ` from `MvPolynomial (Word n D) 𝕜` onto the invariant
     subalgebra, given by evaluating at the generators, has kernel vanishing
     at `x`. So evaluation at `x` induces a character `χ` of the invariant
     subalgebra.
  2. Lying over (`exists_algHom_comp_val_eq`) extends `χ` to the whole
     polynomial algebra, that is, to evaluation at some point `z`.
  3. The invariant relations vanish on the orbit, so `fst z * snd z = 1`.
     Then `x = orbitPoint D (unitOf z hz)`.
- `isClosed_range_act`: the orbit
  `Set.range fun g => MinimalVector.act (tensorRep 𝕜 n D) g (toLp (orbitPoint D 1))`
  is closed. Polynomial evaluation is continuous, so the common zero set
  above is closed. By `act_tensorRep`, the orbit is its preimage under the
  continuous map `WithLp.ofLp`.

## Main results

- `exists_closed_orbit_stabilizer_eq`: assume `[IsAlgClosed 𝕜]`,
  `IsPolynomiallyDefined H` and semisimplicity of `subgroupRep H`. Then there
  exist a finite type `m : Type` with decidable equality, a homomorphism
  `π : GL n 𝕜 →* GL m 𝕜` and a vector `w : EuclideanSpace 𝕜 m` such that:
  - `π (star g) = star (π g)` for all `g`;
  - the orbit `Set.range fun g => MinimalVector.act π g w` is closed;
  - `MinimalVector.stabilizer π w = H`.

  The witnesses are `Word n D`, `tensorRep 𝕜 n D` and
  `toLp (orbitPoint D 1)`, for `D` from `exists_adjoin_generator_eq`.
- `exists_conj_star_mem`: under the same hypotheses there is
  `x : GL n 𝕜` with `x⁻¹ * g * x ∈ H → x⁻¹ * star g * x ∈ H` for every `g`.
  Equivalently, the conjugate `x H x⁻¹` is stable under conjugate transpose.
  This is `MinimalVector.exists_conj_star_mem_stabilizer` applied to the
  data above.

The hypothesis `IsAlgClosed 𝕜` holds for `ℂ` and excludes real-type fields
such as `ℝ`. Semisimplicity of
`subgroupRep H` is a hypothesis here. For groups of points of reductive groups
it must be supplied separately.
