# Eigenvectors of the uniformizer on shifted derivatives

Module `Langlands.Representation.Classification.BernsteinDerivativeEigenvector`,
namespace `Langlands.Classification`.

This module reduces positivity of the central exponents of a shifted derivative
`ν^(1/2) Ψ⁻ τ` to a bound on the eigenvalues of the uniformizer scalar on the radical
coinvariants of `τ`. It is a helper for the positive-order cases of Bernstein's
necessary lower shifted-derivative positivity
(`Langlands.Classification.BernsteinUnitaryLowerDerivativePositivity`).

## Provenance

Bernstein, *P-invariant distributions on GL(N) and the classification of
unitary representations of GL(N) (non-archimedean case)* (1984)
(`bernstein-1984-p-invariant`), §9.4 (i). Bernstein lets `λ_1, …, λ_r` be the
eigenvalues of the uniformizer `ϖ` on the finite-length quotient `E/E_0`, where
`E_0` is spanned by the radical relations. He notes that `|λ_i| = q^(-e)`, where
`e` is the central exponent of an irreducible subquotient of `ν^(1/2) Ψ⁻(π)`.
So `e(ν^(1/2) Ψ⁻(π)) > 0` can be rewritten as `|λ_i| < 1` for all `i`. The last
declaration below proves the implication from the eigenvalue bound to
positivity. The other declarations are routine internal lemmas that Bernstein
uses without comment. No numbered source result is formalized here.

## Conventions

The usual `{p : ℕ} [Fact p.Prime]`, `F : PadicField.{uF} p` and
`T : F.TopologicalData` are fixed, with `T.topology` installed in every
statement. Representations are actual objects of `SmoothRep.{0, uF, uV} ℂ`.
`Derivative.Mirabolic.psiMinus T n` is the normalized functor `Ψ⁻` from mirabolic
representations to representations of `GL_n(F)`. Its carrier is the radical
coinvariant space `Jacquet.Localization.Coinvariants τ.representation (radical n F.Carrier) 1`.
`Derivative.Mirabolic.psiMinusQuotient T n τ` is the quotient map onto it.
`LocalFactor.PadicAbelian.uniformizerUnit T` is the chosen uniformizer as a unit,
and `GeneralLinear.scalar` sends a unit to the corresponding scalar matrix.

## Declarations

- `exists_eigenvector_of_finiteDimensional`: let `W` be a finite-dimensional
  complex subspace of `V` preserved by a linear map `L`. Let `f : V →ₗ U` be a
  linear map with `f (L w - c • w) = 0` for all `w ∈ W`, and suppose `f x ≠ 0` for
  some `x ∈ W`. Then `L` has a nonzero eigenvector in `W` with eigenvalue `c`.
  Proof: otherwise `L - c` is injective on `W`. It is then surjective, since `W`
  is finite-dimensional. So `x = L w - c • w` for some `w ∈ W`, and `f x = 0`,
  a contradiction.

- `exists_eigenvector_of_hom`: for any topological group `G`, let `B` be an
  admissible smooth representation and `g₀` a central element. Suppose `g₀` acts
  on `D` by the scalar `c`, and an intertwiner `f : B ⟶ D` has `f x ≠ 0`. Then
  `g₀` has a nonzero eigenvector in `B` with eigenvalue `c`. Proof: `x` is fixed
  by an open subgroup `K` (smoothness). The `K`-fixed vectors form a
  finite-dimensional space (admissibility, in the Library's all-open-subgroups
  convention), and `B g₀` preserves it because `g₀` is central. Apply the
  previous lemma to this space and `f`.

- `exists_eigenvector_of_isSubquotient`: if `A` is admissible, `g₀` is central,
  and `g₀` acts by the scalar `c` on a nontrivial actual smooth subquotient `D` of
  `A`, then `g₀` has a nonzero eigenvector in `A` with eigenvalue `c`. Proof: the
  subrepresentation `S` of the subquotient is admissible
  (`isAdmissible_of_injective`). The composite of the quotient map `SmoothRep.mkQ`
  with the inverse of the given isomorphism onto `D` is a nonzero intertwiner
  from `S` to `D`. The previous lemma gives an eigenvector in `S`, and its image
  in `A` is the required eigenvector.

- `bernsteinShiftedDerivative_isAdmissible`: for a unitary additive character
  `ψ`, an irreducible smooth `π` of `GL_N(F)` and `k ≤ N`, the shifted derivative
  `bernsteinShiftedDerivative T ψ π k hk` is admissible. Proof: the twist by
  `T.determinantPowerCharacter (N - k) (1/2)` has an open kernel
  (`T.isOpen_ker_determinantPowerCharacter`), so it preserves admissibility both
  ways (`SmoothRep.isAdmissible_twist_iff`). The published
  `Derivative.generalLinearDerivativeFiniteLength` shows that the `k`-th
  derivative of the finite-length `π` has finite length, and
  `glFiniteLengthAdmissibility` makes it admissible.

- `segmentFactor_psiMinus_action`: for a mirabolic representation `τ`, a matrix
  `g` and a vector `y` of `τ`,

  ```lean
  (T.segmentFactor ((Derivative.Mirabolic.psiMinus T n).obj τ) (1 / 2)).representation g
      (Derivative.Mirabolic.psiMinusQuotient T n τ y) =
    Derivative.Mirabolic.psiMinusQuotient T n τ (τ.representation (levi g) y)
  ```

  So `g` acts on a coinvariant class through its Levi image, and the two
  determinant twists cancel. Proof: `T.segmentFactor` twists by
  `|det g|^(1/2)`, and `Derivative.Mirabolic.psiMinus_action` contributes
  `|det g|^(-1/2)`. The product of the two real powers is `|det g|^0 = 1`
  (`Real.rpow_add`).

- `normalizedAbs_uniformizer_lt_one`: `|ϖ| < 1` for `ϖ = T.uniformizer`, since
  `|ϖ| = q⁻¹` (`T.normalizedAbs_uniformizer`) and the residue cardinality `q` is
  greater than one.

- `bernsteinPositiveCentralExponents_segmentFactor_psiMinus` (the reduction step
  of §9.4 (i)): let `τ` be a smooth representation of the mirabolic subgroup of
  `GL_(n+1)(F)`, and assume:

  - `hadm`: `T.segmentFactor ((Derivative.Mirabolic.psiMinus T n).obj τ) (1 / 2)`
    is admissible;
  - `hτ`: for every vector `y` of `τ` outside the radical relations
    `Jacquet.Localization.relations τ.representation (radical n F.Carrier) 1` and
    every `c : ℂ`, if `τ (levi (scalar ϖ)) y - c • y` lies in those relations
    then `‖c‖ < 1`. Here `ϖ` is `LocalFactor.PadicAbelian.uniformizerUnit T`.

  Then `BernsteinPositiveCentralExponents T` holds for the shifted derivative
  `T.segmentFactor ((Derivative.Mirabolic.psiMinus T n).obj τ) (1 / 2)`.

  Proof: let `D` be an irreducible subquotient with exponent `e`, witnessed by a
  scalar character `ω` with `‖ω a‖ = |a|^e`. `D` is nontrivial because it is
  irreducible. The scalar `scalar ϖ` is central, so
  `exists_eigenvector_of_isSubquotient` gives a nonzero vector `w` of the shifted
  derivative with `scalar ϖ • w = ω ϖ • w`. Write `w` as the class of some `y`
  (`psiMinusQuotient_surjective`). Then `y` is not a radical relation (because
  `w ≠ 0`, `Jacquet.Localization.mk_eq_zero`). By
  `segmentFactor_psiMinus_action`, `τ (levi (scalar ϖ)) y - ω ϖ • y` maps to zero
  in the coinvariants, so it is a radical relation. `hτ` gives
  `|ϖ|^e = ‖ω ϖ‖ < 1`. Since `0 < |ϖ| < 1`, `Real.rpow_lt_one_iff_of_pos` gives
  `e > 0`.

## Scope

The hypothesis `hτ` is not derived here. In the main proof it comes from
unitarizability of `τ` together with the absence of nonzero radical-fixed
vectors. Nothing is asserted about the converse implication (positivity ⇒
eigenvalue bound), and no unitarity, homogeneity or highest-derivative condition
is used in this module.
