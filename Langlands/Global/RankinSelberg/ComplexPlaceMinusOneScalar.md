# The scalar of `-1` at a complex place of an actual cuspidal realization

Module: `Langlands.Global.RankinSelberg.ComplexPlaceMinusOneScalar` (namespace
`Langlands.Global.RankinSelbergGlobal.ComplexPlaceMinusOne`).

This is a helper module for the proof of `ComplexPlaceMinusOneStatement`
(module `Langlands.Global.RankinSelberg.ComplexPlaceMinusOneProof`). It adds no new statement
(`Prop`-valued definition). Its three definitions (`minusOneMixed`, `minusOneEigenspace`,
`negOneUnitary`) are auxiliary objects used by the proof.

## Main result

`complexMinusOneScalar_eq_prod`: let `F` be a number field whose adele quotient is compact (the
standing hypothesis of the Library's cuspidal realizations), `T` an actual cuspidal realization of
`GL_(r+1)` over `F`, `w` a complex place of `F`, and `ds` a list of complex characters. If `T`
has the standard-module parameter `ds` at `w`
(`T.realization.HasComplexPlaceParameter w ds`), then

  `complexMinusOneScalar T w = (ds.map fun d => d.character (-1)).prod`,

that is, the element `-1 ∈ U(r+1)` at `w` acts on `T` by the scalar `∏_j χ_j(-1)`.

Mathematically this is the standard argument: `-1` at `w` is central, so it acts by a scalar
on an irreducible representation (Schur's lemma in the form "an eigenspace of a central element
is a subrepresentation"). The scalar is read off on the principal series of the parameter, where
`-1 = diag(-1, …, -1)` acts through the inducing character. The module gives a direct eigenspace proof of the special case it needs;
the general operator-realization Schur lemma is also available as
`OperatorRealization.exists_eq_smul_of_commute` in
`IrreducibleCentralCharacterProof`.

## Proof, section by section

### `-1` at a complex place is central

- `minusOneMixed w`: the element `(1, (-1 at w, 1 at the other complex places))` of the mixed
  space `mixedEmbedding.mixedSpace F = ℝ^(real places) × ℂ^(complex places)`.
- `coordinates_minusOne`: the archimedean coordinate matrix of
  `complexPlaceCompactInclusion F n w (-1)` is the scalar matrix
  `Matrix.scalar (Fin n) (minusOneMixed w)`. The proof compares entries. It uses the Library
  lemmas `realMatrix_complexPlaceCompactInclusion` (the identity at every real place) and
  `complexMatrix_complexPlaceCompactInclusion` (the given unitary matrix at `w` and the identity at
  the other complex places).
- `coordinates_minusOne_commute`: a scalar matrix over the commutative ring of the mixed space
  commutes with every archimedean matrix (`Matrix.scalar_commute`).
- `minusOne_mul_comm`: so `-1` at `w` commutes with every element of the infinite adelic group.
  This follows by injectivity of `archimedeanGLCoordinates`.
- `realLieConjugation_minusOne`, `complexLieConjugation_minusOne`,
  `envelopingConjugation_minusOne`: the adjoint action of `-1` at `w` is trivial on the real Lie
  algebra, then on its complexification (induction over pure tensors), and then on the
  enveloping algebra. The last step uses `UniversalEnvelopingAlgebra.hom_ext` with the Library's
  `ArchimedeanGL.envelopingConjugation_generator`.

### The compact operator of `-1` at `w` is central in the operator algebra

- `minusOne_commute_operator`: the operator `finiteSmoothCompactRightAction` of `-1` at `w`
  commutes with every element of `automorphicOperatorAlgebra F n`. The proof is
  `Algebra.adjoin_induction` over the three kinds of generators:
  - finite adelic group elements, by `AdelicGL.ofFinite_commute_ofInfinite`;
  - standard infinite compact elements, by `minusOne_mul_comm`;
  - enveloping algebra elements, by `finiteSmoothRightAction_envelopingAction` and
    `envelopingConjugation_minusOne`.
- `complexPlaceCompactRepresentation_minusOne_representation`: so on every operator realization
  `S` the compact action of `-1` at `w` commutes with `S.representation a` for every `a`.
- `minusOneEigenspace S w c`: the eigenspace `Module.End.eigenspace` of the compact action of `-1`
  at `w` for the eigenvalue `c`, bundled as a `Subrepresentation` of `S.representation`.
  `mem_minusOneEigenspace` characterizes its elements `x` by `ρ_w(-1) x = c • x`.

### `-1` on the complex principal series

- `prod_complexPositionCharacter`: the product over positions `i < length ds` of
  `complexPositionCharacter ds i z` is `∏_j χ_j(z)` over the list (induction on `ds`).
- `principalSeriesCharacter_neg_one`: if `ds.length = N`, the principal series character at
  `a = (-1, …, -1)` is `∏_j χ_j(-1)`. Each factor `|a_i|^(…)` of the square root of the modulus
  character is `1` because `‖-1‖ = 1`.
- `rightTranslation_neg_one`: for `f` in `complexStandardModule N ds`, right translation by `-1`
  is multiplication by `∏_j χ_j(-1)`. The proof writes `g · (-1) = diag(-1, …, -1) · 1 · g` and
  applies the defining equivariance of the principal series.

### The scalar

- `negOneUnitary N`: `-1` as an element of the Library's `unitaryCompact ℂ N ⊆ GL_N(ℂ)`.
  `negOneUnitary_unitaryGroup` says that its underlying unitary matrix is `-1` in
  `Matrix.unitaryGroup`. `complexPlaceCompactRepresentation_negOneUnitary` restates this for the
  compact action at `w`.
- `negOneUnitary_translate`: on the `U(N)`-finite functions `complexStandardKFinite N ds`, right
  translation by `negOneUnitary N` is multiplication by `∏_j χ_j(-1)`.
- `exists_minusOne_eigenvector`: from the parameter `ds` at `w`, take the injective
  `(𝔤, K)`-equivariant map `A` it provides. The Library theorem `complexStandardNontrivial` gives a
  nonzero `U(r+1)`-finite function `f`, so `A f ≠ 0`. Equivariance for `k = negOneUnitary (r+1)`
  and `negOneUnitary_translate` then give `ρ_w(-1)(A f) = ∏_j χ_j(-1) • A f`.
- `minusOne_eq_smul_of_eigenvector`: in the irreducible realization `T`, a nonzero eigenvector
  `y` of `-1` at `w` with eigenvalue `c` forces `ρ_w(-1) x = c • x` for every `x`.
  `T.irreducible` makes `minusOneEigenspace T.realization w c` either `⊥` or `⊤`. It is not `⊥`
  because it contains `y ≠ 0`.
- `complexMinusOneScalar_eq_prod`: so `-1` at `w` acts by the scalar `c = ∏_j χ_j(-1)`. By the
  Library's `complexMinusOneScalar_spec`, it also acts by `complexMinusOneScalar T w`. The two
  scalars agree because they agree on the nonzero vector `y` (`smul_left_injective`).

## Provenance

All results here are internal. The central-character argument is standard (Schur's lemma for a
central element). The computation of `-1` on the principal series follows directly from the
Library's definition of `principalSeries`.
