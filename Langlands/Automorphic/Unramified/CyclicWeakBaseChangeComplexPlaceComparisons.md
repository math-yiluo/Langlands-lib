# Comparisons for the complex-place reductions of cyclic weak base change

Module `Langlands.Automorphic.Unramified.CyclicWeakBaseChangeComplexPlaceComparisons`. It proves
the comparisons between the literal complex-place parameters of cuspidal classes, the aggregate
parameters of isobaric data, unitarity and weak transfer that are needed to derive the
complex-place compatibility of cyclic weak transfers (B7, restricted B7) from aggregate
statements on unitary isobaric data. The theorems are used by
`Langlands.Automorphic.Unramified.CyclicWeakBaseChangeComplexPlaceReductionProof` and
`Langlands.Automorphic.Unramified.RestrictedCyclicWeakBaseChangeComplexPlaceReductionProof`.
Nothing here is a hypothesis: every theorem is proved from Library results.

## Parameter order (namespace `Langlands.Automorphic`)

- `CuspidalOperatorRealization.hasComplexPlaceParameter_of_perm`: if an actual cuspidal
  realization `T` has the complex standard-module parameter `es` at the complex place `v` and
  `ds` is a permutation of `es`, then `T` has the parameter `ds` at `v`.

  *Proof.* The standard module of `es` embeds in `T`, so it is irreducible
  (`CuspidalOperatorRealization.isIrreducibleComplexStandard`). For an irreducible principal
  series of `GL_n(ℂ)`, `Langlands.Archimedean.complexStandardPermutation` gives a bijective
  intertwining map from the standard module of the permuted list `ds` onto that of `es`.
  Composing it with the embedding of the standard module of `es` gives an injective
  intertwining embedding of the standard module of `ds`, which is the parameter `ds`. This is
  the converse of the uniqueness up to permutation
  `CuspidalOperatorRealization.complexPlaceParameters_perm`. On the source side it is the
  independence of an irreducible principal series of the order of its inducing characters:
  A. W. Knapp, *Representation theory of semisimple groups* (1986), Proposition 10.18 with
  Theorem 10.6 and Corollary 10.42, applied to `SL_n(ℂ)` as explained in the Markdown of
  `Langlands.Representation.Archimedean.ComplexStandardSurjectionInjectiveReduction`; the
  Library proof of `complexStandardPermutation` takes a direct route on `GL_n(ℂ)`.
- `PositiveRankCuspidalClass.hasComplexPlaceParameter_of_perm`: the same for a positive-rank
  cuspidal class, through a representative.
- `IsobaricData.hasComplexPlaceParameter_ofCuspidal_iff`: for the data of one cuspidal class
  `c`, the aggregate parameter `(IsobaricData.ofCuspidal c).HasComplexPlaceParameter v ds` is
  equivalent to the literal parameter `c.HasComplexPlaceParameter v ds`. The Library theorem
  `IsobaricData.hasComplexPlaceParameter_ofCuspidal` identifies the aggregate predicate with
  the permutation closure of the literal one; the previous item removes the closure.

## Unitary central characters (namespace `Langlands.Automorphic.Unramified`)

- `Eigenvalues.norm_leadingCoeff_eulerPolynomial_power`: raising every eigenvalue to the
  `k`th power raises the absolute value of the leading coefficient of the Euler polynomial
  `∏ (1 - z_i X)`, which is `∏ (-z_i)`, to the `k`th power.
- `eventually_cofinite_of_forall_above`: a property of the finite places of `E` that holds at
  every place above all but finitely many finite places of `F` holds at all but finitely many
  finite places of `E` (each place of `E` lies above its contraction, and only finitely many
  places of `E` lie above a finite set).
- `hasUnitaryCentralCharacter_of_isWeakBaseChangeOf`: if the class of the cuspidal realization
  `T` over `E` is a weak base change (`IsoClass.IsWeakBaseChangeOf`) of the class of `S` over
  `F` and `S` has unitary central character, then `T` has unitary central character.

  *Proof.* It follows the Library proof of `weakInductionUnitaryCentralCharacter` (module
  `Langlands.Automorphic.Unramified.WeakInductionUnitaryCentralCharacter`) for weak induction,
  whose two private lemmas are reproduced here. Let `ω` be the unitary central character of `S`
  and `ξ` the central character of `T` (`OperatorRealization.existsUnique_hasCentralCharacter`,
  module `Langlands.Automorphic.IrreducibleCentralCharacterProof`). The inputs are:
  - *Unramifiedness.* `ξ` is unramified outside a finite set of places of `E`
    (`HeckeFunctionalEquation.exists_finset_isUnramifiedAt`, module
    `Langlands.Global.Factors.HeckeFiniteRamification`). This fact is independent of the
    comparison of Euler polynomials below.
  - *Leading coefficients.* At a finite place outside the exceptional set of a presentation,
    the absolute value of the central character at a uniformizer is that of the leading
    coefficient of the Euler polynomial
    (`CuspidalOperatorRealization.finiteUniformizerValue_eq_elementaryCoefficient`, module
    `Langlands.Automorphic.CentralCharacterTopCoefficient`).
  - *Weak base change.* Above all but finitely many places `v` of `F`, the eigenvalues of `T` at
    a place `w | v` are those of `S` at `v` raised to the residue degree `f(w|v)`
    (`SpectralSystem.IsArithmeticWeakBaseChangeOf`, through
    `CuspidalOperatorRealization.IsoClass.isWeakBaseChangeOf_isoClass_iff`).

  With `Eigenvalues.norm_leadingCoeff_eulerPolynomial_power` this gives
  `‖ξ(ϖ_w)‖ = ‖ω(ϖ_v)‖^f(w|v) = 1` above all but finitely many places `v` of `F`, hence, by
  `eventually_cofinite_of_forall_above`, at all but finitely many places `w` of `E`. A Hecke
  character that is unramified with absolute value one at a uniformizer at all but finitely many
  places is unitary: its absolute value `|ξ|` is a Hecke character that agrees with the trivial
  character at almost all local components (`CompletionPadic.subgroup_eq_top_of_uniformizer_mem`,
  module `Langlands.Automorphic.OperatorScalarCentralCharacter`), hence is trivial by
  `heckeLocalComponentRigidity` (module
  `Langlands.Automorphic.Unramified.HeckeLocalComponentRigidityProof`).
- `isUnitary_galoisOrbit_of_hasUnitaryCentralCharacter`: the Galois orbit datum
  `IsobaricData.galoisOrbit F` of the class of a cuspidal realization with unitary central
  character is unitary. Each constituent is the class of an arithmetic pullback, whose central
  character is the pulled-back unitary character (`HeckeCharacter.isUnitary_comap_iff`,
  `CuspidalOperatorRealization.arithmeticComap_hasCentralCharacter_iff`), and
  `CuspidalOperatorRealization.isUnitarizable_of_hasUnitaryCentralCharacter` applies. The same
  argument is a private lemma of `CyclicRegularOrbitLiftReductionProof`.

## Galois orbits above a complex place (namespace `Langlands.Automorphic.Unramified`)

Let `v` be a complex place of `F` and `E/F` Galois. Mathlib's action of `Gal(E/F)` on infinite
places is `σ • w = w ∘ σ⁻¹`.

- `nonempty_infinitePlacesAbove`: every infinite place of `F` has a place of `E` above it
  (Mathlib's `InfinitePlace.comap_surjective`).
- `complexPlaceParameterTransport_flatten_ofFn`: transport of lists between `v` and a place
  above it (identity or blockwise conjugation) commutes with concatenation.
- `smul_infinitePlace_liesOver`, `isUnramified_of_isComplex_under`: Galois automorphisms permute
  the places above `v`, and a place above a complex place is unramified.
- `galoisPlacesAboveEquiv v w`: for a place `w` above `v`, `τ ↦ τ⁻¹ • w` is a bijection from
  `Gal(E/F)` onto the places above `v`. Surjectivity is Mathlib's transitivity
  `InfinitePlace.exists_smul_eq_of_comap_eq`; injectivity holds because the stabilizer of an
  unramified place is trivial (`InfinitePlace.IsUnramified.stabilizer_eq_bot`).
  `galoisPlacesAboveEquiv_apply_val` records the formula.
- `complexPlace_galois`: if `w' = τ⁻¹ • w`, the pullback of the complex place `w'` along the
  ring isomorphism `τ⁻¹` (`ArchimedeanCompactTransport.complexPlace`) is `w`.
- `isAligned_galois_iff` and `parameterList_galois`: with `w' = τ⁻¹ • w`, reading a list at `w'`
  along `τ⁻¹` (`ComplexPlaceArithmeticTransport.parameterList`, identity when the selected
  embeddings are aligned, conjugation otherwise) equals transporting it from `w'` to `v` and then
  from `v` to `w` (`complexPlaceParameterTransport`). The proof compares the three
  identity-or-conjugation choices: the selected embedding `ι'` of `w'` is `ι ∘ τ` or its
  conjugate, where `ι` is the selected embedding of `w`; in the first case both transports agree
  with the identity, in the second exactly one of `w`, `w'` is aligned with `v`, because the
  embedding of `v` is not real.
- `hasComplexPlaceParameter_galoisConj`: if `T` has the parameter `x` at `w' = τ⁻¹ • w`, then
  the Galois conjugate class `(ofFixedRank T.isoClass).galoisConj τ` (the pullback along `τ⁻¹`)
  has at `w` the parameter obtained by transporting `x` from `w'` to `v` and from `v` to `w`. It
  combines `ComplexPlaceArithmeticTransport.cuspidal_hasComplexPlaceParameter_arithmeticComap`
  with the two previous items.
- `galoisOrbit_hasComplexPlaceParameter` (*orbit parameter*): if `T` has the parameter `ds w'`
  at every place `w'` above `v`, then for every enumeration `e` of the places above `v` and
  every place `w` above `v`, the Galois orbit datum of the class of `T` has at `w` the aggregate
  parameter `complexPlaceParameterTransport v w (complexPlaceLanglandsSum v e ds)`. The orbit
  is enumerated as `j ↦ T^{τ_j}` with `τ_j` the automorphism sent to `e j` by
  `galoisPlacesAboveEquiv v w`; the block of `T^{τ_j}` at `w` is then the transported block of
  `e j`, and the concatenation of these blocks is the transported Langlands sum.

## Sources

- J. Arthur and L. Clozel, *Simple algebras, base change, and the advanced theory of the trace
  formula*, Ann. of Math. Studies 120 (1989), source ID `arthur-clozel-1989-base-change` (PDF
  page = printed page + 14): Chapter III, Definitions 1.1–1.2 (weak and strong lifting),
  printed p. 199; Theorem 5.1, printed p. 212. The comparisons above are the bookkeeping that
  turns the archimedean content of strong lifting, stated for isobaric data, into statements on
  cuspidal classes.
- Operator note `operator-external-inputs-plan-2026-11-16`, Section 2.2, item B7 (TeX line
  199): the component at a complex place `v` of the class weakly induced from `π_E` is the
  Langlands sum of the components of `π_E` at the places above `v`.
