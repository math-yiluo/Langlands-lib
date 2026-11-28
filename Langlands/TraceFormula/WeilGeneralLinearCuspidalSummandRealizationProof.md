# Irreducible cuspidal `L²` summands of `Res_{L/K} GL_n` come from cuspidal realizations over `L`

Module `Langlands.TraceFormula.WeilGeneralLinearCuspidalSummandRealizationProof`, namespace
`Langlands.TraceFormula`. The theorem
`Langlands.TraceFormula.weilGeneralLinearCuspidalSummandRealization` proves
`Langlands.TraceFormula.WeilGeneralLinearCuspidalSummandRealizationStatement.{u}` at an arbitrary
universe `u`. Let `L/K` be a finite extension of number fields and `W = Res_{L/K} GL_{r+1}`. Every
nonzero, closed, invariant and minimal submodule `P` of the full almost-everywhere cuspidal subspace
of `L²([W])` is the closure of the range of a linear map `Ψ` from a cuspidal operator realization of
`GL_{r+1}` over `L`. The map `Ψ` sends each vector to the `L²` class of the function its form
induces on `[W]` (`IsWeilFormClass`). The module contains this one theorem and no other declaration.

## The proof

The proof transports the problem to `GL_{r+1}` over `L` and applies the untwisted theorem
`Langlands.Automorphic.GroupSchemeFunctions.generalLinearCuspidalSummandRealization`
(Getz–Hahn, Theorem 9.7.3, summand-to-realization direction). It runs the transport of
`weilGeneralLinearCuspidalRealizationSummand` (module
`Langlands.TraceFormula.WeilGeneralLinearCuspidalRealizationSummandProof`) in the opposite
direction, with the same helpers.

1. **Data over `L`.** The upper group is `G = GL_{r+1}` over `L`, with the scalar torus
   `GeneralLinear.scalarTorus` from `G_m` as its central split torus. Its split identification is
   `splitTorus.gmIso`. Injectivity of its character restriction is
   `WeilGeneralLinearCuspidalTransport.scalarCharacter_injective`, finite index of the range is
   `scalarCharacter_finiteIndex`, and centrality is `scalar_isCentral`. The hypothesis
   `hG : IsConnectedReductive W` gives `W` an affine total space and a locally finite type
   structure map, which the comparison modules require. Connected reductivity of `G` is
   `isConnectedReductive_generalLinear`.
2. **Comparison of quotients.** `WeilGeneralLinearCuspidalTransport.weilIso` identifies `W` with
   the Weil restriction of `GL_{r+1}` written over `L`. Its adelic points map is `ambientEquiv`,
   an isomorphism of topological groups `W(𝔸_K) ≃ₜ* G(𝔸_L)`. `map_positiveImage` shows that this
   map sends the positive subgroup of the given torus `T` onto the positive subgroup of the scalar
   torus. Right invariance of Haar measure on the norm-one subgroup of `G(𝔸_L)` is
   `normOneHaar_rightInvariant`.
3. **Comparison of cuspidal spaces.** `WeilCuspidalTransport.cuspidalEquiv` is a continuous
   linear equivalence `U` from the full cuspidal subspace over `L` onto the subspace `S` over `K`.
   It takes each class to the class of its pullback along the homeomorphism of positive rational
   quotients induced by `ambientEquiv`. The pushforward of the quotient Haar measure over `K` is
   a positive finite multiple of the one over `L` (`map_positiveQuotientHaar`), so pullback is
   bounded in both directions. `cuspidalEquiv_rightAction` states `U ∘ π_L(ambientEquiv a) = π_K(a) ∘ U` for every
   `a ∈ W(𝔸_K)`.
4. **The summand over `L`.** Let `P' := U⁻¹(P)`, the preimage of `P` under `U`. Applying `U⁻¹` to
   the relation of step 3 at `a = ambientEquiv⁻¹ g` gives
   `U⁻¹ ∘ π_K(ambientEquiv⁻¹ g) = π_L(g) ∘ U⁻¹` for every `g ∈ G(𝔸_L)`. The inverse of
   `ambientEquiv` is surjective. `Langlands.Analysis.IsIrreducibleClosedSummand.comap_symm_of_intertwining`,
   applied to the equivalence `U⁻¹`, then shows that `P'` is nonzero, closed, invariant and minimal.
5. **Untwisted theorem.** `generalLinearCuspidalSummandRealization` applied to `P'` gives a
   cuspidal operator realization `R` of `GL_{r+1}` over `L` and a linear map `Ψ'` into the cuspidal
   subspace over `L`. Each `Ψ' f` satisfies `IsGeneralLinearFormClass` for the form of `f`, and the
   closure of the range of `Ψ'` is `P'`.
6. **Back to `W`.** Put `Ψ := U ∘ Ψ'`. By `cuspidalEquiv_val`, the class `Ψ f` is the image of
   `Ψ' f` under the `L²` comparison `quotientL2Equiv`. The equivalence
   `WeilGeneralLinearCuspidalTransport.isWeilFormClass_iff` turns `IsGeneralLinearFormClass` of
   `Ψ' f` into `IsWeilFormClass` of `Ψ f`. Closures of ranges commute with continuous linear
   equivalences (`Langlands.Analysis.topologicalClosure_range_comp_equiv`). So the closure of the
   range of `Ψ` is the preimage of `P'` under `U⁻¹`, which is `P` because `U (U⁻¹ x) = x`.

The Weil group scheme `AffineWeil.groupScheme` is made locally irreducible so that instance
synthesis does not unfold it, as in `weilGeneralLinearCuspidalRealizationSummand`. The module
installs the same two local instances (`IsAffine` and `Smooth` for the general linear group
scheme) as the statement module, so that the theorem has exactly the statement's type.

## Sources

The untwisted input is the summand-to-realization direction of Getz–Hahn, Theorem 9.7.3, with
Theorem 9.7.1 (J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*,
Graduate Texts in Mathematics 300, Springer, 2024, printed pp. 264–267; registered literature
source `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`). The identification
`Res_{L/K} GL_n(𝔸_K) = GL_n(𝔸_L)` behind the comparison is Getz–Hahn §1.4, printed p. 12, and
§13.4, printed p. 350. The adelic, rational and norm-one comparison for Weil restriction used by
the comparison modules is the Library's `AdelicWeilRestriction.normOneComparison`. It follows
T. A. Springer, *Reduction theory over global fields*, Proc. Indian Acad. Sci. (Math. Sci.)
104 (1994), §1.4, printed pp. 208–209, and §3.1(a)–(b), printed p. 214 (registered literature
source `springer-1994-reduction-global-fields`).
