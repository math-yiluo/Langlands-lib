# Cuspidal-pair sections as automorphic functions on the block-parabolic quotient

Module `Langlands.Global.Factors.CuspidalPairSchemeAutomorphy` shows that a section of the
cuspidal pair, in the sense of `CuspidalPairEisenstein.IsSection T T'` (module
`Langlands.Global.Factors.CuspidalPairEisensteinSeries`), transported to the points of the
group scheme `GL_N`, `N = r + t + 2`, is an automorphic function on `U_P(𝔸) M(F) \ GL_N(𝔸)` in
the sense of `IsAutomorphicFunctionOn`, for the scheme block parabolic `P` of type
`(r + 1, t + 1)`. This is the hypothesis on the inducing function in the Library's
group-scheme Eisenstein statements (for example `EisensteinAbsoluteConvergenceStatement` and
`EisensteinMeromorphicContinuationStatement`).

The number field `F : Type u` is arbitrary, with `[CompactSpace (AdeleQuotient F)]` as in
`IsSection`.

## Declarations

All are in the namespace `Langlands.Global.CuspidalPairEisenstein`.

- `blockRealizations T T'`: the realizations `T.realization` and
  `(dualRealization T').realization`, indexed by the two blocks of `blockShape r t`.
- `blockRealizations_isJointlyAdmissible`: both are jointly admissible, by
  `CuspidalOperatorRealization.isJointlyAdmissible`.
- `pairCoefficients_le_coefficientValues`: the span of the product functions
  `m ↦ T(v₁)(m₁) · T'^∨(v₂)(m₂)` that occurs in `IsSection` lies in the realized coefficient
  space `coefficientValues` of the two block realizations. Each product is the realized block
  coefficient (`blockCoefficient`) of the pair `(v₁, v₂)`; the product over the two blocks is
  `Fin.prod_univ_two`.
- `isSection_mem_realizedSections`: a section lies in `RealizedSections` (left invariance under
  the adelic unipotent radical and normalized Levi slices in `coefficientValues`). The unipotent
  invariance of `IsSection` is stated for `unipotentSubgroup`, the image of `unipotentRadical`.
- `realizedSection`, `finiteSmoothSection`, `smoothSection`: the section as an element of
  `RealizedSections`, of its smooth vectors for finite right translation
  (`FiniteSmoothRealizedSections`, from the open subgroup of `IsSection`), and of
  `smoothCompactFiniteSections`. For the last, the orbit span under right translation by the
  archimedean standard compact subgroup injects into the finite-dimensional span of the
  translates by the full standard compact subgroup that `IsSection` supplies
  (`finiteSmoothSection_isFiniteVector`); the smoothness of the archimedean slices is the first
  condition of `IsSection`.
- `smoothSectionOnScheme_smoothSection`: the scheme section of `smoothSection hφ` is
  `φ ∘ adelicHomeomorph F N` (by definition).
- `isAutomorphicFunctionOn_of_isSection`: for all smooth-structure data `hsmooth`, `hcalc` of the
  scheme `GL_N`, `φ ∘ adelicHomeomorph F N` satisfies `IsAutomorphicFunctionOn` for
  `parabolicQuotientSubgroup` of the block parabolic, its block-unipotent radical
  (`blockUnipotentInclusion`) and block-diagonal Levi (`blockLeviInclusion`), the subgroup
  `(standardCompactPoints F N).comap (ofInfinite F GL_N)` and the standard matrix embedding.
  By `standardCompactPoints_comap_ofInfinite` that subgroup is
  `generalLinearStandardInfiniteCompact F N`, and the statement is
  `AdelicBlockScalarSections.SchemeSection.isAutomorphicFunctionOn` applied to `smoothSection`.

## Provenance

This is a derived comparison between two Library models of the same objects. In the notation of
Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995), II.1.1, pp. 78–79, a
section is an element of `A(U(𝔸)M(k)\G)_{π₀}` for the cuspidal representation
`π₀ = π ⊗ (π')^∨` of `M = GL_(r+1) × GL_(t+1)`; the conclusion is the automorphy condition on the
inducing function in Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), §2.2, p. 191. The analytic content (smoothness, finiteness under
the centre of the enveloping algebra, moderate growth) is in the published modules
`Langlands.Global.AdelicBlockAutomorphicSections` and their dependencies.
