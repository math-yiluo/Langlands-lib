# The simultaneous compact-open basis for `GL_N`

`Langlands.BruhatTits.SpecialCompact.generalLinearSimultaneousStandardBasis`
proves `GeneralLinearSimultaneousStandardBasisStatement`, the specialization
of Renard V.5.2(i)–(iv) to the standard integral subgroup of `GL_N`. It holds
for every nonarchimedean local field `F` in universe `u`, every matrix size
`N` and every generic cocharacter `ν` of the diagonal torus
`i := GeneralLinear.diagonalTorus (Fin N) F`.
[Statement and source](GeneralLinearSimultaneousStandardBasisStatement.md)

## Proof

The theorem applies `CongruenceGL.simultaneousStandardBasisAt_integralPoints`
to the integral model `M := GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N)`.
Its hypotheses are supplied as follows.

- `GL_N` over `F` is connected reductive: `isConnectedReductive_generalLinear`.
- The diagonal torus is a maximal split torus:
  `GeneralLinear.isMaximalSplitTorus_diagonalTorus`.
- `ν` is generic: this is the hypothesis of the statement.
- Every cocharacter `y` of the diagonal torus lifts to the model: there is a
  cocharacter `χ` of the model group `GL_N` over `𝒪[F]` with
  `M.genericCocharacter χ = groupHom y ≫ i`.

For the last hypothesis, let `w := GeneralLinear.cocharacterCoordEquiv (Fin N) F y`
be the integer weights of `y` on the diagonal coordinates. The lift is the
diagonal cocharacter `GeneralLinear.diagonalCocharacter (Fin N) 𝒪[F] w` with
the same weights. By definition, `M.genericCocharacter χ` is the base change
of `χ` to `F` followed by the generic isomorphism of `M`; for the standard
model that isomorphism is `GeneralLinear.baseChangeIso`.

1. `GeneralLinear.baseChangeCocharacter_diagonalCocharacter` identifies the
   composite with `GeneralLinear.diagonalCocharacter (Fin N) F w`.
   [Diagonal base change](../../GroupScheme/Dynamic/GeneralLinearBaseChange.md)
2. `GeneralLinear.cocharacterOfWeights_comp_diagonalTorus` identifies the
   latter with `groupHom (cocharacterOfWeights F w) ≫ i`.
   [Diagonal weights](../../GroupScheme/Rational/GeneralLinearIndexing.md)
3. `cocharacterOfWeights F w = y`, because `cocharacterOfWeights` is the
   inverse of `cocharacterCoordEquiv`.

## The model theorem

`CongruenceGL.simultaneousStandardBasisAt_integralPoints` uses the congruence
subgroups `M.congruenceSubgroupAt n` of the integral model. These are compact,
open and normal in the integral points and cofinal among identity
neighborhoods. A faithful integral representation that diagonalizes a lifted
cocharacter gives each of them an Iwahori factorization and weak chamber
contraction for every standard parabolic. The theorem
`simultaneousStandardBasisAt_of_cofinal_weakIwahoriNormalFamily` derives the
full simultaneous basis predicate from these properties.
[Congruence tower proof](CongruenceBasis/Assembly.md)

The proof thus specializes this general integral-model theorem to the
standard `GL_N` model rather than following Renard's argument.
