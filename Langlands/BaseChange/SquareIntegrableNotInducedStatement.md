# Square-integrable representations of `GL_n(F)` are not parabolically induced

This module states, as a proposition, that an irreducible square-integrable
representation of `GL_n(F)` is not isomorphic to a representation induced from
a proper standard block parabolic subgroup. It is not proved here. It is the
first step ("square-integrable representations are σ-discrete for `σ = 1`") of
the recommended route of Task 7882 to the Library statement
`PseudoCoefficientExistenceStatement`; see
`Langlands.BaseChange.PseudoCoefficientExistenceReduction`.

## Statement

`SquareIntegrableNotInducedStatement.{v, w} : Prop` says the following.

Let `F : Type v` be a nonarchimedean local field
(`[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`)
of characteristic zero (`[CharZero F]`), and `n : ℕ`. Let
`π : Representation ℂ (GeneralLinear n F) V`, on a complex vector space
`V : Type w`, be irreducible (`π.IsIrreducible`) and square-integrable
(`JacquetLanglands.IsSquareIntegrable π`: admissible, with a unitary central
character, and with matrix coefficients square-integrable modulo the centre,
for every Haar measure on `GL_n(F) / Z`). Let `B : BlockShape n` be a block
shape with at least two blocks (`2 ≤ B.length`), so that its standard upper
block parabolic subgroup `B.parabolic F` is a proper subgroup of `GL_n(F)`. Let
`Ξ : Representation ℂ (B.Levi F) X`, on a complex vector space `X : Type w`, be
any smooth representation (`IsSmooth Ξ`) of the Levi product
`B.Levi F = ∏ GL_{n_i}(F)`. Then there is no isomorphism of representations
(`π.Equiv`, a `ℂ`-linear equivalence commuting with the actions) from `π` to
the unnormalized smooth induction

`Induction.smoothInduced (B.parabolic F) (Ξ.comp (B.leviProjection F))`,

that is, to right translation on the smooth functions `f : GL_n(F) → X` with
`f(p g) = Ξ(m(p)) f(g)` for `p` in the parabolic subgroup, `m(p)` its Levi
component (`B.leviProjection F`). The form of this conclusion is the last
clause of the Library's `IsSigmaDiscreteSeries` (module
`Langlands.BaseChange.PseudoCoefficient`), including the universe of `X`,
without its hypothesis `IsLeviSigmaStable σ B Ξ`.

### Remarks on the formulation

- Normalized induction differs from unnormalized induction by the twist of the
  inducing representation by `δ_P^{1/2}`, which is again smooth. Since `Ξ`
  ranges over all smooth representations, the statement is the same for
  normalized induction.
- `Ξ` is not assumed irreducible, admissible or σ-stable. An irreducible
  induced representation forces `Ξ` to be irreducible, so the statement is
  equivalent to its restriction to irreducible `Ξ`; σ-stability is vacuous for
  `σ = 1`.
- The characteristic-zero hypothesis is that of the intended proof (the
  Library's Jacquet-module and exponent results are stated over `p`-adic
  fields); the fact holds in every characteristic, but only characteristic zero
  is stated here, which is all that `PseudoCoefficientExistenceStatement` needs.

## Sources

- Henniart–Lemaire, *Changement de base et induction automorphe pour `GL_n` en
  caractéristique non nulle* (2011), II.1.7, printed p. 59 (PDF p. 67): a
  σ-discrete series of `G(E)` is an irreducible smooth tempered σ-stable
  representation that is not isomorphic to the parabolic induction of a smooth
  σ-stable representation of a proper σ-stable Levi subgroup, and "si `E = F`
  et `σ = Id`, on retrouve la notion habituelle de série discrète de `G(F)`".
  The present statement is the half of that remark that is needed here: a
  discrete series (square-integrable) representation is not parabolically
  induced from a proper (standard block) Levi subgroup. HL II.4.6, printed
  p. 88, makes the definition precise with the standard block parabolics.
- Casselman, *Introduction to the theory of admissible representations of
  p-adic reductive groups* (draft, 1 May 1995), Theorem 4.4.6 (p. 45): an
  admissible representation with central character `ω` is square-integrable
  if and only if `ω` is unitary and every central exponent `χ` of its
  unnormalized Jacquet module along every standard parabolic `P_Θ` satisfies
  `|(χ δ_∅^{-1/2})(a)| < 1` for `a ∈ A_Θ^- \ A_∅(O) A_Δ`. Here `δ_∅` is the
  minimal-parabolic modulus, and `A_Θ^-` uses the weak inequalities
  `|α(a)| ≤ 1` for `α ∈ Δ \ Θ` (§1.4, p. 13). Thus some chamber wall points
  are tested. For the upper block parabolic of `GL_n`, the restriction of
  `δ_∅` to block scalars agrees with `δ_P`: within-block roots are trivial
  there and the other positive roots are precisely those in the unipotent
  radical of `P`.

The intended proof uses this criterion. If `π ≅ Ind_P(Ξ)` with `π`
irreducible and admissible, then the smooth inducing representation `Ξ` is
irreducible and admissible, hence has a central character. Put
`σ = Ξ ⊗ δ_P^{-1/2}` so that `π ≅ i_P(σ)` for *normalized* induction
(Casselman §3.1, p. 32). Frobenius reciprocity (Theorem 3.2.4, p. 34) gives
`σ ⊗ δ_P^{1/2}` as a quotient of the unnormalized Jacquet module, so its
central character restricted to block scalars gives an exponent. The
criterion imposes `|χ_σ(a)| < 1` on the test set, where `χ_σ` is the scalar
character of `σ`. The smooth contragredient `π̃` is also square-integrable
and is isomorphic to `i_P(σ̃)` by normalized induction duality (Proposition
3.1.2, p. 32). The same test point would give `|χ_σ(a)^{-1}| < 1`. For
example, with at least two blocks one can take the first block scalar to
be a uniformizer and the others to be one. This point is in the weak
chamber and its block valuations are not all equal, so it is outside
`A_∅(O) A_Δ`. The two strict inequalities are incompatible.

## Provenance

Derived. The proposition is the author's formulation, with the Library's
predicates (`JacquetLanglands.IsSquareIntegrable`, `BlockShape`,
`Induction.smoothInduced`) and in the shape of the last clause of
`IsSigmaDiscreteSeries`, of the classical fact recalled in HL II.1.7 that a
discrete series representation is not parabolically induced from a proper
Levi subgroup; Casselman's criterion is the literature input of its proof.
