# Proof of the regular elementary Jacquet trace formula

`Langlands.BaseChange.regularElementaryJacquetTrace.{u,v}` proves
`Langlands.BaseChange.RegularElementaryJacquetTraceStatement.{u,v}` of the
module `Langlands.BaseChange.RegularElementaryJacquetTraceStatement`. The proof
adds no hypotheses, and the field and representation universes stay
independent. The irreducibility hypothesis of the statement is not used. The
equality holds for every admissible representation with a σ-intertwiner.

Notation:

- `E` is a canonical p-adic field with residue cardinality `q`.
- `K = GL_{r+1}(O_E)`, which has mass one under the ambient Haar measure
  `sphericalHaar E r` on `GL_{r+1}(E)`.
- `I = regularElementaryCompactOpenSubgroup E r` is the subgroup with diagonal
  reduction.
- `t = torus ϖ ν = diag(ϖ^{ν_i})`.
- `A` is the supplied σ-intertwiner, `A ρ(g) = ρ(τ(g)) A`.

The main work is `twistedDistribution_regularElementaryTest_eq_jacquetTrace`,
the same equality for fixed data. The closing theorem only introduces the
quantified variables.

## Route

1. **Coset reduction.** The published `twistedDistribution_regularElementaryTest`
   writes the twisted trace of the regular elementary test as `[K : I]` times
   the twisted trace of `regularElementaryDoubleCosetTest E ϖ ν`. That test is
   by definition the indicator of `I t I`.
2. **Compression.** `twistedDistribution_doubleCosetIndicator` of the module
   `Langlands.BaseChange.DoubleCosetTwistedTrace` gives
   `μ(I) [I : I ∩ t I t⁻¹] · trace_{V^I}(A' ∘ C)`. Here `A'` is `A` restricted
   to `V^I` and `C = Jacquet.compressedAction ρ hρ I hI t` is `w ↦ e_I(ρ(t)w)`.
   The restriction exists by `sigmaIntertwiner_mem_fixedVectors`: `τ` preserves
   `I` (`entrywiseAut_mem_regularElementary_iff`, from the published
   `entrywiseAut_mem_regularElementaryCompactOpenSubgroup` applied to `τ` and
   `τ⁻¹`).
3. **Scalars.** `card_regularElementaryCosets_mul_measure` gives
   `[K : I] μ(I) = 1`. `natCard_quotient_regularElementaryConjIntersection`
   gives `[I : I ∩ t I t⁻¹] = q^{ρ(ν)}`. Both are in the module
   `Langlands.BaseChange.RegularElementaryIwahoriContraction`. The remaining
   factor is `q^{ρ(ν)}`.
4. **Commutation.** `A'` commutes with `C`. `averageMap_sigmaIntertwiner` says
   that `A` commutes with the average over `I`: both send `v` to the average of
   `A v`, because `τ` permutes `I`. The identity `A ρ(t) = ρ(τ(t)) A` and
   `entrywiseAut_torus_of_fixed`, which gives `τ(t) = t` from `τ(ϖ) = ϖ`, finish
   the step.
5. **Fixed-space comparison.** `map_borelJacquetFixed` shows that the published
   linear equivalence `(singletons (r+1)).jacquetModuleEquiv ρ`, from the Borel
   Jacquet module to the ambient coinvariants `V_N`, carries
   `borelJacquetFixed E ρ` onto the vectors of `V_N` fixed by the embedded
   `I ∩ M`. The published `Parabolic.jacquetModuleEquiv_leviCoinvariants`
   intertwines the two Levi actions. Membership in `integralDiagonalLevi`
   matches membership of the embedded diagonal matrix in `I`, by
   `diagonalUnits_mem_regularElementaryCompactOpenSubgroup` and
   `regularElementaryCompactOpenSubgroup_le_spherical`. The restricted
   equivalence is `borelJacquetFixedEquiv`.
6. **Trace on the Jacquet module.** The module
   `Langlands.Representation.Jacquet.IwahoriContractionTrace` supplies
   `Jacquet.trace_compressedAction_mul_of_iwahoriContraction`. It is applied with
   the contraction data `regularElementary_isIwahoriContraction`, `X = A'`, and
   `Z` the conjugate under `borelJacquetFixedEquiv` of
   `borelJacquetDiagonalAction E ρ (ϖ^ν) ∘ borelJacquetFixedTwist E ρ τ A`. The
   required compatibility `p(C(A' x)) = Z(p x)` is checked on a representative.
   - The published `Jacquet.mk_compressedAction_of_iwahoriContraction` and
     `Jacquet.action_mk` show that the class of `e_I(ρ(t) A x)` is the class of
     `ρ(t) A x`.
   - `Z` sends the class of `x` to the class of `ρ(t) A x`. The descended
     intertwiner sends `[x]` to `[A x]`, and the diagonal action of
     `singletonLevi (ϖ^ν)` is `ρ(t)` by `leviEmbedding_singletonLevi_eq_diagonalUnits`.

   Since the trace is commutative, `trace(A' C) = trace(C A')`, which equals
   `trace Z`. By `LinearMap.trace_conj'` that is the trace in the statement.

The main lemma carries `set_option maxHeartbeats 1000000`, a finite limit.
Elaborating its proof term needs more than the default budget.

## Source

Guy Henniart and Bertrand Lemaire, *Changement de base et induction
automorphe pour GLₙ en caractéristique non nulle*, Mém. SMF 124 (2011), I.5.3,
Proposition, printed pp. 31–32 (PDF pp. 39–40). The statement Markdown records
how the Lean formula specializes the source to strict weights and the
unnormalized Borel Jacquet action. The printed proof integrates over an orbital
chart and evaluates its Jacobian `J(t)` as `q^{ρ(lν)}`. The proof here instead
reduces to the compact double coset `I t I`. It counts the cosets of
`I ∩ t I t⁻¹` through the Haar modulus of `t`, and passes from fixed vectors
to the Jacquet module by Jacquet's lemma on the stable image of the
compression. Registered literature ID
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
