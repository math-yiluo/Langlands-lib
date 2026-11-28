# Jacquet modules of non-maximal simple types of kind (a), from Hecke injectivity

The module `Langlands.BushnellKutzko.PositiveDepthNonmaximalTypeJacquetReduction` reduces the
Jacquet nonvanishing statement `PositiveDepthNonmaximalTypeJacquetStatement` (module
`NonmaximalSimpleTypeJacquetStatement`) to the injectivity of the Hecke operators of simple
types of kind (a), `PositiveDepthTypeHeckeInjectivityStatement` (module
`PositiveDepthTypeHeckeInjectivityStatement`).

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open
subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln` (SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`; PDF page = printed page
+ 12): (7.3.2) and the first remark after it, printed p. 223, with (7.3.6)(i), printed
p. 225. BK93 obtain the principal lemma (7.3.1), printed p. 222, in §7.4, printed pp. 231–233,
from the Hecke algebra isomorphism (5.6.6), printed p. 190; the premise of the reduction is the
consequence of (5.6.6) that is used.

## Statement

```lean
def PositiveDepthNonmaximalTypeJacquetReductionStatement : Prop :=
  PositiveDepthTypeHeckeInjectivityStatement.{uF, uρ, uπ} →
    PositiveDepthNonmaximalTypeJacquetStatement.{uF, uρ, uπ}
```

The universes of the field, of the carrier of the type and of the carrier of the
representation are independent and shared by premise and conclusion.
`positiveDepthNonmaximalTypeJacquetReduction` proves it.

## Proof

The proof is `PositiveDepthNonmaximalReduction.positiveDepthNonmaximalTypeJacquet_of_heckeInjectivity`,
which applies the pointwise theorem
`PositiveDepthNonmaximalReduction.not_subsingleton_jacquet_of_heckeInjective`: for given data
`IsSimpleTypeData ψF S q e (glRepresentationToAut ρ)` with `2 ≤ e`, a smooth `π` with
`ContainsType π ρ`, and the Hecke injectivity for this `ρ` and `π`, there are a block shape
`B` with `B.parabolic F ≠ ⊤` and `g` with nonzero `Jacquet.Coinvariants` along
`B.conjugateUnipotent g`. The steps, in `Aut_F(F^n)` and then in `GL_n(F)`:

1. `exists_blockIdempotent`: from a relative splitting `E`-basis of the chain of `𝔄`
   (`exists_relSplits_basis`), `RelSplitIdempotent.blockIdempotent` gives an idempotent `ε`
   of `𝔄` commuting with `β`, with `ε x (1 - ε)`, `(1 - ε) x ε ∈ 𝔓` for `x ∈ 𝔄`. The period
   `e` of the centralizer chain is the shift of a uniformizer of `𝔬_E`
   (`subfieldChain_period_eq_shift`), so `e ≥ 2` gives `ε ≠ 0, 1`.
2. `exists_jAlgebra`: `simpleStratumLatticeProperties` provides `𝔍(β, 𝔄)` as an
   `𝔬_F`-subalgebra `R` of full rank, contained in `𝔄` and containing `𝔅_β`, and
   `simpleStratumGroupProperties` describes `J = U(𝔄) ∩ R` and `J^1 = U^1(𝔄) ∩ R`. Hence
   `ε ∈ R` and `BlockIdempotent.exists_factor` gives the Iwahori factorization
   `J = (J ∩ U)(J ∩ M)(J ∩ U⁻)` for the unipotent radicals and Levi subgroup of `ε`.
3. `zeta`: the contraction `ζ = ϖ_F ε + (1 - ε)` lies in `B_β^×` (`zeta_mem_centralizer`)
   and commutes with `ε`; `pow_conj_upper_mem`, `pow_conj_lower_mem` and
   `exists_pow_conj_mem` give the contraction properties of `ζ` on `J ∩ U`, `J ∩ U⁻` and `U`.
4. Intertwiners: `κ` is intertwined by `ζ^r ∈ B_β^×` (the `β`-extension condition), and
   `sigma_conj_eq` shows, through the Iwahori factorization and the triviality of `σ` on
   `J^1 ⊇ J ∩ U^±`, that the identity intertwines `σ` at `ζ^r`; `intertwines_tprod` gives a
   nonzero intertwiner of `κ ⊗ σ` at `ζ^r`. `IsPairIsomorphic.selfIntertwining_eq` and
   `selfIntertwines_comp_mulEquiv_iff` (module `IntertwiningTransport`) transport it to a
   nonzero `Θ ∈ intertwiningSpace ρ ρ (ζ^r)` in `GL_n(F)`, where the premise gives an
   injective Hecke operator.
5. Shrinking: `κ` is trivial on `J ∩ U^m(𝓛')` for some chain `𝓛'`; with
   `exists_endFiltration_le` and `BlockIdempotent.pow_conj_mem_unitFiltration`, a power of
   `ζ` conjugates `J ∩ U` into that group and into `J^1`, so `κ ⊗ σ`, and hence `ρ` through the
   pair isomorphism, is trivial on `ζ^{r₀} (J ∩ U) ζ^{-r₀}`.
6. `TypeHeckeJacquet.not_subsingleton_coinvariants_of_heckeInjective` gives nonzero
   coinvariants along the preimage of `upperGroup ε`; `BlockIdempotent.exists_blockShape`
   provides `B` and `g` with `B.conjugateUnipotent g` inside it, and
   `not_subsingleton_coinvariants_of_le` passes to the smaller subgroup.

Further helper results of the module: `conj_mem_upperGroup_of_comm` (conjugation by a unit
commuting with `ε` maps `upperGroup ε` into itself), `val_zeta`, `scalar_pow_mul`, `scalar_pow_mem`
and `zeta_mem_leviGroup`. No admissibility or irreducibility of `π` is used, as in (7.3.6)(i).
The module does not prove `PositiveDepthTypeHeckeInjectivityStatement`.
