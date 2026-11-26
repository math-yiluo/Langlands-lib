# Changing the integer ring of a stratum

Module `Langlands.BushnellKutzko.NonsplitFundamentalSimpleTransport`, namespace
`Langlands.BushnellKutzko.NonsplitSimple`. It imports `NonsplitFundamentalSimpleStatement`.

## Setting

`O₁`, `O₂` are commutative rings with algebra maps to a field `K`, and `V` is a `K`-vector space
on which both act through `K` (`IsScalarTower Oᵢ K V`). The data are a ring isomorphism
`φ : O₁ ≃+* O₂` and `hφ : ∀ a, algebraMap O₂ K (φ a) = algebraMap O₁ K a`. Then `φ a` and `a`
act on `V` in the same way (`transport_smul`).

## Constructions

- `transportSubmodule φ hφ M`: an `O₁`-submodule `M` of `V` as an `O₂`-submodule with the same
  vectors. Inclusions, strict inclusions, spans, finite generation and multiplication by the
  Jacobson radical are preserved (`transportSubmodule_le_iff`, `transportSubmodule_lt_iff`,
  `transportSubmodule_span`, `transportSubmodule_fg`, `transportSubmodule_jacobson_smul`). For
  the last, `φ` maps `Ring.jacobson O₁` onto `Ring.jacobson O₂`
  (`transport_mem_jacobson_iff`, `jacobson_eq_map`).
- `transportChain φ hφ 𝓛`: an `O₁`-lattice chain as an `O₂`-lattice chain with the same
  lattices. It has the same filtration `𝔓^n`, period, valuation, normalizer `𝔎(𝔄)` and critical
  exponent `k₀` (`transportChain_mem_endFiltration`, `transportChain_period`,
  `transportChain_valuation`, `transportChain_mem_stabilizer`,
  `transportChain_criticalExponent`). Transport along `φ.symm` recovers the original chain
  (`transportChain_symm`).
- `transportStratum φ hφ S`: the stratum with the transported chain and the same `n`, `r` and
  `b`. It has the same coset (`transportStratum_coset`), so equivalence is preserved. It is
  fundamental or simple exactly when `S` is (`transportStratum_isFundamental`,
  `transportStratum_isSimple`).
- `residueRingEquiv φ : O₁/𝔭₁ ≃+* O₂/𝔭₂` is the induced isomorphism of residue rings. When
  `algebraMap O₂ K` is injective, the reduction `reduceIntegralPolynomial` over `O₂` is the image
  of that over `O₁` (`transport_reduceIntegralPolynomial`), because both choose the unique
  integral preimage of each coefficient. Hence a nonsplit fundamental stratum stays nonsplit
  fundamental (`transportStratum_isNonsplit`), with prime element `φ π` and polynomial the image
  of `p`.
- `transportOrderEquiv`, `transportResidueEquiv`, `transportStratumResidueEquiv`: the orders
  `𝔄` of the two chains are the same subring of `End_K(V)`, so they are isomorphic, and so are
  the rings `𝔄/𝔓`. When `b ∈ 𝔓^{−n}`, the isomorphism matches the residue centralizers
  (`mem_transport_residueCentralizer_iff`), giving `transportResidueCentralizerEquiv`.

## Main result

`nonsplitSimpleCriterion_of_transport`: if `algebraMap O₂ K` is injective,
`b ∈ 𝔓^{−n}` and the transported stratum satisfies `Stratum.NonsplitSimpleCriterion`, then so
does `S`. A simple stratum `T` equivalent to `S` on its chain transports to one for the
transported stratum. Conversely, a simple stratum `T'` for the transported stratum transports
back along `φ.symm` to a simple stratum on `S.chain`, by `transportChain_symm`. The two residue
centralizers are isomorphic rings, so one is semisimple exactly when the other is.

## Use

`NonsplitFundamentalSimpleProof` applies this with `O₁ = subfieldIntegers F E`, the integral
closure of `𝔬_F` in a finite extension `E/F`, and `O₂ = 𝒪[E]` for the spectral local-field
structure of `E`, with `φ = subfieldIntegerEquiv F E` (module `SubfieldIntegerArithmetic`).
These are the two integer-ring presentations of `𝔬_E` used for derived strata in Bushnell–Kutzko,
*The admissible dual of GL(N) via compact open subgroups* (1993), §1.2, printed pp. 24–25,
literature ID `bushnell-kutzko-1993-admissible-dual-gln`.
