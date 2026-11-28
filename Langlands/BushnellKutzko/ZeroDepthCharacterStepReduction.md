# The depth-zero step of BK93 (8.1.5), from the existence of `β`-extensions

Module `Langlands.BushnellKutzko.ZeroDepthCharacterStepReduction` states and proves
`ZeroDepthCharacterStepReductionStatement`: the depth-zero step
`ZeroDepthCharacterStepStatement` (module `Langlands.BushnellKutzko.SplitTypeExistenceSteps`) of
the proof of Bushnell–Kutzko (8.1.5) follows from two propositions,

- `BetaExtensionStatement` (BK93 (5.2.2)(i)–(ii), existence and classification of
  `β`-extensions), at the universes `uF, uF, 0, 0, 0`, and
- `ZeroDepthNonCuspidalStepStatement` (BK93 printed p. 269 with Lemma (8.1.6): the case of a
  noncuspidal layer factor), at the universes `uF, uπ`.

The definition is
`BetaExtensionStatement.{uF, uF, 0, 0, 0} → ZeroDepthNonCuspidalStepStatement.{uF, uπ} →
ZeroDepthCharacterStepStatement.{uF, uπ, uρ}`, and the theorem
`zeroDepthCharacterStepReduction` proves it. The module proves neither premise.

## Source

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), proof of (8.1.5), case `m = 0`, printed pp. 268–270 (PDF pp. 280–282). Literature ID
`bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.

BK93 take the hereditary order `𝔄` minimal among those for which `π` contains a simple
character of a simple stratum `[𝔄, n, 0, β]`. They find in `π` a representation `κ ⊗ ξ` of
`J(β, 𝔄)`, with `κ` a `β`-extension and `ξ` inflated from
`J / J^1 ≅ U(𝔅) / U^1(𝔅) ≅ ∏_i GL(m_i, k_E)` as `ξ_1 ⊗ … ⊗ ξ_e`. A noncuspidal factor
contradicts minimality (p. 269, Lemma (8.1.6)); if all `ξ_i` are cuspidal and equivalent, `𝔅`
is principal and `κ ⊗ ξ` is a simple type; otherwise it is a split type of level `(x, 0)`
(8.1.4). The Lean proof replaces the minimality of `𝔄` by strong induction on `N − e(𝔄)`: the
noncuspidal case, as stated in `ZeroDepthNonCuspidalStepStatement`, yields a simple character
of a simple stratum of level zero whose lattice chain has a larger period.

## The single step: `zeroDepth_step`

Let `F` be a nonarchimedean local field, `ψF` an additive character with
`IsBKAdditiveCharacter ψF`, `π` a smooth complex representation of `GL_N(F)` (irreducibility is
not used), and `S = [𝔄, n, 0, β]` a stratum with `S.r = 0` and `ContainsSimpleCharacter ψF π S`.
Assuming the two premises, `zeroDepth_step` proves that either `π` contains (`ContainsType`) a
pair `(K, ρ)` that is a simple type (`IsGLSimpleType`) or a split type of level `(x, 0)` for some
`x` (`IsPositiveZeroSplitType` after `glRepresentationToAut`), or there is a stratum `T` with
`T.r = 0`, `e(𝔄_S) < e(𝔄_T)` and `ContainsSimpleCharacter ψF π T`.

Proof, with `J = J(β, 𝔄)`, `J^1 = J^1(β, 𝔄)`:

1. `ContainsSimpleCharacter` gives that `S` is simple, a defining-sequence choice `q`, and
   `θ ∈ C(𝔄, 0, β)` contained in `π`. `exists_beta_tensor_intertwining` (module
   `Langlands.BushnellKutzko.ZeroDepthCharacterStepConstruction`) gives `η` over `θ`, a
   `β`-extension `κ` of `η`, an irreducible `ξ` on `Fin dξ → ℂ` trivial on `J^1`, and a nonzero
   `J`-map `f : κ ⊗ ξ → π`.
2. `ξ` is smooth: `J^1` contains some `U^k(𝔄)` (`exists_unitFiltration_le_simpleJGroup`). Hence
   `κ ⊗ ξ` is smooth (`isSmoothRepresentation_tprod`). It is irreducible by
   `isIrreducible_tensor_of_irreducible_restriction`, since the restriction of `κ` to `J^1` is
   equivalent to the irreducible `η` and `ξ` is irreducible and trivial on `J^1`.
3. Let `E = F[β]`, `𝓛_E` the `𝔬_E`-lattice chain of `𝔅 = 𝔄 ∩ End_E(F^N)` (`subfieldChain`), and
   `k_E` its residue field, which is finite (`LatticeChain.finite_subfieldResidueField`). Let
   `ι : U(𝔅) → J` be `LatticeChain.relativeUnitFiltrationEquiv` followed by the inclusion
   `relativeUnitFiltration_le_simpleJ`, and choose `k_E`-bases `b_i` of the layers of `𝓛_E`
   (`LatticeChain.finite_layer`, `Module.finBasis`), of ranks `m_i`.
4. Every operator `ξ(g)`, `g ∈ J`, is some `ξ(ι x)`: `g = u k` with `u ∈ U(𝔅)` and `k ∈ J^1`
   (`exists_relativeUnit_mul_simpleJGroup_one`), and `ξ(k) = 1`. The layer reduction
   `LatticeChain.layerReduction b : U(𝔅) → ∏_i GL(m_i, k_E)` is surjective
   (`LatticeChain.layerReduction_surjective`), and its kernel lies in `U^1(𝔅)`
   (`LatticeChain.mem_unitFiltration_one_of_layerReduction_eq_one`), which `ι` maps into `J^1`
   (`relativeUnitFiltration_le_simpleJGroup`); so `ξ ∘ ι` is trivial on the kernel.
   `exists_equiv_classTensor_comp` gives irreducible classes `a_i` of `GL(m_i, k_E)` with
   `ξ ∘ ι ≅ classTensor a ∘ layerReduction b`.
5. If some `a_i` is not cuspidal, `ZeroDepthNonCuspidalStepStatement`, applied with the
   coordinate realizations of the `a_i` as the factors `σ_i`, gives the stratum `T`.
6. Otherwise the pair `(matrixSubgroup J, matrixSmoothRep (κ ⊗ ξ))` of `GL_N(F)` is contained in
   `π` (`containsType_matrixSmoothRep` with `f`), and it is pair isomorphic, after
   `glRepresentationToAut`, to `κ ⊗ ξ` (`isPairIsomorphic_matrixSmoothRep`).
   - If two of the cuspidal classes `factorClass i`, `factorClass j` of the layer data
     `LatticeChain.classCuspidalData b a` differ, the pair is a split type of level
     `(n / e(𝔄), 0)`: the data of `IsPositiveZeroSplitType` are `S`, `q`, `θ`, `η`, `κ`, `ξ` and
     the layer data, whose inflation is `classTensor a ∘ layerReduction b`
     (`LatticeChain.classCuspidalData_inflation`); irreducibility is that of `κ ⊗ ξ`
     (`IsPairIsomorphic.isIrreducible`).
   - If all classes `factorClass i` are equal, then all ranks `m_i` equal one `r` and all
     `a_i` equal one class `c` (equal cuspidal classes give equivalent representations,
     `FiniteGeneralLinear.CuspidalRep.isoClass_eq_iff`, hence equal irreducible classes,
     `FiniteRep.classOf_eq_iff`). The pair is a simple type exhibited by data of kind (a)
     (`IsSimpleTypeData` with `e = e(𝔅)`): `𝔄` is principal because every index
     `(L_j : L_{j+1})` of its lattice chain equals `|k_E^r|` (`LatticeChain.relIndex_eq_of_bases`,
     the lattices of `𝓛_E` being those of `𝔄`); `σ₀` is the coordinate realization of `c`; the
     reduction of `U(𝔅_β) = relativeUnitFiltration S.chain S.b 0` is the layer reduction
     composed with the inverse of `relativeUnitFiltrationEquiv`, a layer reduction by
     `LatticeChain.isLayerReduction_comp`; and the equivalence of the restriction of `ξ` with the
     inflated tensor power of `σ₀` is `nonempty_equiv_tensorPower_comp` (with
     `classTensor_const`).

## The induction: `zeroDepthCharacterStepReduction`

Given the two premises, the theorem proves, for every `m`, that every stratum `S` with
`N − e(𝔄_S) = m`, `S.r = 0` and `ContainsSimpleCharacter ψF π S` yields a contained simple type
or split type of level `(x, 0)`, by strong induction on `m` (`Nat.strong_induction_on`). In the
second alternative of `zeroDepth_step`, the new stratum `T` has `e(𝔄_T) ≤ N`
(`LatticeChain.period_le_card`) and `e(𝔄_S) < e(𝔄_T)`, so `N − e(𝔄_T) < m` and the induction
hypothesis applies. The hypotheses `0 < N` and `π.IsIrreducible` of
`ZeroDepthCharacterStepStatement` are not used.
