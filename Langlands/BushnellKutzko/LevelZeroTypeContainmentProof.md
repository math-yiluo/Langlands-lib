# Level-zero type containment (BK93 (8.1.5), first case)

The module `Langlands.BushnellKutzko.LevelZeroTypeContainmentProof` proves

```lean
theorem Langlands.BushnellKutzko.levelZeroTypeContainment :
    Langlands.BushnellKutzko.LevelZeroTypeContainmentStatement.{uF, uπ, uρ}
```

the first of the four steps of the proof of BK93 (8.1.5) stated in
`Langlands.BushnellKutzko.SplitTypeExistenceSteps` ([statement](SplitTypeExistenceSteps.md)):
if a smooth representation `π` of `GL_N(F)` has a nonzero vector fixed by `U^1(𝔄)` for the
hereditary order `𝔄` of some lattice chain in `F^N`, then `π` contains a pair `(K, ρ)` that is
a simple type of level zero (`IsGLSimpleType ψF ρ`) or a split type of level `(0, 0)`
(`IsLevelZeroSplitType` of the transported representation). The proof does not use the
irreducibility of `π`, the hypothesis `N > 0`, or the hypothesis on `ψF`.

It also proves the following statement, for any lattice chain `𝓛` of period `e` in an
`F`-vector space `V`, bases `b_i` of the layers `L_i / L_{i+1}` over the residue field `k`,
`0 ≤ i < e`, with `d_i = dim_k L_i / L_{i+1}`, and the layer reduction
`φ = LatticeChain.layerReduction b : U(𝔄) → ∏_i GL_{d_i}(k)`:

- `LatticeChain.exists_layer_constituent`: let `τ` be a complex representation of
  `Aut_F(V)` on `W` and `w ∈ W` nonzero with `τ(g) w = w` for all `g ∈ U^1(𝔄)`. Then there
  are irreducible classes `a_i` of `GL_{d_i}(k)` and an injective linear map `f` from the
  tensor product of their representatives (`VirtualCharacter.rep`) to `W` with
  `f((⊗_i ρ_i)(φ(g)) x) = τ(g) f(x)` for `g ∈ U(𝔄)`, where `⊗_i ρ_i` is the external tensor
  product `FiniteTensor.external`.

## Source

Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), proof of
(8.1.5), printed pp. 267–268 (PDF pp. 279–280). There `𝔄` is chosen minimal among the
hereditary orders for which `π` has a nonzero `U^1(𝔄)`-fixed vector. The restriction of `π`
to `U(𝔄)` then has an irreducible factor `ϑ` that is trivial on `U^1(𝔄)`, hence of the form
`ϑ = ⊗_i ϑ_i` as a representation of `U(𝔄)/U^1(𝔄) ≅ ∏_i GL(L_i / L_{i+1})`. Each `ϑ_i` is
cuspidal, because a noncuspidal factor would give a smaller such order (printed p. 268, PDF
p. 280, following Bushnell 1987, proof of Theorem 2′(i), printed p. 197, PDF p. 14). If the
`ϑ_i` are all equivalent, `𝔄` is principal and the pair is a
simple type of level zero; otherwise it is a split type of level `(0, 0)`. Here the minimal
order is replaced by an induction on `N - e(𝓛)`: the refinement step produces a lattice chain
of strictly larger period, and periods of lattice chains in `F^N` are at most `N`.

## Proof

*An irreducible constituent* (`LatticeChain.exists_layer_constituent`). The layer reduction
`φ` is surjective (`LatticeChain.layerReduction_surjective`) and its kernel lies in `U^1(𝔄)`
(`LatticeChain.mem_unitFiltration_one_of_layerReduction_eq_one`), so `w` lies in the space
`X` of vectors fixed by `ker φ`. The action of `U(𝔄)` on `X` factors through
`U(𝔄) / ker φ ≅ ∏_i GL_{d_i}(k)` (`Representation.quotientToInvariants` and
`QuotientGroup.quotientKerEquivOfSurjective`). Applied to this representation of the finite
product group and the nonzero vector `w`, `exists_externalRep_intertwining`
(`Langlands.Representation.FiniteGeneralLinear.FiniteProductConstituent`) gives the classes
`a_i` and an injective intertwining map into `X`; composing with the inclusion `X ⊆ W` gives
`f`.

*The cuspidal case.* Let `V = F^N`, let `τ` be the action of `Aut_F(F^N)` on `π` through
`Matrix.GeneralLinearGroup.toLin`, and suppose every representative of `a_i` is cuspidal
(`FiniteGeneralLinear.IsCuspidal`). Transporting each representative to coordinates in a basis
of its carrier (`Module.finBasis`) gives cuspidal layer data `A` for `𝓛`
(`LatticeChain.CuspidalLayerData`, irreducibility and cuspidality transported by
`LengthTwo.isIrreducible_of_equiv` and `FiniteGeneralLinear.IsCuspidal.of_equiv`). Let
`K ≤ GL_N(F)` be the preimage of `U(𝔄)` and `ρ` the inflation `A.inflation` along
`K → U(𝔄)`, on its carrier lifted to the universe of the type (`ULift`). It is trivial on
the preimage of `U^1(𝔄)` (`LatticeChain.layerReduction_eq_one_of_mem`), which is open
(`isOpen_unitFiltration` and the continuity of `generalLinearToLinContinuous`), so `ρ` is
smooth; its transport to `Aut_F(F^N)` is pair-isomorphic to `A.inflation`.

`π` contains `(K, ρ)`: `f`, precomposed with the inverse coordinate isomorphisms
(`PiTensorProduct.congr`), intertwines `ρ` with `π | K` (`FiniteTensor.external_tprod`), and
it is nonzero because a pure tensor of nonzero vectors is nonzero
(`tprod_ne_zero_of_forall_ne_zero`) and `f` is injective.

If two of the classes `A.factorClass i` differ, the pair is a split type of level `(0, 0)` by
definition. Otherwise all the ranks `d_i` equal one `r` and all the classes `a_i` are equal:
an isomorphism of the coordinate factors (`FiniteGeneralLinear.CuspidalRep.isoClass_eq_iff`)
gives an isomorphism of the representatives, so their characters agree (`classOf_eq_iff`,
`VirtualCharacter.classOf_rep`). Then `A.inflation` is the inflation along `φ` of the tensor
power `tensorPowerRepresentation σ₀ e` of one irreducible cuspidal `σ₀`, and the data
`(𝓛, e, r, σ₀, b, φ)` satisfy `IsLevelZeroSimpleTypeData`: `φ` is a layer reduction for the
bases `b` (`LatticeChain.equivFun_layerReduction`), and `𝓛` is principal, because every layer
`L_j / L_{j+1}` is isomorphic to a layer of one period
(`LatticeChain.exists_layer_linearEquiv`) and so has `|k|^r` elements
(`LatticeChain.natCard_interval_eq_relIndex`, `Module.natCard_eq_pow_finrank`).

*The noncuspidal case.* If some representative of `a_{i₀}` is not cuspidal,
`LatticeChain.exists_refinement_of_not_isCuspidal`
(`Langlands.BushnellKutzko.LevelZeroRefinement`) gives a lattice chain `𝓜` with
`e(𝓜) > e(𝓛)` and a nonzero vector of `π` fixed by `U^1(𝓜)`.

*Induction.* For a lattice chain `𝓛` in `F^N` the period is at most `N`
(`LatticeChain.period_le_card`). Strong induction on `N - e(𝓛)` combines the two cases: in the
noncuspidal case the new chain `𝓜` has `N - e(𝓜) < N - e(𝓛)`.
