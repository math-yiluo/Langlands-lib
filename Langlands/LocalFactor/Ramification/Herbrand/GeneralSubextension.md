# Relative inverse Herbrand functions in either characteristic

The declarations in `Langlands.Ramification.Local` use the finite Herbrand
functions from `Langlands.LocalFactor.Ramification.Herbrand.GeneralFinite`.

## Construction

Let `K → E → Ω` be a tower of fields and let `M : FiniteGaloisIntermediateField K Ω`
contain the image of `E`. The containment hypothesis `h` lets
`extendFiniteGalois h` view the same elements as an intermediate field of `Ω/E`.
Finiteness over `E` follows from finiteness over `K`. The Galois property over
`E` follows by `IsGalois.tower_top_of_isGalois`.
`extendFiniteGaloisEquiv h` is the identity on those elements as a `K`-algebra
equivalence.

For `relativeIndex K₀ K hbase M h v`, the field `K₀` is locally compact with a
complete, nontrivial, ultrametric norm. Its specified valuative relation
agrees with norm comparison by `hbase`. The field `K` is finite over `K₀`, and
the algebra structures form compatible towers `K₀ → K → Ω` and
`K₀ → E → Ω`. Give `N := extendFiniteGalois h` its canonical realization
`T := LocalField.canonicalTopologicalData K₀ N hbase`, using finiteness over
`K₀` through `K`. The relative index at any `v : ℝ` is
`herbrandPhi T E (herbrandPsi T K v)`. Both functions use the integer ring and
valuation of this one realization of `M`, extending the norm on `K₀`.

For `E : IntermediateField K Ω` with `[FiniteDimensional K E]` and
`[IsSepClosure K Ω]`, `galoisClosure E` is `IntermediateField.normalClosure K E Ω`
with finiteness and Galois certificates. The ambient separable closure gives
`IsGalois K Ω`, and the embedding of `E` into it supplies separability of `E/K`.
`algebraMap_mem_galoisClosure` is the inclusion of `E` in that normal closure.
`relativeHerbrandPsi K₀ K Ω hbase E` takes the relative index in this specified
normal closure. This construction applies to finite intermediate fields,
including nonnormal ones.

`localRelativeHerbrandPsi K Ω E` takes `K₀ = K`. For `[Field K] [ValuativeRel K]
[TopologicalSpace K] [IsNonarchimedeanLocalField K]`, it uses the
`LocalGalois.localNormedField` adapter, with its completeness, ultrametric,
and valuation-comparison results. The adapter uses the topology supplied on `K`.

## Source convention

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg, GTM 67,
Springer (1979), Chapter IV, §3, Remark 2, printed p. 75 (PDF p. 82), defines
`φ_{E/K} = φ_{M/K} ∘ ψ_{M/E}` for a finite Galois overfield `M`. The inverse
composition is `ψ_{E/K} = φ_{M/E} ∘ ψ_{M/K}`. Here the function is constructed
using the finite Galois normal closure in the supplied `Ω`. The same-carrier
change of base, the containment lemma, and the local-field adapter are internal
constructions implementing that formula. The registered source is
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

## P-adic specializations

The definitions in `Langlands.Ramification.HerbrandBridge` in
`Herbrand.SubextensionProof` specialize the general ones by unfolding.
Take `K₀ = Padic p` and the p-adic norm comparison. For the closure construction
on a `FiniteIntermediateExtension F.Carrier`, take `K = F.Carrier`,
`Ω = AlgebraicClosure F.Carrier`, and the same field `E.field`. The algebraic
closure is separable in the p-adic instance by
`IsSepClosure.of_isAlgClosure_of_perfectField`, using characteristic zero to
obtain perfectness of `F.Carrier`. The general construction uses the supplied
separable closure and the finite-dimensionality of the intermediate field.

| General declaration in `Langlands.Ramification.Local` | P-adic specialization in `Langlands.Ramification.HerbrandBridge` |
| --- | --- |
| `extendFiniteGalois h` | `extendFiniteGalois h` |
| `extendFiniteGaloisEquiv h` | `extendFiniteGaloisEquiv h` |
| `relativeIndex K₀ K hbase M h v` | `relativeIndex F M h v` |
| `galoisClosure E` | `galoisClosure E` for a `FiniteIntermediateExtension` |
| `algebraMap_mem_galoisClosure E x` | `algebraMap_mem_galoisClosure E x` |
| `relativeHerbrandPsi K₀ K Ω hbase E v` | `relativeHerbrandPsi E v` |
| `localRelativeHerbrandPsi K Ω E v` | Local-field entry point with `K₀ = K` |
