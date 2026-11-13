# Generator values on an isomorphic standalone field

Author: Worker 5093. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. In Deligne's global
argument (1973, §4.12) the generator at the distinguished place is attached to a finite
intermediate field `L` of the common closure of `F`. That field is isomorphic over `F` to the
completion `E` of a global field, and the completion lives in a different universe. This unit
evaluates the generator value through such an isomorphism. It does not use the image of `E` in
the common closure, which would only be conjugate to `L`.

Everything is in `Langlands.LocalFactor.NonabelianBrauer`. Fix a prime `p`, a p-adic field
`F : PadicField.{uF} p`, a p-adic field `E : PadicField.{uE} p` in an independent universe and a
`ℚ_p`-embedding `f : F →ₐ[ℚ_p] E`, which makes `E` an `F`-algebra
(`Weil.Local.extensionAlgebra F E f`). For a finite intermediate field `L : Extension F` of the
common closure `AlgebraicClosure F`, `L.field` carries the `ℚ_p`-algebra structure of its
standalone repackaging `L.asPadicField` (the local instance `generatorTransportAlgebra`).

## Definition

- `embeddingTraceCharacter F E f ψF`: the additive character `ψF ∘ Tr_{E/F}` of `E` for a
  nontrivial additive character `ψF` of `F`. The trace is taken for the `F`-algebra structure
  given by `f`. It is the published `TopologicalData.traceCharacter`, defined in the same way as
  `SystemEpsilon.standaloneTraceCharacter`, which requires `E` and `F` in one universe.

## Results

Let `σ : E ≃ₐ[ℚ_p] L` and suppose `σ` lies over `F`: for every `a ∈ F`, `σ (f a)` is
`a ∈ AlgebraicClosure F` (hypothesis `hσ`).

- `botEquiv_trace_eq_of_algEquiv`: for `y ∈ L` and `⊥ ≤ L`, the trace of `y` from `L` to the
  bottom field `⊥ = baseExtension F`, read in `F` through `IntermediateField.botEquiv`, is
  `Tr_{E/F}(σ⁻¹ y)`. Proof: the published `Algebra.trace_eq_of_equiv_equiv`, applied to the ring
  isomorphisms `F ≃ ⊥` and `σ : E ≃ L`. These are compatible with the two algebra maps by `hσ`.
- `traceCharacter_eq_additiveCharacter_of_algEquiv`: if `ψ` is the bottom-field character of
  `ψF` (`IsBaseCharacter F ψF ψ`), then the trace character
  `traceCharacter F (baseExtension F) L h ψ` on `L` is the transport along `σ` of
  `embeddingTraceCharacter F E f ψF`
  (`PadicField.ConductorTransport.additiveCharacter E L.asPadicField σ`). Proof: evaluate both
  sides at `y`, unfold `IsBaseCharacter` and apply the previous item.
- `generatorValue_eq_epsilon_of_algEquiv` (**generator values through a field
  isomorphism**): let `g : Generator F (baseExtension F)` and let `σ : E ≃ₐ[ℚ_p] g.extension` lie
  over `F`. Suppose the two characters of `g` are transports along `σ` of quasicharacters `η`,
  `η'` of `E`. That is, `g.first = ConductorTransport.quasicharacter E L σ η`, and likewise
  `g.second` with `η'`. Let `ψ` be the bottom-field character of `ψF`. Then for every family
  of Haar measures `measures` and every Haar measure `μE` on `E`,

  `generatorValue F (baseExtension F) ψ measures g =
    ε(η, ψF ∘ Tr_{E/F}, μE, 0) / ε(η', ψF ∘ Tr_{E/F}, μE, 0)`

  where `ε = PadicAbelian.epsilon E.canonicalTopologicalData` is Tate's local constant on `E`.
  Proof: by the published `abelianEpsilonRatio_haarIndependent`, compute the generator value as
  the epsilon ratio on `L` for the transported Haar measure
  `PadicField.AbelianTransport.haarMeasure E L σ μE`. Rewrite the trace character by the
  previous item. The published cross-universe transport
  `PadicField.AbelianTransport.abelianEpsilonExpression_eq` moves each factor to `E`. Finally,
  `PadicAbelian.abelianEpsilonExpression_normalizedAbsPower_mul` at `s = 0` identifies the
  abelian epsilon expression of `|·|⁰ · χ = χ` with `ε(χ, ψ, μE, 0)`.

## Provenance

These are internal transport lemmas. They follow the published same-universe statement
`generatorValue_standaloneGenerator` (`BrauerKernel.StandaloneBridge`). The image of `E` in
the common closure is replaced by an arbitrary `F`-isomorphic intermediate field, and the field
universes are independent. Tate's local constants are invariant under isomorphisms of local
fields, compatibly with the additive character and the Haar measure. Their role in the global
argument follows Deligne, *Les constantes des équations fonctionnelles des fonctions L* (1973),
proof of Lemma 4.12.
