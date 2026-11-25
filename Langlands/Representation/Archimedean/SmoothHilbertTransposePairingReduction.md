# Reduction of the real smooth Hilbert transpose pairing to three inputs

`Langlands.Archimedean.realSmoothHilbertTransposePairing_of_casselmanWallach` proves the published [real smooth Hilbert pairing proposition](SmoothHilbertTransposePairingStatement.md), **conditionally** on these three propositions:

1. `RealSmoothCasselmanWallachExtensionStatement`, the [extension of an intertwiner](SmoothCasselmanWallachStatement.md) of compact-finite vectors to the genuine smooth carriers;
2. `RealSmoothHilbertHarishChandraModuleStatement`, the [induced Harish-Chandra module structure](SmoothHarishChandraModuleStatement.md) on the compact-finite smooth vectors of the given Hilbert representation;
3. `RealSmoothHilbertDualHarishChandraStatement`, a [nonzero intertwiner](SmoothHilbertDualHarishChandraStatement.md) from that module into the genuine smooth vectors of the inverse-transpose twisted continuous dual.

The theorem keeps the Hilbert carrier universe `uH` free and uses the first proposition at `.{uH,uH,uH}`. These are explicit premises, not new axioms or theorems established here. There is no assumed Hilbert globalization of an abstract module and no use of the final algebraic transpose-pairing theorem.

## Implemented proof

Use the Harish-Chandra module input for the given irreducible admissible Hilbert representation `R` and then take its nonzero compact-finite intertwiner `f` from the dual input. Set `S = (continuousDualRepresentation R) ∘ θ`, with `θ(g) = (g⁻¹)ᵀ`. The already published continuity result for the continuous dual of a jointly continuous Hilbert representation, composed with continuity of `θ`, proves `isContinuousRepresentation_inverseTransposeDual`. The extension input applies to `H` and `StrongDual ℂ H`, with `V = smoothHilbertKFinite ℝ n R` identified by the identity with `smoothKFinite ℝ n R`. This gives a continuous equivariant `T : D(R) →L[ℂ] D(S)` extending `f`.

The pairing construction also works over the general matrix model `F : Type` with `RCLike F`. Write `ε_R` and `ε_S` for the empty-word coordinate maps `derivativeCLM … []`, which send smooth vectors to their values in the underlying spaces. Define the complex bilinear form `smoothDualTwistPairing F n R T` by

`B(y,x) = ε_S(T x)(ε_R y)`.

For fixed `x`, separate continuity is composition of the continuous coordinate `ε_R` with the continuous functional `ε_S(T x)`. For fixed `y`, it is composition of `T`, `ε_S`, and continuous evaluation at `ε_R y`. If `T` is equivariant, then `T(R∞(θ(g)) x) = S∞(θ(g))(T x)`. Because `θ² = 1`, this latter action, viewed in the continuous dual, is `L ↦ L ∘ R(g⁻¹)`. Evaluating on `ε_R(R∞(g)y)` cancels `R(g⁻¹)R(g)`. This gives the exact invariance and variable order required by `IsSmoothHilbertTransposePairing`.

The empty-word coordinate is injective by `toSmooth` and the empty iterated derivative identity (`derivativeCLM_nil_injective`). The range of `ε_R` is norm dense by the published Banach smoothing density theorem, applied with Haar measure on the matrix units group, and surjectivity of `toSmooth` (`denseRange_derivativeCLM_nil`). If `T x ≠ 0`, injectivity gives a nonzero continuous functional `ε_S(T x)`. It cannot vanish on the dense range of `ε_R`, so `smoothDualTwistPairing_ne_zero` gives `B ≠ 0`. In the real reduction, some `f(v) ≠ 0` and `T(e(v)) = f(v)` supply the needed `x`. This density step is in the Hilbert norm, not a claim of compact-finite density in the smooth topology.

## Provenance

This is a derived evaluation argument motivated by Aizenbud–Gourevitch, *Generalized Harish-Chandra descent and applications to Gelfand pairs*, arXiv:0803.3395v7, `aizenbud-gourevitch-2009-generalized-harish-chandra-descent-v7` (SHA256 `a789936fffe560b9295c666f420a3cf7c69a475192bace2e5c2c4c3d975d7dfd`), Theorem 8.2.1 (p.23). Instead of importing the source's smooth contragredient isomorphism, the implemented proof evaluates a genuine smooth vector of the twisted Banach dual after extending an algebraic intertwiner. The sources for the three analytical and algebraic premises are given in their linked files. No character theorem, Casselman–Wallach theorem, or unconditional pairing existence is proved by this module.
