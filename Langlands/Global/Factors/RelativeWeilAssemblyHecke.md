# Hecke functional equations as functional-equation packages

## Contents

This module supports the proof of
`Langlands.Global.FunctionalEquationComparison.RelativeWeilTwistFunctionalEquationStatement`.
It turns the Hecke global functional equation into the published package
`RelativeWeilEngine.HasGlobalEquation` (`Langlands.Global.Factors.RelativeWeilEngine`).
The Hecke global functional equation is the published proposition
`HeckeGlobalFunctionalEquationStatement` (`Langlands.Global.Factors.HeckeFunctionalEquationStatement`).
It is an explicit hypothesis `hH` of the results that need it and is not proved here. All
names are in namespace `Langlands.Global.FunctionalEquationComparison.RelativeWeilEngine`;
`K` is a number field.

### Factors

- `heckeL χ v s`: the finite Hecke L-factor
  `PadicAbelian.lFactor (CompletionPadic.topologicalData v) (χ.finiteComponent v) s`, as in the
  Hecke statement.
- `heckeInfiniteDenominator dR dC s`: the product of the denominators of the archimedean
  L-factors of the presentations `dR` (real places) and `dC` (complex places).
  `heckeInfiniteEpsilon dR dC aR aC s` is the archimedean epsilon factor. Both are written
  exactly as in the Hecke statement.
- `nonzeroMeromorphic_denominator`: the denominator of a published `ReciprocalEntire` function
  has nonzero germ everywhere. `nonzeroMeromorphic_heckeInfiniteDenominator` follows.

### The package of one Hecke character

- `hasGlobalEquation_of_heckeFE` (hypothesis `hH`): fix `χ`, a nontrivial character `ψ` of
  `A_K` trivial on `K`, and all the local data quantified in the Hecke statement. These are
  finite additive components `ψf` with self-dual measures `μ`, archimedean additive data
  `aR`, `aC`, and presentations `dR`, `dR'`, `dC`, `dC'` of the archimedean components of `χ`
  and `χ⁻¹`. Then there is a finite set `S` of finite places outside which the finite epsilon
  factors `HeckeFunctionalEquation.finiteEpsilon χ ψf μ` are `1`, and
  `HasGlobalEquation (heckeL χ) (heckeL χ⁻¹) (finiteEpsilon χ ψf μ) A Ad Ae S`. Here
  `A = 1 / heckeInfiniteDenominator dR dC`, `Ad = 1 / heckeInfiniteDenominator dR' dC'` and
  `Ae = heckeInfiniteEpsilon dR dC aR aC`.
- `nonempty_selfDualHaar`: every nontrivial additive character of a finite completion admits
  a self-dual Haar measure, as required by the Hecke statement.
- `ofCanonicalCharacter v ψ'`: an additive character of `padicField v` in its canonical
  topology (the published `Correspondence.NontrivialAdditiveCharacter`), read as a character
  in the completion topology used by the Hecke statement. The two topologies are equal
  (`CompletionPadic.completion_topology_eq`). `ofCanonicalCharacter_toAddChar` states that the
  underlying additive character is unchanged.

### Archimedean data

- `HeckeArchData χ ψ`, the main definition: a structure holding the archimedean data of the
  Hecke statement for `χ` and `ψ` (`aR`, `aC` with their component properties; `dR`, `dR'`,
  `dC`, `dC'` with their presentation properties). It has the archimedean functions `A`, `Ad`,
  `Ae` as above, with `nonzeroMeromorphic_A`, `nonzeroMeromorphic_Ad` and
  `nonzeroMeromorphic_Ae`.
- `HeckeArchData.ofInfiniteComponent_eq`: the same data serve a character `χ'` with the same
  archimedean components as `χ`. The functions `A`, `Ad`, `Ae` are unchanged
  (`ofInfiniteComponent_eq_A`, `_Ad`, `_Ae`). This makes the archimedean block independent of a
  twist with trivial archimedean components.
- `nonempty_heckeArchData` (hypothesis `hH`): the first conjunct of the Hecke statement
  provides such data for every `χ` and every nontrivial `ψ` trivial on `K`.
- `hasGlobalEquation_of_heckeArchData` (hypothesis `hH`): `hasGlobalEquation_of_heckeFE` with
  the data of a `HeckeArchData`.

### Regrouping over the places below

For a finite extension `L / K`:

- `placesAbove L p`: the finite places of `L` above the finite place `p` of `K`, as a finite
  set. `mem_placesAbove`: `q ∈ placesAbove L p ↔ q.under (𝓞 K) = p`.
- `HasGlobalEquation.pushforwardPlaces`: a package on the finite places of `L` with exceptional
  set `S`, whose epsilon factors are `1` off `S`, gives a package on the finite places of `K`.
  Its local factors at `p` are the products over `placesAbove L p`. Its exceptional set is any
  finite set `T` containing the places under `S`.

## Source and provenance

John Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33, Part II (1979), 3–26
(registered `tate-1979-number-theoretic-background`), Theorem (3.5.3) and the paragraph after
it, printed p.16 (PDF p.25). The functional equation of a Weil-group L-function is obtained by
multiplying Hecke functional equations and regrouping places. This module is internal
bookkeeping: it repackages the published Hecke statement in the format of the published
engine and adds no mathematical content beyond it. The convergence and nonvanishing of the
Hecke Euler products come from the published `HeckeEulerProduct.exists_hasProd_lFactor`. The
self-dual measures come from the published `HarmonicAnalysis.padicSelfDualMeasureExists`.

## Proof

- `nonzeroMeromorphic_denominator`: an entire function is meromorphic everywhere, and it has
  finite order at a point where it is nonzero. On the connected plane, finite order then holds
  everywhere (`MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected`).
- `hasGlobalEquation_of_heckeFE`: the Hecke statement gives `σ`, `Λ`, `Λd`, `S`, meromorphy
  of `Λ`, `Λd`, the Euler products `HasProd (heckeL χ · s) (Λ s · D s)` on `σ < Re s`, `ε_v = 1`
  off `S`, and the functional equation off a codiscrete set. Here `D` is the archimedean
  denominator. The package uses `Λ · D` and `Λd · D'`. They are meromorphic because `D` and
  `D'` are entire. They are nonzero on a right half-plane, by uniqueness of product limits and
  the nonzero limits of `HeckeEulerProduct.exists_hasProd_lFactor` for `χ` and `χ⁻¹`. The
  germ identity follows from the codiscrete functional equation (`meromorphicEq_of_codiscrete`)
  after cancelling `D` and `D'(1 - s)`, which are nonzero on punctured neighbourhoods
  (`NonzeroMeromorphic.eventually_ne_zero`, `NonzeroMeromorphic.reflect`).
- `nonempty_selfDualHaar` applies `HarmonicAnalysis.padicSelfDualMeasureExists` in the
  topological data `CompletionPadic.topologicalData v`.
- `ofCanonicalCharacter` rewrites the topology in the continuity field with
  `completion_topology_eq`.
- `HeckeArchData.nonzeroMeromorphic_Ae`: the archimedean epsilon factors are entire
  (`RealCharacterData.differentiable_epsilon`, `ComplexCharacterData.differentiable_epsilon`)
  and unit-valued, so `nonzeroMeromorphic_of_ne_zero_halfPlane` applies.
  `ofInfiniteComponent_eq` rewrites the presentation properties with the equality of
  archimedean components (and `infiniteComponent_inv`).
- `nonempty_heckeArchData` chooses the archimedean data from the first conjunct of the Hecke
  statement for `χ` and for `χ⁻¹`.
- `HasGlobalEquation.pushforwardPlaces`: first enlarge the exceptional set from `S` to the
  places above `T` with `HasGlobalEquation.changeSet`; the epsilon factors there are `1`. Then
  apply `HasGlobalEquation.pushforward` along `q ↦ q.under (𝓞 K)` with fibres `placesAbove`.
