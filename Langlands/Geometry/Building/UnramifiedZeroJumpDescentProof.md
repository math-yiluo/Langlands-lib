# Zero-value root jumps descend over the maximal unramified extension: the proof

## Statement proved

`Langlands.Geometry.Building.unramifiedZeroJumpDescent :
UnramifiedZeroJumpDescentStatement.{u}`. It has no hypotheses. The statement is defined and
explained in `Langlands/Geometry/Building/UnramifiedAffineRootRestrictionReduction.lean` and its
Markdown.

Informally: let `F` be a non-archimedean local field and `K = F^ur`. Let `G` be connected
reductive with a maximal split torus `S`, and let `T ⊇ S` be a torus that becomes maximal split
over `K`. Let `x` be an `Aut(K/F)`-fixed point of a KP apartment of `(G_K, T_K)`. Suppose a
root `χ` of `(G_K, T_K)` restricts to a relative root `α` of `(G, S)` and has a filtration jump
at `0` for `x`. Then `α` has a filtration jump at `0` for the restricted valuation `φ x`. This
is a pointwise form of the converse part of Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach*, Proposition 9.4.28.

## Declarations

### `unramifiedZeroJumpGaloisDescent`

This is the descent principle for zero-value jumps. Let `F`, `K = F^ur`, `G` and `S` be as
above, let `α` be a root of `(G, S)`, and let `ψ` be a family of root functions of
`(G_K, S_K)`. Suppose that, on the root group `U_{α_K}(K)`, the function `ψ_{α_K}` satisfies:

* (H1) the ultrametric inequality `min (ψ g) (ψ h) ≤ ψ (g h⁻¹)`;
* (H2) invariance under the coefficient action of every `σ ∈ Aut(K/F)`;
* (H3) invariance under conjugation by the points of `S_K` at which every rational character
  has valuation one (for the normalized valuation `MaximalUnramified.valuation F` of `K`).

Then a jump of `α_K` at `0` for `ψ` gives a jump of `α` at `0` for `fieldRestrict ψ`.

The Lean type is the hypothesis `hdesc` of `unramifiedZeroJumpDescent_of_galoisDescent`
(module `UnramifiedZeroJumpDescentAssembly`), copied verbatim. It is a separate theorem so that
other developments with the same hypothesis can use it by name.

The proof fixes `F`, `G`, `S` and `α`, and applies
`MaximalUnramified.isRootFiltrationJump_fieldRestrict_of_linearization` (module
`UnramifiedZeroJumpGaloisDescent`) at `r = 0` to `ψ` and the three hypotheses. Its
linearization hypothesis `RootGroupLinearization iS α (MaximalUnramified.valuation F)` is
supplied by `rootGroupLinearization` (module `RootGroupLinearizationProof`). That theorem needs:

* `IsSplitTorus S.toGrp`, from `hiS.isSplitSubtorus.1`;
* `[Mono iS.hom.hom.left]`, from `mono_of_isMaximalSplitTorus hiS`;
* `RelativeRoot.HasOppositeFactorPairs iS`, from
  `RelativeRoot.exists_oppositeFactorPair_of_componentReductivity` applied to the published
  `RelativeRoot.kernelCentralizerComponentReductive`.

The instances `IsAffineHom G.X.hom` and `Smooth G.X.hom` come from `hG`. They are introduced
with `have`, since they are propositions.

### `unramifiedZeroJumpDescent`

This is the target. It is `unramifiedZeroJumpDescent_of_galoisDescent` applied to
`unramifiedZeroJumpGaloisDescent`. That reduction passes a jump of `χ` to a jump of `α_K` for
the torus restriction `ψ x` (module `TorusRestrictedRootJump`). It checks (H1)–(H3) for `ψ x`
(module `TorusRestrictedRootInvariance`), applies the descent principle, and uses that `φ x` is
`fieldRestrict (ψ x)`.

## Supporting modules

These modules are new and are integrated with this proof:

* `Langlands/Geometry/Building/TorusRestrictedRootJump`: a jump of `χ` gives a jump of `α_K`
  for the torus restriction.
* `Langlands/Geometry/Building/TorusRestrictedRootInvariance`: (H1)–(H3) for the torus
  restriction.
* `Langlands/Geometry/Building/UnramifiedZeroJumpDescentAssembly`: the reduction
  `unramifiedZeroJumpDescent_of_galoisDescent`.
* `Langlands/Geometry/Building/UnramifiedFixedPointRootDescent`: Galois-fixed root-group points
  over `F^ur` descend to `F`, and unit torus points with prescribed character values.
* `Langlands/Geometry/Building/RootGroupLinearization` (Worker 47): the definition of the
  linearization hypothesis.
* `Langlands/Geometry/Building/RootGroupLinearizationProof`: `rootGroupLinearization`.
* `Langlands/GroupScheme/FilteredTraceDescent` (Worker 47): the abstract trace descent of
  filtration jumps.
* `Langlands/Geometry/Building/UnramifiedZeroJumpGaloisDescent` (Worker 47):
  `MaximalUnramified.isRootFiltrationJump_fieldRestrict_of_linearization`.

Each module's Markdown explains its proofs.

## Implementation notes

The descent principle is proved by a `fun` against its stated type. The proof does not unfold
that type, and the module compiles at the default heartbeat limit. The axioms used are
`propext`, `Classical.choice` and `Quot.sound`.
