# Harris's transfer `JL(π_f)` from `GJ` to `GG`

Author: Worker 5443.

This pair defines the relation "`ρ'` is `JL(ρ)`" between representations of
the finite adelic points of Harris's two unitary similitude groups `GJ` and
`GG`. It specializes the generic away-transfer relation
`Langlands.JacquetLanglands.IsAwayTransfer` (module
`Langlands.JacquetLanglands.AwayTransfer`). The splittings and the
identification of complements come from the published module
`Langlands.JacquetLanglands.HarrisAwaySplitting`, and the local relation at
the distinguished place is the published local Jacquet–Langlands relation
`Langlands.JacquetLanglands.IsJacquetLanglandsPair` (module
`Langlands.JacquetLanglands.Relation`). Entry declaration:
`Langlands.JacquetLanglands.IsHarrisJacquetLanglandsTransfer`.

## Source

M. Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39 (1999); literature ID
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`.

§5, printed p. 312 (one-based PDF page 14):

> Let π be a representation of GJ, and let π_v be its constituent at the chosen
> place v, as in [H1, H2]; π_v is a representation of GL(n, 𝒦_v). Suppose π_v
> is supercuspidal. Let JL(π_f) be the corresponding irreducible admissible
> representation of GG(A_f); the local constituents of JL(π_f) and π_f are the
> same except at v, where they correspond by the local Jacquet-Langlands
> correspondence [DKV, R], also denoted JL(•).

§4, printed pp. 308–309 (PDF pp. 10–11) fixes the setting: `p` splits in the
imaginary quadratic field `𝒦₀`, `v = v^(1)` is a prime of `𝒦` of residue
characteristic `p` with `inv_v(ℬ) = 1/n`, "`𝒟` and `ℬ` are isomorphic away
from `v` and their complex conjugates", `GJ_p` is identified with
`∏_j (𝒟_j)ˣ × ℚ_pˣ` in (4.2), and the level of `GG` is defined "via an
identification `GG(A_f^p) ≅ GJ(A_f^p)`". `GJ` is the group of the algebra `𝒟`,
which is split at `v`; `GG` is the group of `ℬ`, which is a division algebra at
`v`, because a central simple algebra of degree `n` with local invariant `1/n`
(of order `n`) is a division algebra.

## Correspondence with Harris's notation

The notation is that of `HarrisAwaySplitting.md`:

- `𝒦₀` is `F`, `𝒦` is `K` (quadratic over the totally real `E`), with
  `ι : F →+* K`; `p`, `hp : p.Prime`, the place `v` of `ℚ` above `p`, a degree-one
  place `𝔭` of `F` above `v` with `h𝔭`; Harris's distinguished place `v = v^(1)`
  is `w₀ : FinitePlacesAbove K 𝔭.1`, and `𝒦_v` is the completion
  `w₀.1.adicCompletion K`, written `K_{w₀}` below.
- `GJ` is `σD.rationalInvolution` for `σD : SecondKindInvolution E K D` (Harris's
  `𝒟` is `D`); `GG` is `σB.rationalInvolution` for
  `σB : SecondKindInvolution E K B` (Harris's `ℬ` is `B`). Their `A_f`-points are
  `σD.rationalInvolution.FiniteAdelicPoints` and
  `σB.rationalInvolution.FiniteAdelicPoints`.
- Harris's `π_f` is `ρ`, a representation of `GJ(A_f)`; `JL(π_f)` is `ρ'`, a
  representation of `GG(A_f)`; `π_v` is the constituent of `ρ` at `w₀`, a
  representation of `GL_n(K_{w₀})`.
- The local identifications are explicit inputs:
  - `s : K_{w₀} ⊗[K] D ≃ₐ[K_{w₀}] Matrix (Fin n) (Fin n) K_{w₀}`, the splitting of
    `𝒟` at `v` that makes `π_v` a representation of `GL(n, 𝒦_v)`;
  - a central division algebra `Δ` over `K_{w₀}` and
    `t : K_{w₀} ⊗[K] B ≃ₐ[K_{w₀}] Δ`, which presents `ℬ_v` as a division ring so
    that the local relation `IsJacquetLanglandsPair` applies;
  - `f w : K_w ⊗[K] D ≃ₐ[K_w] K_w ⊗[K] B` for the places `w ≠ w₀` above `𝔭`, and
    `e : A_f^p ⊗[ℚ] D ≃ₐ A_f^p ⊗[ℚ] B` with `he` (intertwining the involutions),
    which give Harris's identifications of the two groups away from `v`
    (`harrisComplementEquiv`, see `HarrisAwaySplitting.md`).

## Declarations

All declarations are in namespace `Langlands.JacquetLanglands`.

### Auxiliary constructions

- `factorUnitsAlgEquiv t`, for an `S`-algebra isomorphism
  `t : S ⊗[K] B ≃ₐ[S] Δ` onto an `S`-algebra `Δ` with `IsModuleTopology S Δ`, is
  the induced isomorphism of topological groups
  `ImaginaryQuadraticSplit.FactorUnits K B S ≃ₜ* Δˣ` (`Units.mapEquiv`). Both
  directions are continuous because `S`-linear maps between module topologies
  are continuous (`IsModuleTopology.continuous_of_linearMap`) and `Units.map` of
  a continuous monoid map is continuous; this is the argument of the published
  `factorUnitsEquiv` and `factorUnitsMatrixEquiv`. `factorUnitsAlgEquiv_apply_val`:
  the underlying element is `t x` (`rfl`).
- `completionJacquetLanglandsPair w n Δ X X' π π'`, for a finite place `w` of a
  number field `K`, a central division algebra `Δ` over `K_w` (finite-dimensional,
  `Algebra.IsCentral`, `IsModuleTopology`), `X X' : ModuleCat ℂ`,
  `π` a representation of `GeneralLinear n K_w` on `X` and `π'` a representation
  of `Δˣ` on `X'`, is `IsJacquetLanglandsPair K_w Δ n π π'`. The instances
  `ValuativeRel K_w` and `IsNonarchimedeanLocalField K_w` are those of the
  published `Langlands.Global.CompletionPadic.topologicalData w`, whose topology
  is the completion topology of `K_w`. This is the local relation in the shape
  `IsAwayTransfer` requires (constituent spaces are objects of `ModuleCat ℂ`).
- `isAdmissible_trivial G`: the trivial representation of a topological group
  on `ℂ` is admissible (smooth, with every vector fixed by the open subgroup
  `⊤`; every subspace of `ℂ` is finite-dimensional).
- `trivialEquivSplitTensor Φ π σ hπ hσ`: for a splitting `Φ : G ≃ₜ* L × H` and
  representations `π`, `σ` on `ℂ` acting trivially, the trivial representation of
  `G` on `ℂ` is isomorphic to `splitTensor Φ π σ`, through
  `(TensorProduct.lid ℂ ℂ).symm : ℂ ≃ ℂ ⊗[ℂ] ℂ`.
- `harrisAwaySplitAlg σB ι p hp v 𝔭 h𝔭 w₀ t : GG(A_f) ≃ₜ* Δˣ ×
  HarrisAwayComplement σB ι p v 𝔭 w₀` is the published `harrisAwaySplit` for `GG`
  followed by `factorUnitsAlgEquiv t` on the factor at `w₀`. It is the analogue
  for `GG` of the published `harrisAwaySplitGL` for `GJ`.
  `harrisAwaySplitAlg_apply_fst`: the `w₀`-factor of `g` is `t` applied to the
  `w₀`-component of the published `σB.splitPlacePoints ι v.1 𝔭 h𝔭` of the local
  point `σB.rationalInvolution.finiteLocalMap v.1 g` (from the published
  `harrisAwaySplit_apply_fst`). `harrisAwaySplitAlg_apply_snd`: the complement
  component is that of `harrisAwaySplit` (`rfl`).

### The transfer relation

`IsHarrisJacquetLanglandsTransfer σD σB ι p hp v 𝔭 h𝔭 w₀ n s Δ t f e he ρ ρ'`,
for representations `ρ` of `GJ(A_f)` on `V` and `ρ'` of `GG(A_f)` on `V'`
(complex vector spaces in the same universe), is the conjunction of:

1. `ρ` is irreducible (`Representation.IsIrreducible`);
2. `ρ` is admissible (the Library's `IsAdmissible`: smooth, and the fixed
   vectors of every open subgroup form a finite-dimensional space);
3. `ρ'` is irreducible;
4. `ρ'` is admissible;
5. `IsAwayTransfer (harrisAwaySplitGL σD ι p hp v 𝔭 h𝔭 w₀ s)
   (harrisAwaySplitAlg σB ι p hp v 𝔭 h𝔭 w₀ t)
   (harrisComplementEquiv σB σD ι p v 𝔭 w₀ f e he)
   (completionJacquetLanglandsPair w₀.1 n Δ) ρ ρ'`.

Unfolding condition 5 with `AwayTransfer.md`: there are complex vector spaces
`X, X', Y`, a representation `π` of `GL_n(K_{w₀})` on `X`, a representation `π'`
of `Δˣ` on `X'` and a representation `σ` of
`HarrisAwayComplement σD ι p v 𝔭 w₀` on `Y` such that

- `IsJacquetLanglandsPair K_{w₀} Δ n π π'` holds, so `finrank_{K_{w₀}} Δ = n²`,
  `π` is irreducible and essentially square-integrable, `π'` is irreducible, and
  `Θ_π(g) = (-1)^{n-1} Θ_{π'}(g')` for corresponding regular elliptic `g ↔ g'`
  (see `Relation.md`);
- `ρ` is isomorphic to `π ⊠ σ` pulled back along
  `harrisAwaySplitGL … s : GJ(A_f) ≃ₜ* GL_n(K_{w₀}) × HarrisAwayComplement`;
- `ρ'` is isomorphic to `π' ⊠ (σ ∘ θ⁻¹)` pulled back along
  `harrisAwaySplitAlg … t : GG(A_f) ≃ₜ* Δˣ × HarrisAwayComplement`, where
  `θ = harrisComplementEquiv σB σD ι p v 𝔭 w₀ f e he`.

So `ρ` and `ρ'` have the same constituent away from `v`, under Harris's
identifications `f`, `e`, and their constituents at `v` are related by the local
Jacquet–Langlands relation. This is Harris's sentence above, with "the
local constituents … are the same except at `v`" read as one common constituent
of the complement `HarrisAwayComplement`; the comparison with the placewise
reading is in `AwayTransfer.md` ("Source and provenance").

The inspected elaborated type of the definition, with its instance arguments,
ends in `Prop` (validation below).

### Lemmas

- `IsHarrisJacquetLanglandsTransfer.isIrreducible_left`, `.isAdmissible_left`,
  `.isIrreducible_right`, `.isAdmissible_right`, `.isAwayTransfer`: projections
  to conditions 1–5.
- `IsHarrisJacquetLanglandsTransfer.of_equiv_left`, `.of_equiv_right`: the
  relation depends only on the isomorphism classes of `ρ` and of `ρ'`. Proved
  with the published `isIrreducible_of_equiv` (module `Relation`),
  `isAdmissible_of_equiv` and `IsAwayTransfer.of_equiv_left`/`_right`.
- `isHarrisJacquetLanglandsTransfer_splitTensor` (constructor): for `π`, `π'`
  with `completionJacquetLanglandsPair w₀.1 n Δ X X' π π'` and any `σ`, the
  representations `splitTensor (harrisAwaySplitGL … s) π σ` and
  `splitTensor (harrisAwaySplitAlg … t) π' (σ ∘ θ⁻¹)` are related, as soon as both
  are irreducible and admissible (these four facts are hypotheses).
- `isHarrisJacquetLanglandsTransfer_trivial` (nonvacuity on concrete data): for
  `n = 1`, `Δ = K_{w₀}`, any `s : K_{w₀} ⊗[K] D ≃ₐ M_1(K_{w₀})`, any
  `t : K_{w₀} ⊗[K] B ≃ₐ K_{w₀}` and any `f`, `e`, `he`, the trivial
  representations of `GJ(A_f)` and `GG(A_f)` on `ℂ` are related. The proof
  checks all five conditions: irreducibility (published
  `isIrreducible_trivial`), admissibility (`isAdmissible_trivial`), and the
  away transfer with all three constituents trivial on `ℂ`, using
  `trivialEquivSplitTensor` and the published `isJacquetLanglandsPair_trivial_one`
  (the trivial representations of `GL_1(K_{w₀})` and `K_{w₀}ˣ` are
  Jacquet–Langlands related). This shows that the conjunction of the five
  conditions is satisfiable with the actual groups `GJ(A_f)`, `GG(A_f)` and the
  actual local relation, whenever such `s` and `t` exist. The theorem does not
  construct `s` or `t`.

## Hypotheses, normalizations and scope

- **Supercuspidality is not imposed.** Harris assumes `π_v` supercuspidal to
  define `JL(π_f)`. The relation here is stated for every pair; its local
  condition already requires `π` irreducible and essentially square-integrable,
  the domain of the local correspondence (DKV, Badulescu). A consumer working in
  Harris's situation adds supercuspidality of the constituent at `w₀` as a
  separate hypothesis.
- **Irreducible and admissible** are explicit conjuncts for both `ρ` and `ρ'`,
  matching Harris's "irreducible admissible representation of `GG(A_f)`"; they
  are imposed on `ρ` as well, so that the relation is between two irreducible
  admissible representations.
- **Existence and uniqueness of `JL(π_f)` are not asserted.** The definition is
  a relation; nothing here proves that a given `ρ` has a related `ρ'` or that it
  is unique up to isomorphism.
- **The identifications `s`, `t`, `f`, `e` are inputs.** Their existence (from
  Harris's assumptions that `𝒟` is split at `v`, that `inv_v(ℬ) = 1/n`, and that
  `𝒟` and `ℬ` are isomorphic away from `v`) is not formalized, and the relation
  is stated for the given choices. Independence of the choices (for example by
  Skolem–Noether, which changes `s` and `t` by inner automorphisms) is not
  proved.
- **The Hasse invariant is not formalized.** The relation only needs `Δ` to be a
  central division algebra over `K_{w₀}`; the condition
  `finrank_{K_{w₀}} Δ = n²` is part of `IsJacquetLanglandsPair`. Harris uses
  `inv_v(ℬ) = 1/n` to make `ℬ_v` a division algebra (and for the Drinfeld tower
  of §4, which is not part of this module).
- **Topologies.** `GL_n(K_{w₀})` has the units topology of the matrix topology,
  `Δ` carries its `K_{w₀}`-module topology (`IsModuleTopology`) and `Δˣ` the
  units topology, as in `Relation.md`; `factorUnitsAlgEquiv` and the published
  `factorUnitsMatrixEquiv` are homeomorphisms for these topologies.
- **Universes.** `Δ` lives in the universe of `K`, because
  `IsJacquetLanglandsPair F D n` takes `F` and `D` in one universe. The
  constituent spaces live in the universe of `V` and `V'`, as in `IsAwayTransfer`.
- **Local constituents away from `v`.** As in `AwayTransfer.md`, the places
  other than `v` are grouped into `HarrisAwayComplement`; the Library has no
  restricted-product decomposition of `GJ(A_f^p)`, so the placewise reading of
  Harris's condition (via Flath's theorem) remains a later obligation.

## Dependencies and validation

Imports: `Langlands.Global.CompletionPadic`,
`Langlands.JacquetLanglands.AwayTransfer`,
`Langlands.JacquetLanglands.HarrisAwaySplitting`,
`Langlands.JacquetLanglands.Relation` (all published). Environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`).

`lean_check` of the module in place, with declaration
`Langlands.JacquetLanglands.IsHarrisJacquetLanglandsTransfer` (record
`056e0d03-dc12-418d-b1f2-eec036376ab6`): 0 errors, 0 warnings. The inspection
reports a definition with `statement_returns_prop: true`, level parameters
`u v w z z' uV`, and axioms `propext`, `Classical.choice`, `Quot.sound` only.
