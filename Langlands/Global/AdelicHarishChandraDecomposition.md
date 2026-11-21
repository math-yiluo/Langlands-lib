# Harish-Chandra decomposition by constant terms

Module `Langlands.Global.AdelicHarishChandraDecomposition`. Main results:
`Langlands.Global.StandardParabolicFamily.sum_hcComponent` and
`Langlands.Global.StandardParabolicFamily.isCuspidalAlong_hcComponent`. Their statement form is
`Langlands.Global.HarishChandraDecompositionStatement`, proved by
`Langlands.Global.harishChandraDecomposition`.

## Statement

Let `𝓕 : StandardParabolicFamily F G` be a compatible standard parabolic family of a connected
reductive group `G` over a number field `F`, in an arbitrary universe `u`. Let
`f : ContinuousRationalFunctions F G` be a continuous complex function on `G(𝔸)` that is invariant
under left translation by `G(F)`. For a finite set `P` of characters, define

`𝓕.hcComponent P f = Σ_{S ⊆ P} (−1)^{|P ∖ S|} • 𝓕.constantTerm (𝓕.finsetIndex S) f`.

Here `𝓕.finsetIndex S` is the standard index `S ∩ Δ₀`, and `Δ₀` is the set of simple relative
roots. `𝓕.simpleRootFinset` is `Δ₀` as a finset. `𝓕.constantTerm` is the Library's constant term
(`AdelicGroupPoints.subgroupConstantTerm`, normalized measure, chosen representatives). The
statement asserts two things:

1. `Σ_{P ⊆ Δ₀} 𝓕.hcComponent P f = f` as functions on `G(𝔸)`.
2. For every finite `P`, `𝓕.IsCuspidalAlong (𝓕.finsetIndex P) (𝓕.hcComponent P f)` holds. This is
   the Library predicate: `𝓕.constantTerm Q (𝓕.hcComponent P f) = 0` for every standard index
   `Q` strictly contained in `P ∩ Δ₀`.

Both are pointwise identities of functions. No orthogonality, growth or `L²` statement is made.

## Combinatorics (namespace `Langlands.Global.HarishChandraDecomposition`)

For `c : Finset α → M` with `M` a complex vector space, `alternatingSum c P` is
`Σ_{S ⊆ P} (−1)^{|P ∖ S|} • c S`.

- `alternatingSum_insert`: for `a ∉ P`,
  `alternatingSum c (insert a P) = alternatingSum (c ∘ insert a) P − alternatingSum c P`. The
  proof splits the powerset of `insert a P` with `Finset.sum_powerset_insert`.
- `sum_alternatingSum` (Möbius inversion):
  `Σ_{P ⊆ D} alternatingSum c P = c D`, by induction on `D` generalizing `c`, using the previous
  identity.
- `alternatingSum_eq_zero`: if `a ∈ P` and `c (insert a S) = c S` for all `S ⊆ P ∖ {a}`, the
  alternating sum over `P` vanishes.

## Adelic part (namespace `Langlands.Global.StandardParabolicFamily`)

- `finite_simpleRoots`, `simpleRootFinset`, `finsetIndex`. Also
  `finsetIndex_simpleRootFinset : finsetIndex Δ₀ = top`.
- `constantTerm_top`: `𝓕.constantTerm 𝓕.top φ = φ` for every function `φ`. The radical of the
  top index is the standard unipotent subgroup of all simple roots (`range_radical_eq_standardUnipotent`).
  That subgroup is trivial (`standardUnipotent_simple_eq_bot`), so the average of `φ` is `φ`
  (`ConstantTermComposition.average_eq_self`).
- `sum_hcComponent` (statement part 1): Möbius inversion with `c S = C_{S ∩ Δ₀} f`, then
  `constantTerm_top`.
- `continuous_constantTerm` and `isRationalInvariant_constantTerm`. For `f` as above, `C_Q f` is
  continuous. It is also invariant under the rational points of every standard radical `U_R`:
  `U_R ≤ U_{R∩Q}`, and `U_{R∩Q}` normalizes `U_Q`.
- `integrable_out_of_isRationalInvariant`: the representative integrand of a continuous
  `U(F)`-invariant function equals a continuous function on the compact quotient. It is therefore
  integrable for the probability measure.
- `constantTerm_hcComponent`: by linearity of the integral (the integrability above) and the
  composition rule `constantTerm_constantTerm` (module `AdelicConstantTermComposition`),
  `C_Q f_P = Σ_{S ⊆ P} (−1)^{|P ∖ S|} C_{Q ∩ (S ∩ Δ₀)} f`.
- `isCuspidalAlong_hcComponent` (statement part 2): for `Q ⊊ P ∩ Δ₀`, choose `a ∈ P ∩ Δ₀` with
  `a ∉ Q`. The index `Q ∩ ((S ∪ {a}) ∩ Δ₀)` equals `Q ∩ (S ∩ Δ₀)`, so the alternating sum
  vanishes by `alternatingSum_eq_zero`.

## Provenance

Joseph Bernstein and Erez Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), 187–234, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §7.3 (p. 214). They state the direct
sum decomposition `L¹_loc(Z) = ⊕_P L¹_loc,cusp(Z_P)` with projections
`Σ_{Q ⊆ P} (−1)^{dim 𝔞_Q^P} CT_Q`. Here `dim 𝔞_Q^P = |Δ^P ∖ Δ^Q|`, which is the exponent
`|P ∖ S|` above. This module proves the two facts behind that decomposition: the components sum to
`f`, and each component is cuspidal. They are proved pointwise for continuous `G(F)`-invariant
functions, not on `L¹_loc(P₀(F)\G(𝔸))`. Directness of the sum, the projection property, and any
weighted `L²` bound are not proved here.
