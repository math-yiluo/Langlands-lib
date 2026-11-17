# The height on the norm-one points of a Cartan cell

Authors: Worker 106 and Worker 128, task `7f9ba483-3cd4-4733-a87b-b5651bdbd06a` (Task 5461,
revision 1). Worker 106 wrote the module at the request of the task's first executor, Worker 128,
who uses it in the proof of Waldspurger's Corollary III.1.2 on actual rational points. Worker 128
wrote the general lemmas of the sections `AbstractHeight` and `BoundedFunctionals`
(`le_sum_abs_mul_of_subadditive`, `rationalPairingAt`, `rationalPairingAt_toRat`,
`exists_abs_pairing_le_of_span_eq_top`).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCartanCellHeight`,
namespace `Langlands.HarishChandraSchwartz`.

The module contains no `Prop`-valued statements. It contains one auxiliary definition, the linear
map `rationalPairingAt`, and proves six theorems: two general lemmas (subadditive functions along a
lattice homomorphism; propagation of linear bounds along a rational spanning set), the evaluation
lemma `rationalPairingAt_toRat`, two lemmas on cocharacters of a maximal split torus, and the main
bound **`exists_rationalHeight_le_of_mem_rationalCartanCell`**. The main bound says that the height
`σ` of a point `g` of `G¹` that lies in the Cartan cell of a cocharacter `y` is at most `C (1 + T)`,
where `T ≥ 0` bounds the absolute values of the pairings of `y` with the simple roots. Nothing is
assumed beyond the hypotheses written in each theorem. The proofs use no `sorry` and no new axioms.

## Provenance

This is an auxiliary lemma (derived content), not a numbered result of a source. It supplies one
step of the proof of Corollary III.1.2 in J.-L. Waldspurger, *La formule de Plancherel pour les
groupes p-adiques, d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333 (literature
id `waldspurger-2003-plancherel`), printed pp. 263–264. The proof (printed p. 264) reduces to points of
`Ā_0^+ ∩ G¹` and states: "comme `Re(χ) ∈ +a_P^{G*}` pour tout `χ ∈ Exp(π_P)`, il existe `C_3 > 0`
et `ε > 0` tels que `|χ(a)| ⩽ C_3 q^{-εσ(a)}` pour tout `χ ∈ E` et tout
`a ∈ Ā_0^+ ∩ A_M ∩ G¹`". Positivity of the exponents gives decay in terms of the pairings with the
simple roots. Passing to `σ(a)` needs that, on `G¹`, `σ` is bounded by a multiple of `1` plus the
size of these pairings. This module proves that comparison, for the points of `G¹` in the Cartan
cells used in the Library.

The proof is a version of the upper half of Waldspurger's I.1 (6), printed p. 242:
"`C_1(1 + |H_0(m)|) ⩽ 1 + σ(m) ⩽ C_2(1 + |H_0(m)|)`". Here the vector `H_0(m)` is controlled by
the simple roots and the restricted rational characters of `G`. The rational characters vanish on
`G¹`.

## Setting and notation

`F` is a nonarchimedean local field and `G` a group scheme over `Spec F` (with
`[IsAffineHom G.X.hom]` and `[LocallyOfFiniteType G.X.hom]`). `i : S → G` is a homomorphism from a
commutative group scheme and `ν` a cocharacter of `S`. `G(F) = rationalPoints G` carries the local
instances of `RationalWeights` (the topology `rationalPointTopology F G.X`).

- `σ = rationalHeight ρ`, the logarithm of the matrix norm of a matrix representation `ρ`. It
  satisfies `σ ≥ 0`, `σ(1) = 0`, `σ(g⁻¹) = σ(g)`, `σ(gh) ≤ σ(g) + σ(h)` and is continuous.
- `ϖ^y = Aubert.General.uniformizerPowers i (.ofAdd y)` for a cocharacter `y` of `S`. The map
  `y ↦ ϖ^y` is a group homomorphism from `X_*(S)`.
- `⟨α, y⟩ = latticePairing S α y ∈ ℤ`. For a simple root `β`
  (`Aubert.General.RationalPointFamily.SimpleRoot i ν`, a member of `simpleRelativeRoots i ν`),
  `Aubert.General.simpleRootPairing i ν β y = ⟨β, y⟩`.
- `G¹ = Plancherel.rationalCommonNormKernel G`, the common kernel of the normalized absolute values
  `|χ|_F` of the rational characters `χ` of `G`. A point lies in `G¹` exactly when every integer
  valuation `(rationalCharacterValuation G g).toAdd χ` is `0`.
- `rationalCartanCell i K0 F0 y` (module `RationalXiSquareIntegrableOfUpperBound`) is the set of
  `k₁ ϖ^y f k₂` with `k₁, k₂ ∈ K0` and `f ∈ F0`.

## Declarations

### `le_sum_abs_mul_of_subadditive φ h1 hinv hmul s a b` (section `AbstractHeight`)

Let `X` be a group, `σ : X → ℝ` with `σ(1) = 0`, `σ(x⁻¹) = σ(x)` and `σ(xy) ≤ σ(x) + σ(y)`, and
`φ : Multiplicative Y →* X` a homomorphism from (the multiplicative copy of) an abelian group `Y`.
For every finite family `(a_k, b_k)_{k ∈ s}` with `a_k ∈ ℤ` and `b_k ∈ Y`:

`σ(φ(∑_{k ∈ s} a_k • b_k)) ≤ ∑_{k ∈ s} |a_k| σ(φ(b_k))`.

Proof: `σ(x^m) ≤ m σ(x)` for `m ∈ ℕ` by induction, then `σ(x^m) ≤ |m| σ(x)` for `m ∈ ℤ` using
`σ(x⁻¹) = σ(x)`. The sum is handled by induction on `s`, using that `φ` turns sums into products
and integer multiples into integer powers.

### `rationalPairingAt P y` and `rationalPairingAt_toRat` (section `BoundedFunctionals`)

For abelian groups `M`, `Y`, a ℤ-bilinear pairing `P : M →ₗ[ℤ] Y →ₗ[ℤ] ℤ` and `y ∈ Y`,
`rationalPairingAt P y : ℚ ⊗[ℤ] M →ₗ[ℤ] ℚ` is the extension `q ⊗ m ↦ q · P m y` of `m ↦ P m y`
(built with `TensorProduct.lift`). `rationalPairingAt_toRat` states
`rationalPairingAt P y (toRat m) = P m y`, where `toRat m = 1 ⊗ m`
(`Langlands.LinearAlgebra.RationalSpan`).

### `exists_abs_pairing_le_of_span_eq_top P hR W hb m`

Let `R ⊆ M` be a set whose image `toRat '' R` spans `ℚ ⊗[ℤ] M` over `ℚ` (`hR`), and let
`W ⊆ Y × ℝ` be any set of pairs `(y, t)`. If every `m ∈ R` has a constant `C` with
`|P m y| ≤ C t` for all `(y, t) ∈ W` (`hb`), then every `m ∈ M` has such a constant.

Proof: the elements `x` of the ℚ-span of `toRat '' R` with a constant `C` such that
`|rationalPairingAt P y x| ≤ C t` on `W` include `toRat '' R` and are closed under `0`, sums
(constants add) and rational multiples `q x` (constant `|q| C`; `rationalPairingAt P y` is additive
and commutes with rational scalars by `map_rat_smul`). Span induction then covers `toRat m`.

This lemma is not used in the rest of the module (`exists_abs_latticePairing_le_of_simpleRoots` proves a variant directly
for the cocharacter pairing), and the proof of Corollary III.1.2 in
`RationalSquareIntegrableDecayProof` does not use it either. It is kept as a general lemma.

### `exists_rationalHeight_uniformizerPowers_le_sum hS i ρ`

If `S` is a split torus (`IsSplitTorus S.toGrp`), there are a finite type `I`, characters
`α_k` of `S` and constants `M_k ≥ 0` (`k ∈ I`) such that for every cocharacter `y`

`σ(ϖ^y) ≤ ∑_k M_k |⟨α_k, y⟩|`.

Proof: `IsSplitTorus.exists_cocharacterCoordinates` gives a ℤ-linear isomorphism
`e : X_*(S) ≅ ℤ^I`, and `b = Module.Basis.ofEquivFun e` is a basis with `y = ∑_k (e y)_k • b_k`.
The pairing `X^*(S) × X_*(S) → ℤ` is perfect (`CocharacterUniformizer.latticePairing_isPerfPair`),
so each coordinate `(e y)_k` is `⟨α_k, y⟩` for a character `α_k`. The function `y ↦ σ(ϖ^y)`
is `σ ∘ φ` for the homomorphism `φ = Aubert.General.uniformizerPowers i`, and `σ = rationalHeight ρ`
satisfies the three hypotheses of `le_sum_abs_mul_of_subadditive` (`rationalHeight_one`,
`rationalHeight_inv`, `rationalHeight_mul_le`). So
`σ(ϖ^y) ≤ ∑_k |⟨α_k, y⟩| σ(ϖ^{b_k})`, and `M_k = σ(ϖ^{b_k}) ≥ 0`.

### `exists_abs_latticePairing_le_of_simpleRoots hG hi hν hroot hres α`

Let `G` be connected reductive (`hG`), `i` a maximal split torus (`hi`) and `ν` generic (`hν`).
Let `P` be any relation between cocharacters `y` and reals `t`. Assume

- (`hroot`) for each simple root `β` there is `C` with `|⟨β, y⟩| ≤ C t` whenever `P y t`, and
- (`hres`) for each rational character `χ` of `G` there is `C` with `|⟨χ|_S, y⟩| ≤ C t` whenever
  `P y t`, where `χ|_S = torusCharacterRestrict i χ`.

Then every character `α` of `S` has a `C` with `|⟨α, y⟩| ≤ C t` whenever `P y t`.

Proof: the elements `w` of the rational character space `ℚ ⊗ X^*(S)` that admit a constant `C`
with `|ev_y(w)| ≤ C t` whenever `P y t` form a ℚ-submodule `W`. Here
`ev_y = rationalCocharacterEvaluation y`, with `ev_y(toRat α) = ⟨α, y⟩`. The constants add under
sums, and multiply by `|q|` under scalars `q ∈ ℚ`. By `hroot`, `W` contains the ℚ-span of the
simple roots. That span is the span of all relative roots
(`ratSpan_simpleRelativeRoots_eq_relativeRootSpan`, using the negation stability of the relative
roots from `relativeRootSystem`). By `hres`, `W` contains the restricted rational characters. The
relative roots and the restricted rational characters span `ℚ ⊗ X^*(S)`
(`relativeRootsRestrictedCharactersSpan`). So `W` is everything. In particular `toRat α ∈ W`.

### `exists_rationalHeight_le_of_mem_rationalCartanCell hG hi hν hK0c F0 ρ` (main result)

Let `G` be connected reductive, `i` a maximal split torus, `ν` generic, `K0` a compact subgroup of
`G(F)`, `F0` a finite set of points of the centralizer of `S` and `ρ` a matrix representation.
Then there is `C` such that for every cocharacter `y` and every real `T`:
if `0 ≤ T` and `|⟨β, y⟩| ≤ T` for all simple roots `β`, then every
`g ∈ rationalCartanCell i K0 F0 y` with `g ∈ G¹` satisfies

`σ(g) ≤ C (1 + T)`.

`ρ` need not be a closed embedding. The hypothesis `0 ≤ T` is needed: if there are no simple roots,
the condition on `T` is empty. Then `C (1 + T)` with very negative `T` would contradict `σ ≥ 0`
whenever `σ` is not identically `0` on `G¹`.

Proof:

1. `K0 ⊆ G¹`, since every compact subgroup lies in `G¹`
   (`Plancherel.compactSubgroup_le_rationalCommonNormKernel`). So for `g = k₁ ϖ^y f k₂ ∈ G¹`,
   also `ϖ^y f = k₁⁻¹ g k₂⁻¹ ∈ G¹`.
2. For a rational character `χ` of `G`, `⟨χ|_S, y⟩` is the valuation of `χ(ϖ^y)`
   (`Plancherel.RenardCartan.rationalCharacterValuation_map_uniformizerSection`). Since
   `ϖ^y f ∈ G¹`, this valuation is minus the valuation of `χ(f)`
   (`Plancherel.mem_rationalCommonNormKernel_iff_valuation`). So `|⟨χ|_S, y⟩|` is at most an
   upper bound `V_χ` of `|val χ(f)|` over the finite set `F0`.
3. Apply `exists_abs_latticePairing_le_of_simpleRoots` with `P y t`: `1 ≤ t`, `|⟨β, y⟩| ≤ t` for all simple roots `β`,
   and `ϖ^y f ∈ G¹` for some `f ∈ F0`. The constants are `1` for the simple roots and `V_χ` for
   the restricted characters (using `t ≥ 1`). For the characters `α_k` of
   `exists_rationalHeight_uniformizerPowers_le_sum` (applied to the split torus `S`), this gives
   constants `C_k` with `|⟨α_k, y⟩| ≤ C_k (1 + T)`, since `P y (1 + T)` holds.
4. `σ(g) ≤ σ(k₁) + σ(ϖ^y) + σ(f) + σ(k₂)` by subadditivity. `σ` is continuous, hence bounded by
   some `b` on the compact `K0`, and bounded by some `b'` on the finite `F0`. So
   `σ(g) ≤ 2b + b' + ∑_k M_k |C_k| (1 + T)`, and
   `C = |2b + b'| + ∑_k M_k |C_k|` works because `1 + T ≥ 1`.
