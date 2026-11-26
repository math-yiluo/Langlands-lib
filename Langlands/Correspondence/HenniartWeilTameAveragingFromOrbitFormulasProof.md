# The fixed-cutoff tame average from the orbit formulas

`Langlands.Henniart.weilTameAveragingFromOrbitFormulas.{uK,uW}` proves
`WeilTameAveragingFromOrbitFormulasStatement.{uK,uW}` (module
`Langlands.Correspondence.HenniartTameOrbitFormula`). It is an implication.
It assumes `TameWeilFrobeniusParametrizationStatement`,
`WeilTameOrbitFormulaStatement` and `WeilTameFieldFixedPointStatement`, and
derives `WeilTameAveragingStatement` from them. This module does not prove the
three premises.

The mathematics is the averaging over the Frobenius cosets in H. Koch,
*Bemerkungen zur numerischen lokalen Langlands-Vermutung* (1984), §8
(`koch-1984-numerical-langlands-remarks`). There the count over the base
field and the counts over the `m` tame totally ramified fields of degree `m`
are compared. In the Lean proof, that comparison is a twisted form of
Burnside's lemma, proved in general and then applied to the tame wild classes.
All counts are in `ℕ∞`. No finiteness hypothesis is assumed.

## Auxiliary results

**Finite disjoint unions.** `Langlands.enatCardSigma` says that for a finite
index type `ι`, `ENat.card (Σ i, f i) = ∑ i, ENat.card (f i)`. If every `f i`
is finite, this is `Fintype.card_sigma`. Otherwise both sides are `⊤`.

**Twisted Burnside.** Let a group `G` act on `Y`, and let `σ : Y → Y` map
orbits into orbits: for all `g`, `y` there is `g'` with
`σ (g • y) = g' • σ y`. The twisted-stable points
`twistedStablePoints σ hσ = {y | ∃ g, g • σ y = y}` form a sub-`G`-set.
`nonempty_twistedFixed_equiv` constructs a bijection
\[
  \{(g, y) \in G \times Y : g \cdot \sigma(y) = y\} \;\simeq\;
  (\text{$G$-orbits of twisted-stable points}) \times G .
\]
For each twisted-stable `y`, choose `u(y)` with `u(y) • σ y = y`. The map
`(g, y) ↦ (g u(y)⁻¹, y)` is a bijection onto the pairs `(s, y)` with `y`
twisted-stable and `s • y = y`. Its inverse is `(s, y) ↦ (s u(y), y)`.
Mathlib's Burnside bijection `MulAction.sigmaFixedByEquivOrbitsProdGroup`
then identifies those pairs with orbits × `G`. `enatCard_twistedFixed` is the
resulting equality of cardinalities in `ℕ∞`.

**Averaging over cosets.** Let `W` act on `X`, and let `I` and `J` be normal
subgroups of `W`. Let `T ⊆ X` be stable under `W` (`stableSubMulAction`) and
fixed pointwise by `J`. Then `J ∩ I` acts trivially on `T`
(`subgroupOf_le_ker_toPermHom`), so the quotient `I ⧸ (J ∩ I)` acts on `T`
(`cosetMulAction`). Now let `φ ∈ W`, and let `g : ι → I` meet each coset of
`J ∩ I` exactly once, with `ι` finite. `sum_encard_cosetFixed` proves
\[
  \sum_{i} \#\{c \in T : (g_i \varphi)\cdot c = c\}
  = |\iota| \cdot \#\{\text{$I$-orbits $o$ in $X$} : \exists c \in T,\
    [c] = o = [\varphi\cdot c]\}.
\]
The proof applies the twisted Burnside count to `G = I ⧸ (J ∩ I)` acting on
`T`, with `σ = (φ • ·)`. Orbits go into orbits because `φ h φ⁻¹ ∈ I` for
`h ∈ I`. The pairs `(x, c)` are reindexed by the bijection `ι → G`, and for
`c ∈ T` the condition `x • σ c = c` is `(g_i φ) • c = c` when `x` is the coset
of `g_i`. The orbits of `G` on twisted-stable points of `T` map injectively to
the `I`-orbits of `X`. Their image is the stated set of orbits: `c` is
twisted-stable exactly when some `h ∈ I` has `h • (φ • c) = c`, that is, when
`φ • c` lies in the `I`-orbit of `c`.

**Stability of the tame classes.** `wildClassTrivialAt_smul` shows that
triviality on the upper ramification group `W_K^v` passes to conjugates, since
the upper ramification groups of the Weil group are normal (preimages of the
normal groups `Ramification.Padic.absoluteUpperRamificationGroup K v`).
`smul_mem_tameOrbitClasses` shows that, for `J` normal in `W_K`, the set
`tameOrbitClasses K J r m j` is stable under `W_K`. Fixedness by `J` passes to
`w • c` because `w⁻¹ g w ∈ J`. The rank is unchanged by
`openKernelIrreducibleRank_smul`. The slope condition passes by
`wildClassTrivialAt_smul`.

## The main proof

Fix `p`, `K`, `r`, `m`, `j` with `p ∤ m`. Take
`φ = Weil.Local.localGeometricFrobenius K`, which has `localDegreeInt K φ = 1`
by `Weil.Local.localDegreeInt_localGeometricFrobenius`. The parametrization
premise supplies `D : TameWeilFrobeniusData K m φ` with kernel `J`. Put
`g i = (D.cosetEquiv i).out`, a representative in `I_K` of the `i`-th coset.
Then `i ↦ [g i]` is the bijection `D.cosetEquiv`. The enumeration of fields
required by `WeilTameAveragingStatement` is
`D.cosetEquiv.trans D.fieldEquiv`.

1. The index of `J ∩ I_K` in `I_K` is `m`, read off from `D.cosetEquiv`, so
   the orbit formula applies to `J` and `φ`:
   `C_K(p^r m, j) = (q_K - 1) · #(frobeniusStableTameOrbits K J r m j φ)`.
2. The field with index `i` is the field of the coset `[g i]`, so the
   fixed-point formula at `g = g i` gives
   `C_{E_i}(p^r, j) = (q_K - 1) · #{c ∈ T : (g_i φ) • c = c}`, where
   `T = tameOrbitClasses K J r m j`.
3. `T` is stable under `W_K` (`smul_mem_tameOrbitClasses`) and fixed
   pointwise by `J` (its first defining condition). `I_K` and `J` are normal
   in `W_K`. So `sum_encard_cosetFixed` applies with `ι = Fin m`:
   `∑ᵢ #{c ∈ T : (g_i φ) • c = c} = m · #(frobeniusStableTameOrbits K J r m j φ)`.

Summing step 2 over `i`, factoring out `q_K - 1`, and using steps 3 and 1
gives `∑ᵢ C_{E_i}(p^r, j) = m · C_K(p^r m, j)` in `ℕ∞`. This is the identity
that `WeilTameAveragingStatement` requires.
