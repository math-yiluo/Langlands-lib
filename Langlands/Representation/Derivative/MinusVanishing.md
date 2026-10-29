# A smooth mirabolic representation with vanishing `Ψ⁻` and `Φ⁻` is zero

Authors: Worker 1025.

This module proves the helper theorem

```
Langlands.Derivative.Mirabolic.subsingleton_of_psiMinus_phiMinus T ψ m :
  ∀ X : SmoothRep ℂ (mirabolic (m + 1) F.Carrier),
    Subsingleton ((psiMinus T (m + 1)).obj X) →
    Subsingleton ((phiMinus T ψ m).obj X) → Subsingleton X
```

for a p-adic field `F` with topological data `T`, a unitary additive character `ψ`
and independent universes `uF` (field) and `uV` (representation spaces). In words:
if `X` is a smooth representation of the mirabolic group `P_(m+2)` whose
trivial-character localization `Ψ⁻ X` and whose `θ_ψ`-localization `Φ⁻ X` along the
abelian radical `V_(m+2) ≅ F^(m+1)` both vanish, then `X = 0`. The determinant
twists in `psiMinus` and `phiMinus` do not change their carriers, which are the plain
coinvariant quotients `X ⧸ relations ρ V 1` and `X ⧸ relations ρ V θ_ψ`.

## Provenance

This is the vanishing consequence of the exact sequence
`0 → Φ⁺Φ⁻ → Id → Ψ⁺Ψ⁻ → 0` of Bernstein–Zelevinsky, *Induced representations of
reductive p-adic groups I* (BZ77), Proposition 3.2(e), printed p. 451. BZ77 refers to
Bernstein–Zelevinsky 1976, §5, for its proof. BZ77 §3.5, printed p. 452, uses the same
sequence to glue a representation of `P_n` from its derivatives. The theorem here is an
internal helper for the proof of BZ77 §4.4 (task
`2e5183b1-01e9-44fb-b26c-f4521a25c7c7`), where it gives a nonzero top derivative.
The Lean statement is weaker than the exact sequence: it states only the vanishing
consequence. The proof does not go through the sequence. It uses the direct
averaging argument below.

## Implemented proof

Write `ρ` for the action of `P_(m+2)` on `X`, `N = V_(m+2)` for the radical with
coordinates `radicalCoordinates : N ≃ F^(m+1)`, and `n(ψ)` for the additive
conductor `T.additiveConductor ψ`.

### Coordinate characters and radical boxes

- `coordinateCharacter T ψ m a` is the character `u ↦ ψ(a ⬝ c(u))` of `N`, where
  `c(u)` are the radical coordinates. `coordinateCharacter_zero` shows that `a = 0`
  gives the trivial character.
- `radicalBox T m M` is the compact open subgroup of `N` with coordinates in the
  lattice box `(π^(-M) O)^(m+1)` (`latticeBox T (m+1) M`). Its lemmas are
  `mem_radicalBox`, `radicalBox_mono` and `isCompact_radicalBox`, the last as the
  continuous image of a compact box.
- `exists_mem_latticeBox`: every vector lies in some lattice box, using the discrete
  valuation of each coordinate. So the boxes `radicalBox T m k` for `k : ℕ` exhaust
  `N`.
- `coordinateCharacter_eq_one` and `coordinateCharacter_eq_of_sub_mem`: if
  `a ∈ latticeBox T (m+1) (n(ψ) - M)`, then the character of `a` is trivial on
  `radicalBox T m M`. Two parameters that differ by such an element give characters
  that agree on that box. Both come from the Library duality lemma
  `character_dotProduct_eq_one`.
- `isOpen_ker_coordinateCharacter`: each coordinate character has open kernel,
  because the kernel contains a radical box.

### Step 1: Levi transport of the `θ_ψ`-relations

- `exists_lastRow_eq_of_ne_zero`: every nonzero row `x ∈ K^(m+1)` over a field is the
  last row of an invertible matrix. The proof replaces row `j` of the identity
  (where `x j ≠ 0`) by `x` and then swaps rows `j` and `last`. The determinant is
  `± x j` (`Matrix.det_updateRow_sum`, `Matrix.det_permute`).
- `levi_inv_mem_relations`: for `g ∈ GL_(m+1)`, the operator `ρ(levi g⁻¹)` maps
  `relations ρ N θ_ψ` into the relations of the coordinate character of the last row
  of `g`. On a generator `ρ(u(c)) w - θ_ψ(u(c)) w`, the Library identity
  `levi_mul_radicalElement` gives
  `levi g⁻¹ · u(c) = u(g⁻¹ c) · levi g⁻¹`. The Library lemma `theta_radicalElement`
  gives `θ_ψ(u(c)) = ψ(c_last)`, and `c_last = g_last ⬝ g⁻¹ c`. So the image is a
  generator of the relations for the last row of `g`.

In the main theorem, `Φ⁻ X = 0` means `relations ρ N θ_ψ = ⊤`. Given a nonzero `a`,
choose `g` with last row `a` and apply `levi_inv_mem_relations` to `ρ(levi g) v`.
This puts every vector `v` in the relations of the coordinate character of `a`.
`Ψ⁻ X = 0` covers `a = 0` (`Submodule.Quotient.subsingleton_iff`).

### Step 2: eventual vanishing of the averages

Fix `x ∈ X`. By smoothness some open subgroup fixes `x`, so by the Library lemma
`exists_latticeBox_subset` there is `l` such that `ρ(u) x = x` whenever
`c(u) ∈ latticeBox T (m+1) l`. For every `a`, the vector `x` lies in the relations of
the coordinate character of `a`. The Library lemma
`Jacquet.Localization.eventually_characterAverage_eq_zero`, applied to the exhaustion
`k ↦ radicalBox T m k`, then gives a level `M_a` at which the twisted average
`characterAverage` of `x` over `radicalBox T m M_a` vanishes.

### Step 3: one level for a compact set of characters

- `characterAverage_eq_zero_of_le`: a twisted average that vanishes over a compact
  open subgroup `H` also vanishes over every larger compact open subgroup `H'`. The
  proof shows `v - P_H v ∈ ker P_H'` by the orbit-mean lemma `sub_orbitMean_mem`.
- `characterAverage_congr`: the average over `H` depends only on the character
  restricted to `H`.
- `exists_forall_characterAverage_eq_zero`: suppose every coordinate character
  kills `x` at some level `M_a`. Then for each lattice box `A` of parameters a single
  level `M` works for all `a ∈ latticeBox T (m+1) A`. The sets
  `a + latticeBox (n(ψ) - M_a)` are open and cover the compact box. Take a finite
  subcover and the maximum `M` of its levels. Each point is close to a center `a`,
  so its character agrees with that of `a` on `radicalBox T m M_a`
  (`coordinateCharacter_eq_of_sub_mem`, `characterAverage_congr`). Finally
  `characterAverage_eq_zero_of_le` lifts the vanishing to level `M`.

This is applied with `A = n(ψ) - l`.

### Step 4: finite Fourier inversion

`eq_zero_of_forall_characterAverage_eq_zero` makes the following assumptions:
- `x` is fixed by the radical box of level `l`;
- for every `a` in the dual box `B = latticeBox (n(ψ) - l)`, the average of `x` over
  `H = radicalBox T m M` against the character of `a` vanishes.

Under these assumptions it concludes `x = 0`. Put `K = H ∩ radicalBox T m l`, a
finite-index subgroup of `H`, and `L = B ∩ latticeBox (n(ψ) - M)`, a finite-index
subgroup of `B` (Library `finite_latticeBox_quotient`).

1. Each character of `B` is trivial on `radicalBox T m l`. So
   `characterAverage_eq_quotient_sum` writes each average as
   `|H/K|⁻¹ Σ_{c ∈ H/K} ψ(-a ⬝ c) ρ(c) x`, with fixed coset representatives.
2. Sum these vanishing averages over representatives `b` of `B/L` and exchange the
   sums. For the trivial coset, every character value is `1` (because
   `ρ(c) x = x` and `character_dotProduct_eq_one`), so the inner sum is `|B/L| • x`.
   For a nontrivial coset `c ∉ K`, the Library lemma
   `mem_latticeBox_of_forall_character_eq_one` gives `b₀ ∈ B` with
   `ψ(b₀ ⬝ c) ≠ 1`. The character `b ↦ ψ(-b ⬝ c)` of `B` is trivial on `L` (since
   `c ∈ H`), so its sum over coset representatives vanishes by the Library lemma
   `sum_out_eq_zero`.
3. Hence `|H/K|⁻¹ |B/L| • x = 0`, and so `x = 0`.

Since every `x` is zero, `X` is a subsingleton.

## Dependencies

The module imports only the Library modules
`Langlands.Representation.Derivative.MirabolicMinus`,
`Langlands.Representation.Derivative.MirabolicLatticeBox`,
`Langlands.Representation.Jacquet.CharacterAveraging` and
`Langlands.Group.GL.Padic`. It uses no Whittaker-model, coinvariant-finiteness,
finite-length or segment results.
