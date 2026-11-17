# Unit filtration, the group `𝔎(𝔄)` and the valuation `v_𝔄` (Bushnell–Kutzko 1993, §1.1)

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open
subgroups*, Annals of Math. Studies 129 (1993), `bushnell-kutzko-1993-admissible-dual-gln`,
§1.1, printed pp. 21–22 (PDF pp. 33–34; PDF page = printed page + 12).

The module imports `Langlands.BushnellKutzko.LatticeChain` and works in the same generality: a
commutative ring `O`, a field `K` with an algebra map `O → K`, a `K`-vector space `V` that is an
`O`-module through `K`, and a lattice chain `𝓛 : LatticeChain O K V`. As there,
`A = End_K(V) = Module.End K V`, `𝔄 = 𝔄(𝓛) = 𝓛.order` and `𝔓^n = End^n_O(𝓛) =
𝓛.endFiltration n`. The group `G = Aut_K(V)` is the unit group `(Module.End K V)ˣ`. Every
object is indexed by the chain `𝓛`, as the task permits.

## The unit groups `U^n(𝔄)` (BK93 p. 21)

BK93 defines `U^0(𝔄) = U(𝔄) = 𝔄^×` and `U^n(𝔄) = 1 + 𝔓^n` for `n ≥ 1`.

`LatticeChain.unitFiltration 𝓛 n : Subgroup (Module.End K V)ˣ`, for `n : ℕ`, is the set of
units `g ∈ G` with

- `g ∈ 𝔄` and `g⁻¹ ∈ 𝔄`, and
- `g - 1 ∈ 𝔓^n`.

The subgroup axioms are proved directly from `End^m · End^n ⊆ End^{m+n}`.

- For `n = 0` the last condition holds automatically, so `U^0` is the unit group `𝔄^×` of `𝔄`
  inside `G` (`mem_unitFiltration_zero`).
- For `n ≥ 1`, `coe_image_unitFiltration` proves that the image of `U^n` in `A` is exactly
  `{y ∈ A : y - 1 ∈ 𝔓^n} = 1 + 𝔓^n`. So `unitFiltration 𝓛 n` is BK93's `U^n(𝔄)`, viewed in `G`.
  The proof is Nakayama's lemma (see below), so the conditions `g ∈ 𝔄`, `g⁻¹ ∈ 𝔄` are redundant
  when `n ≥ 1`. They are included in the definition so that it is a subgroup for every `n ≥ 0`
  without needing that argument.

Also proved: `mem_unitFiltration` and `unitFiltration_antitone` (`U^m ⊇ U^n` for `m ≤ n`).

### Proved supporting lemmas

- `fg_lattice`: every `L_i` is a finitely generated `O`-module.
- `finiteDimensional`: a `K`-vector space carrying a lattice chain is finite-dimensional. In
  particular, a statement quantifying over lattice chains in `V` needs no separate
  `FiniteDimensional K V` hypothesis.
- `map_one_add_eq`: if `n ≥ 1` and `x ∈ 𝔓^n`, then `(1 + x) L_i = L_i` for every `i`. Proof:
  `L_i ⊆ (1 + x) L_i + L_{i+k}` for every `k ≥ 0` by induction on `k`. With `k = e(𝓛)` this
  becomes `L_i ⊆ (1 + x) L_i + Ring.jacobson O • L_i`. Nakayama's lemma
  (`Submodule.le_of_le_smul_of_le_jacobson_bot`) then gives `L_i ⊆ (1 + x) L_i`. The reverse
  inclusion holds because `1 + x ∈ 𝔄`.
- `exists_mem_unitFiltration`: for `n ≥ 1` and `x ∈ 𝔓^n` there is `g ∈ U^n` with `g = 1 + x`.
  `1 + x` is surjective on `V` because its image contains the spanning lattice `L_0`, so it is
  invertible since `V` is finite-dimensional. Its inverse preserves each `L_i` by
  `map_one_add_eq`.
- `coe_image_unitFiltration`, described above.

## The group `𝔎(𝔄)` (BK93 p. 21)

BK93 defines `𝔎(𝔄) = Aut(𝓛) = {x ∈ G : x L_i ∈ 𝓛, i ∈ ℤ}`.

`LatticeChain.stabilizer 𝓛 : Subgroup (Module.End K V)ˣ` is the set of units `g` such that,
for every `i`, the image `g L_i` (`Submodule.map` of `g` regarded as an `O`-linear map) equals
`L_j` for some `j`. This is BK93's definition, a one-sided condition. Closure under inverses is
proved with the lemma `exists_shift`: if every `g L_i` is a member of the chain, then
`g L_i = L_{i+d}` for a single integer `d` and all `i`. The proof shows that the induced map on
indices is strictly increasing, commutes with `i ↦ i + e(𝓛)`, and is therefore a translation.

BK93's second description of `𝔎(𝔄)` as the `G`-normalizer of `𝔄`, and the statement that the
`U^n(𝔄)` are normal subgroups of `𝔎(𝔄)`, are not proved here. They are part of
`NormalizerStatement`.

## The integer `v_𝔄(g)` for `g ∈ 𝔎(𝔄)` (BK93 pp. 21–22)

`LatticeChain.stabilizerValuation 𝓛 g : ℤ`, for `g : 𝓛.stabilizer`, is the integer `d` with
`g L_i = L_{i+d}` for all `i`, chosen from `exists_shift`. The module proves that it has this
property (`map_lattice_stabilizer`) and that it is unique: if `g L_i = L_{i+d}` for one `i`,
then `d = stabilizerValuation g` (`stabilizerValuation_unique`).

BK93 (p. 22, after (1.1.3)) states that for `x ∈ 𝔎(𝔄)` the valuation `v_𝔄(x)` of (1.1.3) is
the integer `n` with `x𝔄 = 𝔄x = 𝔓^n`. The task describes `v_𝔄(g)` as the integer with
`g L_i = L_{i + v_𝔄(g)}`, and that integer is what this declaration defines. The agreement with
the valuation (1.1.3) and with `g𝔄 = 𝔄g = 𝔓^{v_𝔄(g)}` is part of `NormalizerStatement`.

## The valuation `v_𝔄` on `A` (BK93 (1.1.3), p. 22)

BK93 (1.1.3) defines `v_𝔄(x) = max {n ∈ ℤ : x ∈ 𝔓^n}` for `x ∈ A`, with `v_𝔄(0) = ∞`.

`LatticeChain.valuation 𝓛 : Module.End K V → WithTop ℤ` sends

- `0` to `⊤ = ∞`, and
- `x ≠ 0` to `sSup {n ∈ ℤ : x ∈ 𝔓^n}`, the conditionally complete supremum in `ℤ`.

When the set is nonempty and bounded above, this supremum is its maximum, BK93's value. For a
lattice chain over a nonarchimedean local field, `RadicalFiltrationStatement` asserts that this
holds for every `x ≠ 0`. That fact is not proved here. For a set that is empty or unbounded
above, Mathlib's `sSup` on `ℤ` returns `0`. The statement says this case does not arise for
`x ≠ 0`. Proved: `valuation_zero`.
