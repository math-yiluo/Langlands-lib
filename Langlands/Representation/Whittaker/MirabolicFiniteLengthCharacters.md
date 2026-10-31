# Locally constant additive characters of a p-adic field

Author: Worker 11.

This helper module of the mirabolic finite-length proof
[MirabolicFiniteLengthProof](MirabolicFiniteLengthProof.md) classifies the
locally constant characters of the additive groups `F` and `F^n` of a p-adic
field. It also moves a nonzero row vector to the last coordinate row by an
invertible matrix. All declarations live in the namespace
`Langlands.Whittaker.MirabolicFiniteLength`. The module adds no definitions to
the public interface beyond theorems, and it changes no existing pair.

The source facts are Bernstein–Zelevinsky (1976), §5.3 and Lemma 5.4,
printed pp.44–45. Fix a nontrivial additive character `ψ₀` of `F`. Then
`a ↦ ψ_a`, with `ψ_a(x) = ψ₀(a₁x₁ + ⋯ + a_kx_k)`, is an isomorphism from `F^k`
onto its character group (the source cites Weil, *Basic Number Theory*,
Ch. II §5). Every nonzero character of the radical `M ≅ F^(n-1)` is conjugate
under `G'` to the fixed character `Θ`. The Lean proofs here do not follow
Weil's argument. They give a self-contained elementary argument in terms of the
Library's valuation lattices, described below. Only the surjectivity half of the
classification is proved, because only that half is used.

A character of `F` is a monoid homomorphism
`χ : Multiplicative F.Carrier →* ℂˣ` whose complex values
`x ↦ (χ (ofAdd x) : ℂ)` are locally constant for the supplied topology
`T.topology`. BZ76 §1.19, printed p.11, calls these characters.

## Valuation lattices

The lattices are the Library's
`Langlands.PadicField.TopologicalData.additiveLattice T k`, written `L k`. They
are the additive subgroups `{x | v(x) ≤ exp k}` for the discrete valuation `v`
of `T`, so `L j ⊆ L k` when `j ≤ k`, and `L k = ϖ^(-k) 𝒪`.

- `additiveLattice_mul_mem`: `L j · L k ⊆ L (j + k)`, by multiplicativity of
  the valuation.
- `exists_mem_additiveLattice`: every `x` lies in some `L k` (take
  `k = log v(x)` for `x ≠ 0`).
- `div_mem_additiveLattice`: if `x ∈ L (c + 1)` and `z ∉ L j`, then
  `x / z ∈ L (c - j)`. The proof uses the Library lemma
  `mul_mem_additiveLattice_iff` with the order `T.ord z`.
- The imported `PadicField.TopologicalData.isCompact_additiveLattice` and
  `PadicField.TopologicalData.isOpen_additiveLattice` from
  `HarmonicAnalysis.PadicLatticeTopology` show that `L k` is the image of
  the compact open ring of integers `T.Integers` under multiplication by
  `ϖ^(-k)`, using `mem_additiveLattice_iff_exists_integer`,
  `mem_additiveLattice_iff_div_mem_integers`, `isCompact_integers` and
  `isOpen_integers` of the Library.
- `finite_quotient_additiveLattice m k`: the quotient of `L k` by `L m ∩ L k`
  is finite. `L k` is compact and the subgroup is open, so Mathlib's
  `AddSubgroup.quotient_finite_of_isOpen` applies.

## Conductors

- `exists_trivial_additiveLattice`: a locally constant `χ` is trivial on some
  `L m`, since the fibre over `1` is an open neighbourhood of `0` and the
  Library's `exists_additiveLattice_subset` puts a lattice inside it.
- `exists_exact_conductor`: a nontrivial locally constant `ψ` has an exact
  conductor `t`. That is, `ψ` is trivial on `L t`, and some `x₀ ∈ L (t + 1)`
  has `ψ x₀ ≠ 1`. The set of `k` with `ψ` trivial on `L k` is nonempty and
  bounded above (a point with `ψ ≠ 1` lies in some `L j`), so it has a greatest
  element `t` by `Int.exists_greatest_of_bdd`.
- `mem_additiveLattice_of_forall_mul`: with `t` and `x₀` as above, if
  `y ↦ ψ(a y)` is trivial on `L k`, then `a ∈ L (t - k)`. Otherwise
  `x₀ / a ∈ L k` by `div_mem_additiveLattice`, and `ψ(a · x₀ / a) = ψ x₀ ≠ 1`.

## A finite pairing

`exists_eq_of_pairing` is a statement about abstract additive groups `X`, `Y`
with subgroups `X₀`, `Y₀` of finite index. Let `β : X → AddChar Y ℂ` be
multiplicative in the first variable. Suppose `β` is trivial when either variable
lies in `X₀` or `Y₀`, and nondegenerate on both sides: `β x` trivial forces
`x ∈ X₀`, and `β · y` trivial forces `y ∈ Y₀`. Then every character `χ` of `Y`
trivial on `Y₀` equals `β x` for some `x`.

Proof. The pairing descends to injective homomorphisms
`Φ : X ⧸ X₀ → (Y ⧸ Y₀)^` and `Ψ : Y ⧸ Y₀ → (X ⧸ X₀)^` into complex character
groups. Here `^` denotes `AddChar · ℂ`, and characters descend to quotients
through the private helper `descendChar`. Mathlib's `AddChar.card_eq` says a
finite abelian group has as many complex characters as elements. With `Ψ` this
gives `|(Y ⧸ Y₀)^| = |Y ⧸ Y₀| ≤ |X ⧸ X₀|`. Hence the injective `Φ` is
bijective (`Function.Injective.bijective_of_nat_card_le`). The preimage of the
descended `χ` is the required `x`.

## Classification

- `exists_mul_eq_on_additiveLattice`: let `ψ` have exact conductor `t` with
  witness `x₀`, and let `χ` be trivial on `L m`. Then on each lattice `L k`,
  `χ x = ψ(a x)` for some `a ∈ L (t - m)`. This is `exists_eq_of_pairing` for
  `X = L (t - m)`, `X₀ = L (t - k)`, `Y = L k`, `Y₀ = L m` and
  `β a x = ψ(a x)`. Triviality on `X₀` and `Y₀` follows from
  `additiveLattice_mul_mem` and the conductor. Both nondegeneracies are
  `mem_additiveLattice_of_forall_mul`, and the quotients are finite by
  `finite_quotient_additiveLattice`.
- `exists_mul_eq`: for a nontrivial locally constant `ψ` and any locally
  constant `χ`, some `a ∈ F` satisfies `χ x = ψ(a x)` for all `x`. Let `S i` be
  the set of `a` that work on `L (m + i)`. Each `S i` is closed, because
  `ψ` is continuous. Every finite family of the `S i` meets the compact set
  `L (t - m)`, by the previous lemma applied to the largest index. Hence
  `IsCompact.inter_iInter_nonempty` gives one `a` in all `S i`, and every `x`
  lies in some `L (m + i)`.
- `exists_generating_character`: some locally constant `ψ` generates in this
  sense. If a nontrivial locally constant character exists, take it and apply
  `exists_mul_eq`. Otherwise `ψ = 1` works with `a = 0`, because then every
  locally constant character is trivial. This case split does not use the
  published `Langlands.HarmonicAnalysis.padicUnitaryAdditiveCharacterExists`
  theorem. The downstream proof needs only the generating property.
- `exists_dotProduct_eq`: for a generating `ψ`, every locally constant
  character `χ` of `F^n` has the form `v ↦ ψ(a ⬝ᵥ v)`. Restrict `χ` to each
  coordinate axis through `Pi.single i` (continuous, so the restriction is
  locally constant), obtain `a i`, and write `v` as the sum of its coordinate
  vectors (`Finset.univ_sum_single`).

## Transitivity on nonzero rows

`exists_dotProduct_mulVec_eq_last` holds over any field `K`. For a nonzero
`a : Fin (n + 1) → K` there is `g : GeneralLinear (n + 1) K` with
`a ⬝ᵥ (g v) = v_last` for every `v`. In other words, the row `a` becomes the
last coordinate row after the change of variables `g`. This is the linear
algebra behind BZ76 Lemma 5.4: the characters `v ↦ ψ(a ⬝ᵥ v)` with `a ≠ 0` are
moved to the fixed character `v ↦ ψ(v_last)`.

Proof. Choose `w` with `a ⬝ᵥ w = 1` and `w_last ≠ 0`. If `a_last ≠ 0`, use a
multiple of the last basis vector; otherwise use `a_k⁻¹ e_k + e_last` for some
`a_k ≠ 0`. Put `u = e_last - a` and `M = 1 + w uᵀ`, so
`M v = v + (u ⬝ᵥ v) w`. Then `a ⬝ᵥ (M v) = a ⬝ᵥ v + (v_last - a ⬝ᵥ v) = v_last`.
Suppose `M v = 0`. Then `v_last = a ⬝ᵥ (M v) = 0` and `v = (a ⬝ᵥ v) w`, and
the last coordinate gives `(a ⬝ᵥ v) w_last = 0`. Hence `a ⬝ᵥ v = 0` and
`v = 0`. So `M` is injective and therefore invertible
(`Matrix.mulVec_injective_iff_isUnit`).

## Sources

I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group GL(n,F)
where F is a non-Archimedean local field*, Russian Mathematical Surveys 31:3
(1976), 1–68. Registered source `bernstein-zelevinsky-1976-representations-gln`,
Central-Library PDF SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`; printed
pages equal one-based PDF pages. Read: §1.19 p.11, §§5.1–5.5 pp.44–45.
