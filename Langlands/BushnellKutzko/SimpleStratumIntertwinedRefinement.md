# The refinement step in the proof of BK93 (3.5.9)

This module states and proves `SimpleStratumIntertwinedRefinementStatement`, the
step of the proof of BK93 (3.5.9) that turns an intertwining property of a
character into a new simple stratum.

Source: Bushnell and Kutzko, *The admissible dual of GL(N) via compact open
subgroups* (1993), literature ID `bushnell-kutzko-1993-admissible-dual-gln`,
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`:
the proof of (3.5.9), printed p. 122 (PDF p. 134); Lemma (2.4.11), printed
pp. 72–73 (PDF pp. 84–85); the refinement theorem (2.2.8), printed p. 56 (PDF
p. 68); Proposition (2.2.1) and the Remark before it, printed p. 51 (PDF p. 63);
the definition (1.5.5) of pure and simple strata, printed p. 43 (PDF p. 55);
the exact sequence (1.4.10), printed p. 38 (PDF p. 50); and the duality (1.1.4)–(1.1.6),
printed p. 22 (PDF p. 34).

## The statement

Let `F` be a nonarchimedean local field, `ψ_F` an additive character of `F`
trivial on `𝔭_F` and not on `𝔬_F` (`IsBKAdditiveCharacter`), and
`[𝔄,n,m,β]` a simple stratum (`Stratum.IsSimple`, with `S.r = m`) with `m ≥ 1`.
Let `b ∈ 𝔓^{−m}` and write `ψ_b(y) = ψ_F(tr(b(y − 1)))` (`elementCharacter` of
`traceCharacter`). The hypothesis is that `ψ_b` on `U^m(𝔅_β)`
(`relativeUnitFiltration`) is intertwined by every element of `B_β^×`
(`centralizerUnitGroup`): `ψ_b(tyt⁻¹) = ψ_b(y)` whenever `t` commutes with `β`
and both `y` and `tyt⁻¹` lie in `U^m(𝔅_β)`. The conclusion is a simple stratum
`[𝔄,n,m,β']` on the same lattice chain with `β' ≡ β + b (mod 𝔓^{1−m})`.

On printed p. 122, BK derive from this hypothesis that `s(b) ∈ F[β] + 𝔔^{1−m}` by
(2.4.11), where `s` is a tame corestriction relative to `F[β]/F` and
`𝔔 = 𝔓 ∩ B_β`, and then obtain the new stratum from (2.2.8). The statement
covers every `b ∈ 𝔓^{−m}`, including those whose derived coset
`s(b) + 𝔔^{1−m}` is zero. Such `b` include `b = 0`, but may also have valuation
`v_𝔄(b) = −m`. Theorem (2.2.8) does not apply to them: it needs a simple stratum
`[𝔅,m,m−1,c]` with `c` in the derived coset, whereas every element of the zero
coset lies in `𝔔^{1−m}` and a pure stratum of level `m` requires an element of
valuation exactly `−m` ((1.5.5), printed p. 43). The conjugation argument of
(2.2.1) handles this case, whatever the valuation of `b`. For a nonzero derived
coset, the scalar representative and `b` both have valuation `−m`, and
simplicity of `[𝔄,n,m,β']` at index `m` (and not only of `[𝔄,n,m−1,β']`) comes
from part (ii) of (2.2.8), the formula `k₀(β',𝔄) = max{k₀(β,𝔄), k₀(c,𝔅)}`, with
a scalar `c`.

## The proof

Write `E = F[β]` (the generated algebra `elementAlgebra β`, a field by purity),
`B = End_E(V)`, and let `s` be a tame corestriction relative to `E/F`, which
exists by `tameCorestriction` (BK93 (1.3.2)–(1.3.4)) and maps `𝔓^k` onto
`𝔔^k = 𝔓^k ∩ B`. When `β` is scalar, `E = F` and `B = A`; the argument below
needs no separate treatment of that case.

1. **Linearization** (`trace_mem_of_intertwined`). For `t ∈ B_β^×` and `z ∈ 𝔓^m`
   commuting with `β` with `tzt⁻¹ ∈ 𝔓^m`, apply the hypothesis to `y = 1 + az`
   for every `a ∈ 𝔬_F`. Since `ψ_b(tyt⁻¹)/ψ_b(y) = ψ_F(a·tr((t⁻¹bt − b)z))` and
   `ψ_F` has conductor `𝔭_F`, this gives `tr((t⁻¹bt − b)z) ∈ 𝔭_F`.
2. **Duality** (`exists_decomposition_of_trace_test`,
   `exists_decomposition_of_intertwined`). The trace forms vanishing on
   `[β, A] = {βy − yβ}` are those of elements commuting with `β`
   (`eq_zero_of_forall_trace_mul_eq_zero`, `exists_trace_mul_eq`), and the trace
   dual of `𝔓^k` is `𝔓^{1−k}` (BK93 (1.1.4)–(1.1.6)). Separating the image of the
   finitely generated lattice `𝔓^{1−m} + t⁻¹𝔓^{1−m}t` in `A/[β,A]` by linear forms
   (`separates_fg_submodule`) turns step 1 into
   `t⁻¹bt − b ∈ 𝔓^{1−m} + t⁻¹𝔓^{1−m}t + [β, A]`.
3. **Derived coset** (`corestriction_commutator_mem_of_intertwined`). The map `s`
   is a `B`-bimodule map vanishing on `[β, A]` (`TameCorestriction.adjointMap_eq_zero`).
   Applying it to step 2 for `t = x ∈ B^×` gives
   `x s(b) − s(b) x ∈ x𝔔^{1−m} + 𝔔^{1−m}x`: every element of `B^×` intertwines the
   coset `s(b) + 𝔔^{1−m}` in `B`. This replaces BK's passage through the character
   `ψ_{B,s(b)}` of the Remark before (2.2.1) and the coset-intertwining
   comparison of §1.5.
4. **(2.4.11) over `E`** (`exists_algebraMap_sub_mem_of_coset_intertwined`,
   `exists_scalar_sub_mem_of_coset_intertwined`). The lattices of the chain form an
   `𝔬_E`-lattice chain (`LatticeChain.relativeLatticeChain`, with the valuation of
   `E` from `LocalField.FiniteExtension`), whose filtration of `B` is `𝔔^k`. The
   coset part of (2.4.11) for this chain is proved by the splitting-basis argument
   of `exists_algebraMap_sub_mem_of_coset_intertwined` in
   `SimpleStratumCorestrictionCongruenceProof`: off-diagonal entries are removed
   by scaling one basis vector by a uniformizer, and diagonal entries are compared
   by transpositions. It gives `δ ∈ E` with `s(b) ≡ δ (mod 𝔔^{1−m})`.
5. **Zero derived coset** (`exists_simple_of_corestriction_mem`). If
   `δ ∈ 𝔓^{1−m}`, then `s(b) ∈ 𝔔^{1−m}`. The conjugation lemma
   `exists_conj_sub_mem` (built on the exact sequence (1.4.10), as in the proof of
   (2.2.1)) gives `g ∈ U¹(𝔄)` with `g(β + b)g⁻¹ ≡ β (mod 𝔓^{1−m})`. Then
   `β' = g⁻¹βg` satisfies `β' ≡ β + b (mod 𝔓^{1−m})`, and `[𝔄,n,m,β']` is simple
   because conjugation by an element of `𝔄^×` preserves simple strata on the chain
   (`isSimple_conjStratum`).
6. **Nonzero derived coset** (`exists_simple_of_corestriction_sub_scalar_mem`).
   If `δ ∉ 𝔓^{1−m}`, then `v_𝔄(δ) = −m`, and also `v_𝔄(b) = −m`, since
   `b ∈ 𝔓^{1−m}` would put `s(b)`, hence `δ`, into `𝔓^{1−m}`. The derived stratum
   `[𝔅,m,m−1,s(b)]` (on the chain `LatticeChain.subfieldChain` with the same
   lattices) is equivalent to the scalar stratum `[𝔅,m,m−1,δ]`, which is simple
   with `k₀(δ,𝔅) = −∞` (`exists_scalar_simple`). The refinement theorem
   `refinement` (`RefinementStatement`, BK93 (2.2.8)) gives a simple stratum
   `[𝔄,n,m−1,β']` with `β' ≡ β + b (mod 𝔓^{1−m})` and
   `k₀(β',𝔄) = max{k₀(β,𝔄), −∞} = k₀(β,𝔄) < −m`. The last inequality is the
   simplicity of `[𝔄,n,m,β]`, so `[𝔄,n,m,β']` is simple as well.

`LatticeChain.eq_of_lattice_coe_eq` identifies the two `𝔬_E`-chains with the same
lattices that occur in step 6. The theorem `simpleStratumIntertwinedRefinement`
combines steps 3–6.
