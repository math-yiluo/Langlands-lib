# Witt-vector inputs for Greenberg rings

This file collects the Witt-vector facts used to build Greenberg coefficient rings
(`GreenbergRing.lean`, `GreenbergDVR.lean`) for the mixed-characteristic case of
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*, Theorem A.4.19 (Greenberg functor,
§A.4). Everything here is an internal auxiliary result. Throughout, `p` is a prime and
`𝕎 = WittVector p`.

## Truncated Witt vectors as a functor

- `truncate_map_eq_zero`: if `truncate m x = 0` then `truncate m (map f x) = 0`.
- `truncMap p m f : TruncatedWittVector p m R →+* TruncatedWittVector p m S`, the ring map
  induced by `f : R →+* S`. It is defined by descending `truncate m ∘ map f` along the
  surjection `truncate m`.
- `truncMap_truncate`, `truncMap_comp`, `truncMap_id`: its defining equation and functor
  laws.

## The vanishing lemma

`truncate_mul_map_eq_zero`: let `k` be a perfect field of characteristic `p` and `T` a
`k`-algebra. Let `c ∈ W(k)` with `truncate j (p ^ a * c) = 0`, and let `w ∈ W(T)` have its
first `a` coefficients equal to zero. Then `truncate j (w * map (algebraMap k T) c) = 0`.

Proof: `T` is trivial or of characteristic `p`. Write `w = V^a w'`. If `j ≤ a`, the first
`j` coefficients of `V^a (w' · map c)` vanish. Otherwise `p ^ a c ∈ (p ^ j)`, so
`c = p ^ (j - a) d` because `W(k)` is a domain. Then `V^a w' · p ^ (j - a) = V^j (F^{j - a}
w')`. For this we use `iterate_verschiebung_iterate_frobenius` and
`iterate_verschiebung_mul`.

This lemma is what makes the Greenberg coordinate functionals well defined on generators
`e i` of exponent `p ^ (m i)`.

## The ring map `W(k) → A`

Let `A` be a commutative ring and `r : A →+* k` a surjection onto a perfect field of
characteristic `p` with `(ker r) ^ (N + 1) = ⊥`.

- `ghostComponent_eq_sum`: the explicit sum `w_N(x) = Σ_{i ≤ N} p^i x_i^{p^{N-i}}`.
- `ghostComponent_mem_pow`: if `p ∈ I` and all coefficients of `x` lie in `I`, then
  `w_N(x) ∈ I ^ (N + 1)`.
- `residue_ghostComponent`: `r (w_N x) = r(x_0) ^ p ^ N`.
- `ghostComponent_eq_zero_of_map_eq_zero`: if `map r x = 0` then `w_N x = 0`. This is the
  previous lemma with `I = ker r`.
- `wittToLocal₀`: so `w_N` descends along the surjection `map r : W(A) → W(k)` to a ring
  map `W(k) →+* A`.
- `wittToLocal p r hr N hN := wittToLocal₀ ∘ map (Frob^{-N})`. This is the Frobenius
  untwist.
- `residue_wittToLocal`: `r (wittToLocal w) = w.coeff 0`.

This is the classical structure map from the Witt vectors of a perfect residue field.
Compare Serre, *Local Fields* (source `serre-1979-local-fields`), II §§5–6, where it is
built for complete rings from multiplicative representatives. The Lean route uses ghost
components instead. It is stated only for rings with nilpotent residue kernel, which is all
that `R ⧸ 𝔪ⁿ` needs.

## Cyclic Witt coordinates

`WittDecomposition p ψ`, for a ring map `ψ : W(k) →+* A`, consists of:

- a finite index type `ι`, exponents `m : ι → ℕ` and generators `e : ι → A`;
- additive coordinate maps `coord i : A →+ TruncatedWittVector p (m i) k`. They are
  `ψ`-semilinear (`coord_mul`) and dual to the generators (`coord_e_self`,
  `coord_e_ne`);
- `eq_sum`: every `a` equals `Σ ψ (c i) * e i` for any lifts `c i` of its coordinates.

This is the Lean form of a decomposition `A ≅ ⊕_i W(k) ⧸ p ^ (m i)` as `W(k)`-modules.
Here the truncation `truncate (m i)` identifies `W(k) ⧸ p^{m i}` with `W_{m i}(k)`. The
structure is an internal device of this proof: it fixes the coordinates in which the
Greenberg ring is presented.

- `span_irreducible_pow_eq`: an irreducible `q` of `W(k)` generates the same power ideals
  as `p`.
- `mem_ker_truncate_iff_mem_span`: `truncate n x = 0 ↔ x ∈ (p ^ n)`.
- `nonempty_wittDecomposition p ψ g hs M hM`: suppose `A` is spanned over `W(k)` (through
  `ψ`) by a finite family `g`, and `p ^ M = 0` in `A`. Then `A` has a `WittDecomposition`.

  Proof: `A` is a finitely generated torsion `W(k)`-module over the PID `W(k)`. Mathlib's
  `Module.equiv_directSum_of_isTorsion` gives `A ≅ ⊕ W(k) ⧸ (q_i ^ m_i)` with `q_i`
  irreducible, hence associated to `p`. The coordinates are the components followed by
  `W(k) ⧸ (p ^ m_i) → W_{m_i}(k)`.
