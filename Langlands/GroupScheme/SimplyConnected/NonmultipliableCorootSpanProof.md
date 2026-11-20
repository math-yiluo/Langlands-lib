# Proof: nonmultipliable relative coroots of a simply connected group span the cocharacters

Author: Worker 151 (Task 7828).

This module proves the Library proposition
`Langlands.GroupScheme.NonmultipliableCorootSpanStatement`
([`SimplyConnected.NonmultipliableCorootSpanStatement`](NonmultipliableCorootSpanStatement.md))
at its original universe `u`:

```
theorem Langlands.GroupScheme.nonmultipliableCorootSpan :
    NonmultipliableCorootSpanStatement.{u}
```

So let `k : Type u` be a field, `G` a simply connected group scheme over `Spec k`,
`i : S.toGrp ⟶ G` a maximal split torus, and
`P : RootDatum J (characterLattice S) (cocharacterLattice S)` a root datum whose pairing is
`latticePairing S` (hypothesis 1) and whose roots are exactly the nonmultipliable relative roots
`{a | a ∈ roots i ∧ 2 • a ∉ roots i}` (hypothesis 2). The theorem proves `P.corootSpan ℤ = ⊤`.

**Hypothesis 3 (each reflection of `P` is realized by a rational point normalizing `i`) is not
used.** The proof uses only that `P` is a root pairing over `ℤ` on the lattices of `S`
(Mathlib's `RootDatum J M N` is `RootPairing J ℤ M N`) together with hypotheses 1 and 2.

The proof is case-free: it uses no classification, no highest roots and no choice of base. It
does not follow the route of Borel–Tits (1972), 4.3–4.4 (which compares weight lattices
through an adapted base). It has three parts: two lattice facts for every finite root pairing
over `ℤ` (part 1), an elementary finiteness lemma (part 2), and the reduction to the split
simply connected case over a field splitting a maximal torus (part 3).

The module adds helper theorems and the main theorem, and no definitions and no axioms. The
axioms used are `propext`, `Classical.choice` and `Quot.sound`. The file sets
`backward.isDefEq.respectTransparency false` and does not change any heartbeat limit.

## Part 1: lattice facts for finite root pairings over `ℤ`

Namespace `Langlands.LinearAlgebra.MinusculeLattice`. Throughout, `ι` is a type with
`[Fintype ι]`, `M` and `N` are additive commutative groups, and `Q : RootPairing ι ℤ M N`.
`Q.RootForm` is Mathlib's canonical bilinear form on `M` (module
`Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear`),
`(x, y) = ∑ j ⟨x, α_j∨⟩ ⟨y, α_j∨⟩`, where `⟨x, α_j∨⟩ = Q.coroot' j x`. It is nonnegative on the
diagonal (`zero_le_rootForm`) and positive on nonzero vectors of the root span
(`rootForm_pos_of_ne_zero`).

- `rootForm_comm (x y : M) : Q.RootForm x y = Q.RootForm y x` (by the defining sum).
- `two_mul_rootForm_root (i : ι) (x : M) :
  2 * Q.RootForm (Q.root i) x = Q.coroot' i x * Q.RootForm (Q.root i) (Q.root i)`.
  Proof: apply `x` to Mathlib's `rootForm_self_smul_coroot`
  (`(α_i, α_i) • α_i∨ = 2 • (polarization of α_i)`).
- `four_le_rootForm_root (i : ι) : 4 ≤ Q.RootForm (Q.root i) (Q.root i)`: by
  `rootForm_root_self` the left side is `∑ j (pairing i j)^2`, and the term `j = i` is
  `2^2 = 4`.
- `rootForm_sub_root (i : ι) (x : M)` and `rootForm_add_root (i : ι) (x : M)`:
  `(x ∓ α_i, x ∓ α_i) = (x, x) ∓ (⟨x, α_i∨⟩ ∓ 1) (α_i, α_i)`, from bilinearity, symmetry and
  `two_mul_rootForm_root`.
- `rootForm_sum_smul_root (n : ι → ℤ) (y : M) :
  Q.RootForm (∑ j, n j • Q.root j) y = ∑ j, n j * Q.RootForm (Q.root j) y`.

**(A) Minimal representatives.** `exists_sub_mem_rootSpan_forall_abs_le_one (x : M) :
∃ y : M, x - y ∈ Q.rootSpan ℤ ∧ ∀ i, |Q.coroot' i y| ≤ 1`.
Proof by strong induction on the natural number `(x, x)`. If every `|⟨x, α_i∨⟩| ≤ 1`, take
`y = x`. Otherwise pick `i` with `⟨x, α_i∨⟩ ≥ 2` (respectively `≤ -2`) and replace `x` by
`x - α_i` (respectively `x + α_i`). By `rootForm_sub_root`/`rootForm_add_root` and
`four_le_rootForm_root` the norm drops by at least `4`, it stays nonnegative, and `x - y`
changes by `±α_i ∈ Q.rootSpan ℤ`.

**(B) No nonzero minimal vector in the root lattice.**
`eq_zero_of_mem_rootSpan_of_forall_abs_le_one {x : M} (hx : x ∈ Q.rootSpan ℤ)
(h : ∀ i, |Q.coroot' i x| ≤ 1) : x = 0`.
Proof: write `x = ∑ j n_j α_j` (`Submodule.mem_span_range_iff_exists_fun`) and induct on
`∑ j |n_j|`, for all coefficient vectors at once. Suppose `x ≠ 0`. Then
`0 < (x, x) = ∑ j n_j (α_j, x)`, so some `i` has `n_i (α_i, x) > 0`. Put `c = ⟨x, α_i∨⟩`. Since
`2 (α_i, x) = c (α_i, α_i)` and `(α_i, α_i) ≥ 4`, this gives `n_i c > 0`, so `c ≠ 0`, hence
`c = ±1` with the sign of `n_i`. The reflection `s_i x = x - c α_i` has coefficients
`n' = n - c · δ_i`, with `|n'_i| + 1 = |n_i|`, so `∑ |n'_j| + 1 = ∑ |n_j|`. The reflection
permutes the coroots (`coroot'_reflection`), so `s_i x` still satisfies the bound. By
induction `s_i x = 0`, so `x = 0`, a contradiction.

Coroot forms, applying (A) and (B) to `Q.flip` (whose root span is `Q.corootSpan` and whose
`coroot'` is `Q.root'`):

- `exists_sub_mem_corootSpan_forall_abs_le_one (x : N) :
  ∃ y : N, x - y ∈ Q.corootSpan ℤ ∧ ∀ i, |Q.root' i y| ≤ 1`;
- `eq_zero_of_mem_corootSpan_of_forall_abs_le_one {x : N} (hx : x ∈ Q.corootSpan ℤ)
  (h : ∀ i, |Q.root' i x| ≤ 1) : x = 0`.

## Part 2: the doubling lemma

`Langlands.GroupScheme.NonmultipliableCorootSpan.abs_le_one_of_doubling`:
for an additive commutative group `X`, `g : X →ₗ[ℤ] ℤ`, a finite set `s : Set X` (`hs`) such
that `|g a| ≤ 1` for every `a ∈ s` with `2 • a ∉ s` (`h`), and `c ∈ s`, we have `|g c| ≤ 1`.

Proof: if `|g c| > 1`, induction on `n` shows `2^n • c ∈ s` for all `n` (if `2^(n+1) • c ∉ s`,
then `h` gives `|2^n g c| ≤ 1`, which is false). The map `n ↦ 2^n • c` is injective
because `g c ≠ 0`, contradicting finiteness of `s`.

## Part 3: the main theorem

Fix the data above and hypotheses 1 and 2.

1. **Finiteness.** `G` is connected reductive (`hG.isSemisimple.isConnectedReductive`), so
   smooth and with affine structure map. `S` is a split torus (`hi.1.1`), so `roots i` is finite
   (`IsSplitTorus.finite_relativeRoots`). By hypothesis 2 the injective map `P.root` has range
   inside `roots i`, so `J` is finite; the proof fixes a `Fintype J` instance.
2. **A split maximal torus over an extension.** `exists_maximalTorus_extension_of_finiteType`
   gives a maximal torus `j : M.toGrp ⟶ G` and `f : S.toGrp ⟶ M.toGrp` with `f ≫ j = i`. The
   first clause of `IsMaximalTorus j`, namely `IsTorus M.toGrp`, provides a field `K` over `k`
   such that the base change `M_K` is split. Let `b = algebraBaseMap k K`. Then `G_K` is connected reductive
   (`connectedReductiveFieldExtensionStatement`), `j_K` is a maximal torus
   (`maximalTorusBaseChange`), and `rootDatumExistence` gives a finite `J'` and a reduced root
   datum `Q` of `j_K` (`IsRootDatumOf j_K Q`). `G_K` is simply connected
   (`isSimplyConnectedFieldExtension`), so `splitSimplyConnectedCorootSpan` gives
   `Q.corootSpan ℤ = ⊤`.
3. **Restricting absolute roots.** Let `f_K : S_K ⟶ M_K` be the base change of `f` and, for
   `a : J'`, let `r a : characterLattice S` be the descent along
   `characterLattice.baseChangeEquiv b S hS` of `f_K ≫ Q.root a`.
   - Pairing (`hpairQ`): for every `μ : cocharacterLattice S`,
     `Q.root' a (cocharacterMapInt f_K (μ_K)) = P.toLinearMap (r a) μ`, where
     `μ_K = cocharacterLattice.baseChange b S μ`. This is
     `TitsIndexExistence.latticePairing_restriction` combined with hypothesis 1 and the
     pairing clause of `IsRootDatumOf j_K Q`.
   - Restriction (`hr`): `r a = 0` or `r a ∈ roots i`. Since `Q.root a ∈ roots j_K` (range
     clause of `IsRootDatumOf`), this is `mem_roots_iff_exists_splittingField_restriction`
     applied to `f` and `j`, using `f ≫ j = i`.
4. **Injectivity.** `i_K` is a closed subgroup (`IsClosedSubgroup.baseChange`), so its
   underlying scheme morphism is a monomorphism. It equals `f_K ≫ j_K`, so `f_K` is a
   monomorphism and `RealTorusSpace.cocharacterMapInt f_K` is injective
   (`cocharacterMapInt_injective`). The base-change map
   `cocharacterLattice.baseChange b S` is injective for the split torus `S`
   (`IsSplitTorus.cocharacterLattice_baseChange_bijective`).
5. **Bound on all relative roots** (`hbound`). If `μ : cocharacterLattice S` satisfies
   `|P.root' c μ| ≤ 1` for all `c : J`, then `|⟨a, μ⟩| ≤ 1` for every `a ∈ roots i`. Apply
   part 2 with `s = roots i` and `g = ⟨·, μ⟩`: a relative root `a` with `2 • a ∉ roots i` is
   nonmultipliable, so by hypothesis 2 it is `P.root c` for some `c`, and
   `⟨P.root c, μ⟩ = P.root' c μ`.
6. **Conclusion.** Let `x : cocharacterLattice S`. By (A) for `P` there is `μ` with
   `x - μ ∈ P.corootSpan ℤ` and `|P.root' c μ| ≤ 1` for all `c`. Put
   `ν = cocharacterMapInt f_K (μ_K)`. It lies in `Q.corootSpan ℤ = ⊤`, and for every `a : J'`,
   `Q.root' a ν = ⟨r a, μ⟩` (step 3), which is `0` if `r a = 0` and has absolute value at
   most `1` by step 5 if `r a ∈ roots i`. By (B) for `Q`, `ν = 0`. By step 4, `μ = 0`. Hence
   `x ∈ P.corootSpan ℤ`.

## Relation to the literature

The statement is Borel–Tits (1972), Proposition 4.3 (ii)′ with Corollaire 4.4, in the form
recorded in the statement's Markdown. The source proves it by comparing the weight lattices of
`Φ` and of `Φ₁` through a base of `Φ` restricting to a base of `r(Φ)^×` (Borel–Tits 1965, 6.8).
This Lean proof takes a different route. Part 1 is the standard argument that each coset of a
coroot lattice contains a minuscule element (one pairing with every root to `-1`, `0` or `1`),
and that `0` is the only minuscule element of the coroot lattice itself. Here both facts are
proved directly over `ℤ` with Mathlib's canonical form. Steps 5–6 apply them to the absolute
coroot lattice `X_*(M_K) = Q(Φ̌)` (simply connected case) and to the image of `X_*(S)` in it.
