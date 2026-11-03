# Jacquet's lemma from abstract Iwahori factorization and contraction

This module proves a conditional generalization of Jacquet's lemma (Renard,
VI.6.1) and its unnormalized admissibility corollary for an arbitrary
topological group `G`. It replaces
the structure theory of a reductive group (Renard V.5.2 together with the choice
`t ∈ C_A^{++}`) by an explicit predicate on a compact open subgroup `K` and an
element `g`. The representation has complex coefficients; no reductive-group,
root-datum or local-field hypothesis is required. It
imports only `Jacquet.IwahoriContraction` (the predicate `IsIwahoriContraction`,
its lemmas `upper_pow`, `levi_pow`, `eventually_mem`, and the cofinality
predicate `HasIwahoriContractionBasis`), `Jacquet.CompressionStabilizationProof`
(Fitting decomposition of compression), `Jacquet.BlockCompressionProof` (for the
generic lemma `map_averageMap_of_forall_eq`) and `Jacquet.SmoothTwist` (for
`Jacquet.isSmooth_action`).

It supplies the first four clauses of
`Langlands.Jacquet.IwahoriContractionJacquetStatement` for focused proof task
`70794755-13dc-4217-9b1e-b9e13ed7910d`. The closed Jacquet finite-length task
`73e60be8-481a-4cea-b464-eed3bd89be7f` is a separate consumer. The structural
input `hbasis : HasIwahoriContractionBasis N M Nbar` remains an explicit
hypothesis; its realization for actual reductive rational-point parabolics is
separate.

The original source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The precise passages are V.5.2(ii)–(iv), printed p.123 / PDF p.129, and VI.6.1,
printed pp.176–177 / PDF pp.182–183. Worker 834 authored the reused Lean proof.
Worker 1004 checked it against the current Library and original passages and
revised this documentation; the Lean implementation is unchanged.

All declarations are in `Langlands.Jacquet`. The group universe `uG` and the
carrier universe `uV` are independent. Throughout, `ρ : Representation ℂ G V`,
`N M Nbar : Subgroup G` and `hMN : M ≤ Subgroup.normalizer N`. The descended
action `action ρ N M hMN` of `M` on `Coinvariants ρ N`, the quotient map
`mk ρ N`, `fixedJacquetMap`, `compressedAction`, `stableImage`,
`powerKernelSup` and `stableImageJacquetMap` are the existing Library
definitions (`Jacquet.Coinvariants`, `Jacquet.CanonicalLiftDefinitions`). The
compression `compressedAction ρ hρ K hK g` is `v ↦ e_K(ρ(g) v)` on the actual
`K`-fixed vectors, where `e_K` is the normalized compact average
`Compact.averageMap`. It is Renard's operator `π(a_{t,K}) = π(e_K ∗ δ_t ∗ e_K)`
on `V^K`.

## The imported predicate

`IsIwahoriContraction K N M Nbar g` and `HasIwahoriContractionBasis N M Nbar`
are defined in `Langlands.Representation.Jacquet.IwahoriContraction`, whose
Markdown gives the seven fields and their source. Write `K_N = K ⊓ N`,
`K_M = K ⊓ M` and `K_Nbar = K ⊓ Nbar` (as subgroups of `G`). The proofs below
use the fields as follows. `factor` is the Iwahori decomposition
`K = K_Nbar K_M K_N` (Renard V.5.2 (ii), ledger row S21). `upper`, `levi` and
`lower` are the inclusions `g K_N g⁻¹ ⊆ K_N`, `g⁻¹ K_M g ⊆ K_M`,
`g⁻¹ K_Nbar g ⊆ K_Nbar` (V.5.2 (ii), S21). `exhaust` says every element of `N`
is conjugated into `K` by some `g ^ r` (V.5.2 (iii), S22). `contract` says
`(g ^ s)⁻¹ K_Nbar g ^ s` lies in any given open subgroup for large `s`
(V.5.2 (iv), S23). The labels S21–S23 are the rows of the project's Chapter V
ledger `notes/renard/chapter-v-structural-inputs.md`; Renard's Théorème V.5.2
is on printed p. 123 (PDF p. 129).

The orientation matches Renard's proof of VI.6.1 (printed p. 176, PDF p. 182).
There `t ∈ C_A^{++}` satisfies `t⁻¹ K_Nbar t ⊂ K_Nbar` and `t⁻¹ K_M t = K_M`, and
`{t⁻ᵐ K_Nbar tᵐ | m ∈ ℕ}` is a neighbourhood base of the identity in `Nbar`.
The `upper` and `exhaust` fields also support the eventual-vanishing argument
below. Renard's section construction on PDF p.183 instead uses uniform
compact containment from V.5.2 and the operator identities of V.5.3.
The predicate does not require `g` to be central in `M`, and it does not
require `K_M` to be normalized by `g`. Only the inclusions above are used.

## Declarations

| Declaration | Statement |
| --- | --- |
| `exists_upper_translate` | if `b⁻¹ K_Nbar b ⊆ K` and `b⁻¹ K_M b ⊆ K`, then for `v ∈ V^K` and `k ∈ K` there is `u ∈ K_N` with `ρ k (ρ b v) = ρ u (ρ b v)` |
| `compressedAction_mul_of_factor` | `compressedAction (a * b) = compressedAction a * compressedAction b` when `a K_N a⁻¹ ⊆ K` and `b` is as above |
| `mk_compressedAction_of_factor` | for `b : M` as above, `mk ρ N (e_K(ρ b v)) = action ρ N M hMN b (mk ρ N v)` on `V^K` |
| `IsIwahoriContraction.compressedAction_pow` | `compressedAction (g ^ r) = compressedAction g ^ r` |
| `mk_compressedAction_of_iwahoriContraction` | the identity (VI.6.1.1): `j(a_{g,K} v) = π_N(g) j(v)` |
| `powerKernelSup_eq_ker_of_iwahoriContraction` | `powerKernelSup ρ hρ K hK g = ker (fixedJacquetMap ρ N M hMN K)` |
| `IsIwahoriContraction.exists_pow_lower_fixed` | for smooth `ρ` and any `v`, some `ρ (g ^ s) v` is fixed by `K_Nbar` |
| `stableImageJacquetMap_bijective_of_iwahoriContraction` | if `V^K` is finite dimensional, `stableImageJacquetMap ρ hρ K hK g N M hMN` is bijective |
| `finiteDimensional_fixedVectors_action_of_iwahoriContraction` | if `V^K` is finite dimensional, so is `(V_N)^{K ∩ M}` |
| `fixedJacquetMap_surjective_of_iwahoriContraction` | if `V^K` is finite dimensional, `j : V^K → (V_N)^{K ∩ M}` is surjective |
| `isAdmissible_action_of_iwahoriContraction` | if `ρ` is admissible and `hbasis : HasIwahoriContractionBasis N M Nbar`, then `action ρ N M hMN` is admissible |

In the last theorem, `HasIwahoriContractionBasis N M Nbar` says: for every
`L : OpenSubgroup M` there is `K : OpenSubgroup G` with `IsCompact (K : Set G)`,
`K.toSubgroup.comap M.subtype ≤ L.toSubgroup` and some `g` with
`IsIwahoriContraction K N M Nbar g`. Every other theorem takes one `K`, its
compactness witness `hK`, and one `h : IsIwahoriContraction K N M Nbar g`.

`fixedJacquetMap_surjective_of_iwahoriContraction` generalizes the weak Jacquet
lemma of VI.6.1 under the displayed structural hypotheses. It assumes only
that `V^K` is finite dimensional, which is weaker than admissibility of `V`.
`stableImageJacquetMap_bijective_of_iwahoriContraction` is a derived analogue
of the isomorphism on PDF p.183: its domain is the stable image
`⋂ᵣ Im(a_{g,K}^r)`. Renard's domain is `Im a_{t,K}` for a sufficiently
contracting single element `t ∈ C_A^+(ε)`; comparison with that domain remains
separate. `isAdmissible_action_of_iwahoriContraction` conditionally generalizes
the first sentence of the Corollary of VI.6.1, for the unnormalized
`(π_N, V_N)`.

## Implemented proof

Three private helpers do the bookkeeping. `apply_eq_of_mem_fixedVectors`
unfolds `Langlands.fixedVectors`. `averageMap_apply_mem` shows
`e_K(ρ k v) = e_K v` for `k ∈ K`, since the `K`-orbits of `ρ k v` and `v` agree.
`apply_apply_eq` shows that `k` fixes `ρ b v` when `b⁻¹ k b` fixes `v`.

**Compression identities.** For `v ∈ V^K` and `k ∈ K`,
`exists_upper_translate` factors `k⁻¹ = l m u` by `factor`. Then
`k = u⁻¹ m⁻¹ l⁻¹`, and `l⁻¹`, `m⁻¹` fix `ρ b v` by `apply_apply_eq`. So
`ρ k (ρ b v) = ρ u⁻¹ (ρ b v)`. For multiplicativity,
`compressedAction_mul_of_factor` applies the Library lemma
`map_averageMap_of_forall_eq` to `f = e_K ∘ ρ a` and the vector `ρ b v`. Each
`K`-translate becomes `e_K(ρ a (ρ u (ρ b v))) = e_K(ρ (a u a⁻¹) (ρ (a b) v))`,
and `a u a⁻¹ ∈ K` is absorbed by `averageMap_apply_mem`. This is the analogue of
Renard's Lemma V.5.3. `mk_compressedAction_of_factor` applies the same lemma to
`f = mk ρ N`; the factor `ρ u` with `u ∈ N` disappears by the Library lemma
`mk_apply_subgroup`, and `action_mk` identifies `mk ρ N (ρ b v)`. This is
(VI.6.1.1). `compressedAction_pow` follows by induction on `r` with the pair
`(g ^ r, g)`.

**Kernel.** `relations_eventually_average_zero` (private) proves, by span
induction on `relations_eq_span`, that every Jacquet relation `w` satisfies
`e_K(ρ (g ^ s) w) = 0` for all large `s`. For a generator `ρ x w - w` with
`x : N`, the imported `eventually_mem` gives a threshold after which
`g ^ s * x * (g ^ s)⁻¹ ∈ K`, so the two averages agree. Sums take the maximum of
the thresholds. `powerKernelSup_eq_ker_of_iwahoriContraction` then proves both
inclusions. If `(compressedAction g)^r v = 0`, iterating (VI.6.1.1) gives
`action (g ^ r) (mk v) = 0`, and the action is bijective
(`Representation.apply_bijective`), so `mk v = 0`. Conversely `mk v = 0` puts
`v` in the relations (`mk_eq_zero`), and `compressedAction_pow` turns the
eventual vanishing into membership in some kernel. This requires no finite
dimensionality. It supplies an alternative power-kernel argument for this
proof; Renard's (VI.6.1.2) instead annihilates the entire fixed-vector quotient
kernel with a sufficiently contracting single operator, using Proposition
III.2.9 and Theorem V.5.2. That uniform single-operator conclusion is a
separate obligation.

**Bijectivity.** Assume `V^K` is finite dimensional. The Library theorems
`powerKernelSup_isCompl_stableImage` and `stableImageAction_bijective` give
`V^K = T ⊕ S` with `T` the power-kernel supremum and `S` the stable image, and
compression bijective on `S`. Injectivity: a stable-image vector in the kernel
of `j` lies in `T ⊓ S = ⊥`. Surjectivity: let `y ∈ (V_N)^{K ∩ M}` and choose a
lift `v` (`mk_surjective`). By `exists_pow_lower_fixed` (smoothness of `ρ` and
`contract`) there is `s` such that `K_Nbar` fixes `ρ (g ^ s) v`. For every
`k ∈ K`, factor `k⁻¹ = l m u`; then `l⁻¹` fixes, `u⁻¹` is killed by `mk`, and
`(g ^ s)⁻¹ m⁻¹ g ^ s ∈ K_M` (the imported `levi_pow`) fixes `y`. Hence every `K`-translate of
`ρ (g ^ s) v` has image `action (g ^ s) y`, and so does its average
(`map_averageMap_of_forall_eq`). Since `T = ker j` and `V^K = T ⊕ S`, some
`t ∈ S` has `j t = action (g ^ s) y`. Finally the action of `g` is cancelled
`s` times: if `j t = action g z` with `t ∈ S`, write `t = compressedAction g t'`
with `t' ∈ S` (bijectivity on `S`); then (VI.6.1.1) and injectivity of
`action g` give `j t' = z`.

This route differs from Renard's. Renard first proves surjectivity from the
finite dimensionality of `j(V^K)` and the invertibility of `π_N(t)`, and then
the decomposition. The Lean proof gets the decomposition from Fitting's lemma
for one operator and deduces surjectivity.

**Consequences.** `finiteDimensional_fixedVectors_action_of_iwahoriContraction`
is `Module.Finite.of_surjective` along the bijection, and
`fixedJacquetMap_surjective_of_iwahoriContraction` composes the bijection with
the inclusion of `S`. For `isAdmissible_action_of_iwahoriContraction`,
smoothness is `Jacquet.isSmooth_action`. Given `L : OpenSubgroup M`, `hbasis`
gives `K` and `g`; admissibility of `ρ` makes `V^K` finite (Casselman's
all-open-subgroups convention of `Langlands.IsAdmissible`); and
`(V_N)^L ≤ (V_N)^{K ∩ M}` because `K ∩ M ≤ L`, so `Module.Finite.of_injective`
along the inclusion finishes.

## Scope and uncovered statements

- `HasIwahoriContractionBasis N M Nbar` is not proved here. For a parabolic `P = M N` of a connected reductive
  group over a nonarchimedean local field, it follows from Renard Théorème V.5.2
  and the Corollary's proof (PDF p. 183: a neighbourhood base of compact open
  subgroups with Iwahori decomposition along `P`). In the project these are the
  structural inputs S20–S23 of the Chapter V ledger
  (`notes/renard/chapter-v-structural-inputs.md`).
- The independence of `V^K = V^K_0 ⊕ V^K_*` from `t` and the canonical section
  `s_P^K` (Proposition, PDF p.183) remain separate, as does comparison of the
  power-kernel and stable-image submodules with Renard's sufficiently
  contracting single-operator kernel and image.
- Howe's theorem VI.6.3, Jacquet finite generation VI.1.3 and the closed
  finite-length theorem VI.6.4 are neither proved nor assumed here.
- `G` is any topological group. The private group-theoretic helpers omit
  the `IsTopologicalGroup` instance; it is used only through compact averages.
