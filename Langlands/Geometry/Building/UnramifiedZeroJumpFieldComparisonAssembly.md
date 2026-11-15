# The zero-jump comparison over `F` and `F^ur`, given two Galois descent principles

Module `Langlands.Geometry.Building.UnramifiedZeroJumpFieldComparisonAssembly`.

This module reduces `Langlands.Geometry.Building.UnramifiedZeroJumpFieldComparisonStatement`
(module `UnramifiedZeroJumpFieldComparisonStatement`) to two principles about zero-value
filtration jumps: an ascent principle `hfwd` and a descent principle `hdesc`. The module has
no `def` and states nothing new. It proves three theorems. The last one takes `hfwd` and
`hdesc` as hypotheses, so it does **not** prove the target statement unconditionally.

Notation. `K/k` is a field extension, `b = algebraBaseMap k K`, and `S_K`, `T_K`, `G_K`,
`f_K`, `iS_K`, `iT_K` and `α_K = characterLattice.baseChange b S α` are the base changes along
`b`. `IsRootFiltrationJump i ψ a r` (module `RootJumpLiftNonMultipliable`) is
`U_{a,ψ,r} ⊈ U_{a,ψ,r+} · U_{2a}`. `RootFunctionFamily.fieldRestrict ψ` is the family
`a ↦ (g ↦ ψ_{a_K}(g_K))` on `(G, S)`.

## The three hypotheses

These are the hypotheses (H1)–(H3) of `hdesc` in `unramifiedZeroJumpDescent_of_galoisDescent`
(module `UnramifiedZeroJumpDescentAssembly`, Task 6754). For a family `ψ` of root functions
of `(G_K, S_K)` and a root `α` of `(G, S)`, write `U = rootGroupPoints iS_K α_K`.

- (H1) For `g, h ∈ U`, `min (ψ_{α_K} g) (ψ_{α_K} h) ≤ ψ_{α_K} (g h⁻¹)`.
- (H2) For `σ ∈ Aut(K/k)` and `g ∈ U`, `ψ_{α_K} (σ g) = ψ_{α_K} g`, where `σ g` is
  `rationalConjugate k K G σ g`.
- (H3) For `t ∈ characterValuationKernel v S_K` (every rational character of `S_K` has
  `v`-valuation one at `t`) and `g ∈ U`, `ψ_{α_K} (t g t⁻¹) = ψ_{α_K} g`, where `t` also
  denotes its image `rationalPoints.map iS_K t` in `G_K(K)`.

## Results

All three theorems have the same data. `iS : S ⟶ G`, `iT : T ⟶ G` and `f : S ⟶ T` satisfy
`groupHom f ≫ iT = iS`, and `iT_K` is a monomorphism. `S` is split over `k`, `T_K` is split
over `K`, and `iT_K` has opposite factor pairs. `v` is a valuation of `K` with values in `ℤₘ₀`
and `C` is a centralizer datum for `iT_K`. `φ` is a valuation of the root datum of
`(G_K, T_K)` that satisfies V6 for `(v, C)` and is fixed by every `σ ∈ Aut(K/k)`. Finally
`α ∈ relativeRoots iS`.

### (H1)–(H3) for the torus restriction

`torusRestrictedRootFunctionFamily_descentHypotheses`. With the data above, let
`ψ = torusRestrictedRootFunctionFamily (hS.baseChange b) hT hE hφ f_K`, the torus restriction
of `φ` to `S_K`. Then (H1), (H2) and (H3) hold for `ψ` and `α`, as one conjunction.

Proof.

1. `groupHom f_K ≫ iT_K = iS_K`, by rewriting with `hf` and using `Functor.map_comp`.
2. `α_K` is a root of `(G_K, S_K)` for the composite `groupHom f_K ≫ iT_K`: rewrite with
   step 1 and use `mem_roots_baseChange_iff`.
3. (H1) is `torusRestrictedRootFunctionFamily_min_le_mul_inv` at the root of step 2, after
   step 1 rewrites the membership hypotheses `g, h ∈ U`.
4. (H2) is `torusRestrictedRootFunctionFamily_rationalConjugate`, which uses the Galois
   fixedness of `φ`.
5. (H3) is `torusRestrictedRootFunctionFamily_conj_of_mem_characterValuationKernel`, which
   uses V6 together with `C.j`, `C.s`, `C.bijective`, `C.isRepresentedBy` and `C.comp_eq`.
   Step 1 rewrites its conclusion.

The three lemmas cited in steps 3–5, and `mem_roots_baseChange_iff`, are proved in module
`TorusRestrictedRootInvariance` (Task 6754).

### The core iff, over an arbitrary field extension

`isRootFiltrationJump_torusFieldRestricted_iff_of_galoisDescent`. Data as above, plus two
hypotheses that quantify over every family `ψ` of root functions of `(G_K, S_K)` that
satisfies (H1), (H2) and (H3) for `α`:

- `hfwd`: if `α_K` has no jump at `0` for `ψ`, then `α` has no jump at `0` for
  `fieldRestrict ψ`;
- `hdesc`: if `α_K` has a jump at `0` for `ψ`, then `α` has a jump at `0` for
  `fieldRestrict ψ`.

Conclusion: `α` has a jump at `0` for
`torusFieldRestrictedRootFunctionFamily hS hT hE hφ f_K` (module
`RootValueTorusFieldRestriction`) if and only if `α_K` has a jump at `0` for the torus
restriction `ψ = torusRestrictedRootFunctionFamily (hS.baseChange b) hT hE hφ f_K`.

Proof. The previous theorem gives (H1)–(H3) for `ψ`. By definition,
`torusFieldRestrictedRootFunctionFamily hS hT hE hφ f_K` is `fieldRestrict ψ` (`rfl`), and
the goal is rewritten to that form. The direction `→` holds by contradiction: if `α_K` had
no jump for `ψ`, then `hfwd` would rule out the jump of `α` for `fieldRestrict ψ`. The
direction `←` is `hdesc`.

### The target, given the two principles

`unramifiedZeroJumpFieldComparison_of_galoisDescent (hfwd) (hdesc) :
UnramifiedZeroJumpFieldComparisonStatement.{u}`.

The two hypotheses share their binders. For every nonarchimedean local field `F` with
`K = inertiaFixedField F` (the maximal unramified extension), every connected reductive `G`,
every maximal split torus `iS : S ⟶ G`, every `α ∈ relativeRoots iS`, and every family `ψ` of
root functions of `(G_K, S_K)` that satisfies (H1), (H2) and (H3) with
`v = MaximalUnramified.valuation F`:

- `hfwd`: `¬ IsRootFiltrationJump iS_K ψ α_K 0 → ¬ IsRootFiltrationJump iS (fieldRestrict ψ) α 0`;
- `hdesc`: `IsRootFiltrationJump iS_K ψ α_K 0 → IsRootFiltrationJump iS (fieldRestrict ψ) α 0`.

The text of `hdesc` is copied verbatim from the `hdesc` hypothesis of
`unramifiedZeroJumpDescent_of_galoisDescent`. `hfwd` keeps the same binders and changes only
the conclusion. This module proves neither principle. Each is to be proved in its own
module.

Proof. Introduce the data of the target statement: `F`, `G`, `hG`, `S`, `iS`, `hiS`, `T`,
`iT`, `f`, `hf`, `hiT`, `hE`, `D`, `C`, the V6 hypothesis `hΩ`, the fixed point `x` with
`hx : fixed x`, the families `φx`, `ψx` with their defining equations, and `α`, `hα`. The
instances `IsAffineHom` and `Smooth` come from `hG`, and the monomorphisms come from
`mono_of_isMaximalSplitTorus` for `hiS` and `hiT`. `subst` replaces `φx` and `ψx` by their
definitions. Then the core iff applies with `k = F`, `K = inertiaFixedField F`, split tori
`hiS.isSplitSubtorus.1` and `hiT.isSplitSubtorus.1`, `v = MaximalUnramified.valuation F`,
`φ = x.val` (`D.isRootDatumValuation_of_mem x.mem`), V6 from `hΩ x.val x.mem`, Galois
fixedness `hx`, and `hfwd`, `hdesc` specialized to `F, G, hG, S, iS, hiS, α, hα`. The two sides
of the core iff are the two sides of the target. The declaration needs
`maxHeartbeats 6400000`.

## Scope and provenance

This is internal infrastructure, not a transcription of a numbered result of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023). The Markdown of the target statement explains
its relation to KP Proposition 9.4.28. Here we prove only that the target follows from
`hfwd` and `hdesc`. The case `2α ∉ Φ(G, S)` needs no separate argument, because both
principles are stated for every root `α`.
