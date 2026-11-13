# Renard VI.3.1, Lemma: proof

Module `Langlands.Representation.CuspidalSupport.RationalNormKernelConjugationLemmaProof`.
Namespace `Langlands.CuspidalSupport`.

This module proves the published proposition
`Langlands.CuspidalSupport.RationalNormKernelConjugationLemmaStatement.{u, uV, uW}`
(module `RationalNormKernelConjugationLemmaStatement`). The theorem is
`Langlands.CuspidalSupport.rationalNormKernelConjugationLemma`. Its type is exactly
that proposition, with the same three universe parameters `u`, `uV` and `uW`.
The statement's Lean/Markdown pair and its imports are unchanged, and no hypothesis
is added.

## What is proved

The source is the Lemma of VI.3.1 in David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, printed pp.142–143 / PDF
pp.148–149. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

Fix a nonarchimedean local field `F`, a connected reductive group scheme `G` over
`F`, and its rational-point group `G(F)` with the canonical topology. Write
`⁰G = Plancherel.rationalCommonNormKernel G` and, for `g ∈ G(F)`,
`conj g = MulAut.conjNormal g⁻¹`, the automorphism `h ↦ g⁻¹ h g` of `⁰G`. Then:

1. For every irreducible smooth complex representation `σ` of `⁰G` there is a
   finite set `S ⊆ G(F)` such that every `σ ∘ conj g` is equivalent
   (`Representation.Equiv`) to some `σ ∘ conj s` with `s ∈ S`.
2. For every smooth `π` of `G(F)`, every irreducible smooth `σ` of `⁰G` and every
   `g`, the image under `π(g)` of
   `span {f w | f : σ → π|_{⁰G} intertwining, w ∈ σ}` is
   `span {f w | f : σ ∘ conj g → π|_{⁰G} intertwining, w ∈ σ}`.

## Proof

The proof has two layers: three generic theorems about a group `Γ`, a normal
subgroup `N` and a commutative semiring `k`, and the final theorem, which applies
them to `Γ = G(F)`, `N = ⁰G` and `k = ℂ`.

### Generic theorems

**`nonempty_equiv_comp_conjNormal_mul_of_mem_sup_center`.** For a representation
`σ` of `N` on any `k`-module `W`, any `g ∈ Γ` and any `h ∈ N ⊔ Z(Γ)`, the
representations `σ ∘ conj (g h)` and `σ ∘ conj g` are equivalent.

Mathlib's `Subgroup.mem_sup_of_normal_left` writes `h = n z` with `n ∈ N` and
`z ∈ Z(Γ)`. Let `m = ⟨n, hn⟩ ∈ N`. Since `z` is central, `z⁻¹ a z = a` for all
`a ∈ Γ`. Using this, the identity
`(g n z)⁻¹ x (g n z) = n⁻¹ (g⁻¹ x g) n` holds in `Γ` for `x ∈ N`, so
`conj (g h) x = m⁻¹ · conj g x · m` in `N` (the step `key`; the group identity is
closed by the `group` tactic). The linear equivalence `e = σ(m)`, with inverse
`σ(m⁻¹)`, is built by `LinearEquiv.ofLinearMap`. It intertwines:

`σ(m) σ(m⁻¹ · conj g x · m) w = σ(conj g x · m) w = σ(conj g x) σ(m) w`.

`Representation.Equiv.mk` packages `e` with this identity.

**`exists_finset_nonempty_equiv_comp_conjNormal`.** If `N ⊔ Z(Γ)` has finite
index, then for every representation `σ` of `N` there is a finite set `S ⊆ Γ` such
that every `σ ∘ conj g` is equivalent to some `σ ∘ conj s` with `s ∈ S`.

Let `H = N ⊔ Z(Γ)`. Finite index makes `Γ ⧸ H` finite, so it carries a `Fintype`
structure. `S` is the image of `Finset.univ` under `Quotient.out`, a set of left
coset representatives. Given `g`, take `s = (g H).out ∈ S`. Mathlib's
`QuotientGroup.mk_out_eq_mul` gives `s = g h` with `h ∈ H`. The previous theorem
gives an equivalence `σ ∘ conj (g h) ≅ σ ∘ conj g`, and its inverse
(`Representation.Equiv.symm`) is the required `σ ∘ conj g ≅ σ ∘ conj s`.

**`map_span_intertwiningMap_range_eq`.** For a representation `π` of `Γ` on `V`,
a representation `σ` of `N` on `W` and `g ∈ Γ`, the image under `π(g)` of the span
of the images of all intertwiners `σ → π|_N` equals the span of the images of all
intertwiners `σ ∘ conj g → π|_N`. Here `π|_N = π ∘ N.subtype`. No irreducibility
is needed.

Mathlib's `Submodule.map_span` turns the image of the span into the span of the
image, so it suffices to prove that the two generating sets agree.

- If `x = π(g) (f w)` with `f : σ → π|_N`, then `π(g) ∘ f` intertwines
  `σ ∘ conj g` and `π|_N`: for `y ∈ N`,
  `π(g) f(σ(g⁻¹ y g) v) = π(g) π(g⁻¹ y g) f(v) = π(y) π(g) f(v)`.
  So `x` is the value at `w` of this intertwiner. It is built with
  `LinearMap.intertwiningMap_of_isIntertwiningMap`.
- Conversely, if `x = f'(w)` with `f' : σ ∘ conj g → π|_N`, then
  `π(g⁻¹) ∘ f'` intertwines `σ` and `π|_N`. For `y ∈ N` put
  `y' = g y g⁻¹ ∈ N`; then `conj g y' = y`, so the intertwining property of `f'`
  at `y'` reads `f'(σ(y) v) = π(g y g⁻¹) f'(v)`, and
  `π(g⁻¹) π(g y g⁻¹) f'(v) = π(y) π(g⁻¹) f'(v)`. Finally
  `π(g) (π(g⁻¹) (f' w)) = f' w` by Mathlib's `Representation.self_inv_apply`.

### The final theorem

After introducing `F`, `G` and `hG`, the proof recreates the instances fixed by the
statement (the affine structure map, affineness of `G.X.left`, smoothness, the
canonical topology `rationalPointTopology F G.X` and the topological-group
instance `rationalPoint_isTopologicalGroup F G`). It then installs as an instance
the published finite-index theorem
`rationalCommonNormKernel_sup_center_finiteIndex F G hG` (module
`RationalNormKernelCentralFiniteIndex`): `⁰G ⊔ Z(G(F))` has finite index. That
theorem derives the finiteness from the split component and Renard's Proposition
V.2.6 (finiteness of `G/⁰G A_G`).

- Part (i) is `exists_finset_nonempty_equiv_comp_conjNormal` applied to
  `σ.representation`.
- Part (ii) is `map_span_intertwiningMap_range_eq` applied to
  `π.representation`, `σ.representation` and `g`. The statement's local
  definitions `conj`, `res` and `iso` unfold to exactly these expressions.

The irreducibility hypotheses on `σ` are not used: both parts hold for every
representation of `⁰G`. Smoothness is not used either.

## Comparison with Renard

Renard's argument is the same. For (i), conjugation by `h ∈ ⁰G` gives an isomorphic
representation (via `σ(h)`), central elements act trivially by conjugation, and
`G/⁰G Z(G)` is finite. For (ii), `f ↦ π(g) ∘ f` identifies `Hom_{⁰G}(σ, π)` with
`Hom_{⁰G}(σ^g, π)`. The Lean proof describes the isotypic part as the span of the
images of all intertwiners, as in the statement, instead of the image of
`Hom_{⁰G}(σ, π) ⊗ W → V`.

The only axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.CuspidalSupport.RationalNormKernelConjugationLemmaStatement` | the target statement |
| `Langlands.Representation.CuspidalSupport.RationalNormKernelCentralFiniteIndex` | `rationalCommonNormKernel_sup_center_finiteIndex` |
