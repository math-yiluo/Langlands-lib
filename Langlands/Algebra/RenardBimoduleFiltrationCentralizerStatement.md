# Centralizers of filtered bimodules (Renard VI.10.4, Lemma): statement

Module `Langlands.Algebra.RenardBimoduleFiltrationCentralizerStatement`.
Namespace `Langlands.Algebra`. Universe parameters `u, v`.
The module contains one **statement**, the `Prop`-valued definition
`RenardBimoduleFiltrationCentralizerStatement`; it proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read VI.10.4, printed pp.211–212 / PDF pp.217–218. The Lemma
starts at the bottom of printed p.211 and ends at the top of printed p.212:

> **Lemme.** Soit `A` un anneau commutatif unitaire, et `𝒞` la catégorie des
> `A`-bimodules (unitaires). Pour tout `M ∈ 𝒞`, on note
> `𝒞_A(M) = {a ∈ A | ma = am, (∀m ∈ M)}`.
> Supposons que `M ∈ 𝒞` admette une filtration
> `0 = M_{n+1} ⊂ M_n ⊂ M_{n−1} ⊂ ⋯ ⊂ M_1 ⊂ M_0 = M`
> dont les quotients successifs `Q_i = M_i/M_{i+1}`, `i = 0, …, n`, vérifient
> `Hom_𝒞(Q_i, Q_j) = 0` `(i ≠ j)`.
> Alors `𝒞_A(M) = ⋂_{i=0}^{n} 𝒞_A(Q_i)`.

The proof follows on printed p.212. The Lemma is pure commutative algebra and
uses nothing else from the book.

## The statement

For every commutative ring `A : Type u`, every additive group `M : Type v`
with a module structure over `A ⊗[ℕ] Aᵐᵒᵖ`, every `n : ℕ` and every
`F : ℕ → Submodule (A ⊗[ℕ] Aᵐᵒᵖ) M` such that

- `F 0 = ⊤` and `F (n + 1) = ⊥`;
- `F (i + 1) ≤ F i` for every `i ≤ n`;
- for all `i, j ≤ n` with `i ≠ j`, every `A ⊗[ℕ] Aᵐᵒᵖ`-linear map
  `Q_i → Q_j` is zero, where
  `Q_i = ↥(F i) ⧸ (F (i + 1)).comap (F i).subtype`,

the set `{a : A | ∀ x : M, (a ⊗ₜ 1) • x = (1 ⊗ₜ op a) • x}` equals the
intersection over `i ∈ Finset.range (n + 1)` of the sets
`{a : A | ∀ x : Q_i, (a ⊗ₜ 1) • x = (1 ⊗ₜ op a) • x}`.

## Formalization choices

- **Bimodules.** Following the convention documented in
  `Mathlib.Algebra.Module.Bimodule`, an `A`-bimodule is a module over the
  enveloping ring `A ⊗[ℕ] Aᵐᵒᵖ`: `a` acts on the left by `a ⊗ₜ 1` and on the
  right by `1 ⊗ₜ op a`. Unital `A`-bimodules (left and right actions that
  commute, each unital) are exactly unital modules over this ring;
  `A ⊗[ℕ] Aᵐᵒᵖ` and `A ⊗[ℤ] Aᵐᵒᵖ` are canonically isomorphic. Sub-bimodules are
  submodules, and morphisms in Renard's category `𝒞` are the
  `A ⊗[ℕ] Aᵐᵒᵖ`-linear maps.
- **Centralizers.** `𝒞_A(N) = {a ∈ A | na = an ∀ n ∈ N}` is written
  `{a | ∀ x, (a ⊗ₜ 1) • x = (1 ⊗ₜ op a) • x}`, the set of `a` whose left and
  right actions agree. The conclusion is an equality of subsets of `A`.
- **Filtration.** Renard's filtration is the function `F` with `M_i = F i`
  for `0 ≤ i ≤ n + 1`; its values beyond `n + 1` play no role. The inclusions
  `⊂` of the source are inclusions in the French sense, not necessarily
  strict, and the statement requires only `F (i + 1) ≤ F i`. A repeated term
  gives a zero quotient, for which the hypothesis is vacuous and the
  centralizer is all of `A`.
- **Quotients.** `Q_i = M_i/M_{i+1}` is the quotient of the submodule
  `↥(F i)` by `F (i + 1)` pulled back to `↥(F i)`. Instance search does not
  find the additive group structure of `↥(F i)` for submodules over
  `A ⊗[ℕ] Aᵐᵒᵖ`, so the statement supplies it by
  `letI : ∀ i, AddCommGroup ↥(F i) := fun i => (F i).addCommGroup`, the
  standard Mathlib structure `Submodule.addCommGroup`.
- **The hypothesis `Hom_𝒞(Q_i, Q_j) = 0`** is stated for `i, j ∈ {0, …, n}`
  with `i ≠ j`, as "every linear map `Q_i → Q_j` is zero".
- **Universes.** The ring and the bimodule live in independent universes
  `u` and `v`.

## Why the statement is true

Renard argues by induction on `n`; the case `n = 0` is trivial, since then
`Q_0 ≅ M`. For the inductive step, `M_1` carries the filtration
`M_{n+1} ⊂ ⋯ ⊂ M_1` with quotients `Q_1, …, Q_n`, so
`𝒞_A(M_1) = ⋂_{i=1}^{n} 𝒞_A(Q_i)` by induction. From
`0 → M_1 → M → Q_0 → 0` one gets `𝒞_A(M) ⊂ 𝒞_A(M_1) ∩ 𝒞_A(Q_0)`.
Conversely, for `β ∈ 𝒞_A(M_1) ∩ 𝒞_A(Q_0)`, the map `m ↦ βm − mβ` sends `M`
to `M_1` (since `β ∈ 𝒞_A(Q_0)`) and vanishes on `M_1`, so it defines
`Q_0 → M_1`. Because `A` is commutative this map is a bimodule morphism:
`β(am) − (am)β = a(βm − mβ)` and similarly on the right. It vanishes, so
`β ∈ 𝒞_A(M)`.

Renard says only that the hypothesis forces this morphism to vanish. The
detail is that `Hom_𝒞(Q_0, M_1) = 0`. This follows from
`Hom_𝒞(Q_0, Q_j) = 0` for `1 ≤ j ≤ n`, by descending induction on `k` using
the left exactness of `Hom_𝒞(Q_0, −)` on `0 → M_{k+1} → M_k → Q_k → 0`. In a
formal proof it may be more convenient to show
`𝒞_A(M_k) = ⋂_{i ≥ k} 𝒞_A(Q_i)` by descending induction on `k`, from
`k = n + 1` down to `k = 0`.

## Use in the source

Renard applies the Lemma to the category of `ℨ_D`-bimodules and to
`Hom_M(Π_D, r_D i_P^G(Π_D))` with the filtration whose quotients are
`Hom_M(Π_D, w · Π_D)`, `w ∈ W(D)`, to obtain `ℨ_Ω = ℨ_D^{W(D)}`. That
application, together with `ℨ_Ω ⊂ ℨ_D^{W(D)}` and the identification of the
filtration, is not stated here. The published
`InducedProgeneratorCenterInclusionStatement` states `ℨ_Ω ⊂ ℨ_D` and
`ℨ_Ω = 𝒞_{ℨ_D}(R_Ω)`.

## Remaining obligations

The proof is a separate obligation. It is self-contained commutative
algebra over Mathlib.

## Imports

| Module | Used for |
| --- | --- |
| `Mathlib.Algebra.Module.Bimodule` | the bimodule convention and the tensor product ring `A ⊗[ℕ] Aᵐᵒᵖ` |
| `Mathlib.LinearAlgebra.Quotient.Basic` | quotient modules `Q_i` |
