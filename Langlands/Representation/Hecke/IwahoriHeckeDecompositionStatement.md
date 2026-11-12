# The decomposition of the Hecke algebra `H(G, K)`: statement

Module `Langlands.Representation.Hecke.IwahoriHeckeDecompositionStatement`.
Namespace `Langlands.Hecke`. Universe parameter `u`.
The module contains one **statement**, the `Prop`-valued definition
`IwahoriHeckeDecompositionStatement`; it proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read V.3.23–V.3.24, V.5.1–V.5.3, printed pp.117–125 /
PDF pp.123–131. V.5.3 is printed pp.123–125 / PDF pp.129–131:

> Rappelons que si `K` est un sous-groupe ouvert compact de `G`, et si `g` est
> un élément de `G`, nous avons défini en II.3.12, remarque 2, la distribution
> `a_{g,K} := e_K ∗ δ_g ∗ e_K` dans `H(G, K)`. […] Fixons un sous-groupe ouvert
> compact `K` de `G`, contenu et distingué dans `K₀` et admettant une
> décomposition d'Iwahori selon les sous-groupes paraboliques standards.
> Choisissons un système de représentants `{x₁, …, x_r}` des classes de `K`
> dans `K₀`. Posons `H₀ := H(K₀, K)`. Il est clair que `H₀` est une
> sous-algèbre de dimension finie de `H(G, K)` dont une base est
> `{a_{x_i}}`.
>
> **Lemme.** Pour tout `g ∈ G`, on a : `a_g a_{x_i} = a_{g x_i}`,
> `a_{x_i} a_g = a_{x_i g}`.
>
> **Lemme.** Soient `z₁, z₂ ∈ C_∅^+`. Alors `a_{z₁} a_{z₂} = a_{z₁ z₂}`.
>
> Soit `A` la sous-algèbre de `H(G, K)` engendrée par les `a_z`, `z ∈ C_∅`.
> Comme `C_∅` est un groupe abélien, on en déduit :
>
> **Corollaire.** La sous-algèbre `A` est abélienne : quels que soient
> `z₁, z₂ ∈ C_∅^+`, `a_{z₁} a_{z₂} = a_{z₂} a_{z₁}`.
>
> Notons `M` la sous-algèbre de `H(G, K)` engendrée par les éléments `a_{zf}`
> avec `z ∈ C_∅^+` et `f ∈ F_∅`.
>
> **Lemme.** L'algèbre `M` est un `A`-module de type fini.
>
> Soit `{D_j}_{j=1,…,q}` un système de générateurs fini du `A`-module `M`. […]
>
> **Théorème.** L'algèbre de Hecke `H(G, K)` se décompose en :
> `H(G, K) = ∑_{j=1}^q H₀ A D_j H₀`.
>
> **Remarque.** En considérant la structure de `A`-module à droite de `M` et
> en adaptant les démonstrations ci-dessus, on obtient aussi une décomposition
> de `H(G, K)` sous la forme `H(G, K) = ∑_{j=1}^{q'} H₀ E_j A H₀`, où les
> `E_j` sont des éléments de `M`.

Here (V.3.23) `C_A` is the lift `X_*(A) → A(F)`, `λ ↦ λ(ϖ)`, of `Λ(A)`;
`F_M ⊆ M` is a finite set with `C_A F_M` a set-theoretic lift of
`Λ(M) = M/⁰M`; `C_A^+ = C_A ∩ M^+`; and Renard arranges `F_M ⊆ M^+` and
`C̃_A^+ := C̃_A ∩ M^+ = C_A^+ F_M` ("c'est ce que nous supposerons dans la
suite"). The proof of the Theorem uses the Cartan decomposition
`G = K₀ C_∅^+ F_∅ K₀` (V.5.1).

The Library's coverage notes (`notes/renard/coverage-update-2026-11-10.md`)
record the decomposition of `H(G, K)` in V.5.3 as not stated; its proof
mechanism is implemented by the internal constructions
`IwahoriSandwich`, `ResidualIwahoriSandwich`, `ResidualCosetStabilization`
and `FiniteResidualSandwich` for abstract groups, without the reductive
Cartan data.

The provenance is source. The coverage of V.5.3 is **partial**: the
statement contains the finite-dimensionality and basis of `H₀`, the two
Lemmas on products, the Corollary, the finiteness Lemma in its module form,
the Theorem and the Remark, in the formal reading described below. The
finiteness Lemma for Renard's generated *subalgebra* `M` is not stated; it is
retained as an outstanding source obligation (see "Not stated" below).

## Framework and published objects

All objects are published; this file constructs nothing.

- `F` is a nonarchimedean local field and `G` a connected reductive group
  scheme over `F` (`hG : IsConnectedReductive G`). `G(F)` has the canonical
  topology `rationalPointTopology F G.X`, which makes it a topological group
  (`rationalPoint_isTopologicalGroup`, using smoothness `hG.smooth`). It is
  assumed Hausdorff and given a Borel measurable structure, as in the
  published VI.4.5 statement `RationalSummandBlockCenterStatement`.
- `𝔅 : KPBuildingAssignment` with `𝔅.IsAvailableFor F G hG`: corrected
  Kaletha–Prasad building data available for `G`, as in the published
  `AvailableCartanStatement` (Bruhat–Tits Cartan decomposition). Its base
  datum `B = (𝔅.datum F G hG).base` supplies the maximal split torus
  `B.i : S → G`, the centralizer `j = B.centralizer.j : Z → G` (Renard's
  `M_∅`), `s = B.centralizer.s : S → Z`, and the apartment.
- `ν` is a generic cocharacter of `S`; it fixes the positive roots and the
  standard parabolic subgroups (`P_∅` and the `P_J`).
- `x` is a special vertex of the apartment and
  `K₀ = B.apartment.specialCompactSubgroup x` the special maximal compact
  subgroup (Renard's `K₀`, V.5.1), as in the published
  `AvailableSimultaneousStandardBasisStatement`.
- `K : OpenSubgroup G(F)`, compact, with `K ≤ K₀` and `k₀ k k₀⁻¹ ∈ K` for
  `k₀ ∈ K₀`, `k ∈ K` (normal in `K₀`). "Admettant une décomposition
  d'Iwahori selon les sous-groupes paraboliques standards" is read as
  Renard's V.5.2 (ii) for `K`, for every standard parabolic `P_J`: some
  compatible split component `q : A → S`
  (`IsCompatibleStandardSplitComponent`) with
  `StandardParabolicBasisMember B.i ν J q K`. That published predicate is the
  Iwahori factorization `K = K_{N̄} K_M K_N` together with the contraction
  clauses (`C_A` normalizes `K_M`, `C_A^+` contracts `K_N`, `C_A^-`
  contracts `K_{N̄}`) and the cofinality clauses of V.5.2 (iii)–(iv); it is
  the property of the members of the basis of V.5.2.
- `F₀ ⊆ Z(F)` is a finite set with
  `Plancherel.RenardCartan.IsFiniteLatticeTransversal s F₀`: exactly one
  element in each coset of `Λ(Z)` modulo the image of `Λ(S)`, so that
  `C_∅ F₀` lifts `Λ(Z)` (Renard's `F_∅`).
- `haar` is a Haar measure on `G(F)` and `HeckeAlgebra.Corner haar K hK` is
  `H(G, K)`, the unital algebra of `K`-bi-invariant test functions under
  convolution.
- `a g = HeckeAlgebra.Corner.massIndicator K hK haar g` is the indicator of
  `K g K` divided by its Haar mass. This is Renard's
  `a_{g,K} = e_K ∗ δ_g ∗ e_K`: that measure is `K`-bi-invariant, supported on
  `K g K`, of total mass one, hence equal to `1_{KgK} / vol(KgK)`.
- `C_∅ = Plancherel.RenardCartan.C0 S s ⊆ Z(F)` is the image of `S(F)`'s
  uniformizer section `λ ↦ λ(ϖ)`, Renard's `C_{A_∅}`;
  `dom = BruhatTits.Cartan.parahoricDominantSet B ν` is the dominant part of
  `Z(F)` (Renard's `M_∅^+`), the set used in the Cartan decomposition of
  `AvailableCartanStatement`.
- `C⁺ = C_∅ ∩ dom` is Renard's `C_∅^+`, and
  `C̃⁺ = Plancherel.RenardCartan.tildeC0Plus s F₀ dom = (C_∅ F₀) ∩ dom` is
  Renard's `C̃_∅^+`. Elements of `Z(F)` are mapped to `G(F)` by
  `rationalPoints.map j`.

## The statement

`IwahoriHeckeDecompositionStatement` asserts, for all such data:

1. **`H₀`.** `span {a x | x ∈ K₀}` is finite-dimensional, the set of the
   `a x` (`x ∈ K₀`) is linearly independent, and `a x = a x'` exactly when
   `x⁻¹ x' ∈ K`. So `{a_{x_i}}`, for representatives `x_i` of `K₀/K`, is a
   basis of `H₀`.
2. **First Lemma.** `a g * a x = a (g x)` and `a x * a g = a (x g)` for every
   `g ∈ G(F)` and `x ∈ K₀` (Renard states it for the representatives `x_i`;
   `a x` only depends on `x K`).
3. **Second Lemma.** `a z₁ * a z₂ = a (z₁ z₂)` for `z₁, z₂ ∈ C⁺`.
4. **Corollary.** Any two elements of the subalgebra `A` generated by the
   `a z`, `z ∈ C⁺`, commute.
5. **Finiteness Lemma, module form.** There are finitely many `t_k ∈ C̃⁺`
   such that every `a t`, `t ∈ C̃⁺`, is a linear combination of products
   `a z * a t_k`, `z ∈ C⁺`. Since `A` is spanned by the `a z` (by 3), this
   says that the left `A`-module generated by the individual `a t`,
   `t ∈ C̃⁺`, is generated by finitely many of them. This is not Renard's
   assertion about the generated subalgebra `M` (see "Not stated").
6. **Theorem.** For every finite family `D_k ∈ H(G, K)` such that every `a t`,
   `t ∈ C̃⁺`, is a linear combination of products `a z * D_k`, the products
   `a x * a z * D_k * a x'` (`x, x' ∈ K₀`, `z ∈ C⁺`) span `H(G, K)`. As `H₀`
   is spanned by the `a x` and `A` by the `a z`, this is
   `H(G, K) = ∑_k H₀ A D_k H₀`.
7. **Remark.** There are finitely many `t_k ∈ C̃⁺` such that every `a t` is a
   linear combination of products `a t_k * a z`, and the products
   `a x * a t_k * a z * a x'` span `H(G, K)`: `H(G, K) = ∑_k H₀ E_k A H₀`
   with `E_k = a t_k`.

## Formal choices and departures from the source

- **`A` is generated by `a_z`, `z ∈ C_∅^+`.** Renard writes "engendrée par
  les `a_z`, `z ∈ C_∅`", but the Corollary and all later uses concern
  `z ∈ C_∅^+`, and the deduction "comme `C_∅` est un groupe abélien" uses the
  second Lemma, which is stated for `C_∅^+` only. The argument gives no
  information on `a_z` for non-dominant `z`, so the statement follows the
  displayed content of the Corollary and uses `C_∅^+`.
- **`M` and Renard's arrangement `C̃^+ = C^+ F`.** Renard assumes (V.3.23)
  that `F_∅ ⊆ M_∅^+` and `C̃_∅^+ = C_∅^+ F_∅`; then the elements `a_{zf}`
  (`z ∈ C_∅^+`, `f ∈ F_∅`) are exactly the `a_t`, `t ∈ C̃_∅^+`. The statement
  does not assume this arrangement: `F₀` is any finite lattice transversal,
  and `M` is replaced by the `A`-module generated by the `a t`,
  `t ∈ C̃⁺ = (C_∅ F₀) ∩ dom`, whose elements cover the Cartan decomposition
  `G = K₀ C̃_∅^+ K₀`. Under the arrangement this is Renard's set of
  generators. The statement neither needs nor asserts the existence of such
  an arrangement. Item 5 is the module form described above; Renard's
  assertion about the subalgebra `M` is not replaced by it (see below).
- **Generators `D_j`.** The Theorem is stated for every finite family with
  the spanning property of item 5, not only for generators lying in `M`;
  this is stronger and is what the proof gives.
- **Iwahori decomposition.** Read as the published V.5.2 (ii) predicate,
  which also contains the cofinality clauses (iii)–(iv); the members of the
  V.5.2 basis satisfy it (published
  `AvailableSimultaneousStandardBasisStatement`).
- **Topological hypotheses.** `T2Space` and the Borel structure on `G(F)` are
  instance binders, as in the published VI.4.5 statement.

## Not stated: the finiteness Lemma for the subalgebra `M`

Renard defines `M` as "la sous-algèbre de `H(G, K)` engendrée par les
éléments `a_{zf}`" and asserts "L'algèbre `M` est un `A`-module de type fini".
This statement does **not** contain that assertion; it remains an
outstanding source obligation of the whole-book task.

- The generated subalgebra and the `A`-module generated by the `a_{zf}` can
  differ, even under Renard's arrangement. Example (Reviewer 1385):
  `G = G_m` over `ℚ₃`, `K₀ = ℤ₃^×`, `K = 1 + 3ℤ₃`, uniformizer `3`,
  `F₀ = {-1}`. With `T = a_3` and `ε = a_{-1}`, `A = ℂ[T, T⁻¹]`, the module
  generated by the `a_{zf}` is `Aε`, and the generated algebra is `A ⊕ Aε`
  (it contains `ε² = 1`). So item 5 is not Renard's assertion.
- Renard's proof computes `a_{z₁} a_{z₂ f}` for `z₁, z₂ ∈ C_∅^+` and
  `f ∈ F_∅` only, which gives the module form. Products `a_{zf} a_{z'f'}` of
  two generators are not treated; for elements `f` outside `C_∅`, the
  hypotheses on `K` (normality in `K₀`, contraction by `C_A^+`) do not by
  themselves control `f K_N f⁻¹` or `f⁻¹ K_M f`. The algebra form is
  therefore not established here, and no corrected version is proposed.
- The Theorem and the Remark need only the module form (item 5), which is
  how they are stated.

## Source issue: `C_∅^+ / C_{A_G}` need not be free

Renard V.3.24 (printed p.117 / PDF p.123) asserts that
`S = C_∅^+ / C_{A_G}` is isomorphic to `ℕ^d`, `d = |Δ_∅|`, and the proof of
the finiteness Lemma (printed p.125) runs a critical-point argument on `ℕ^d`.
This is false in general (Reviewer 1385): for the diagonal torus of `SL_3`,
`C_∅^+` is `{(a, b, c) ∈ ℤ³ | a + b + c = 0, a ≥ b ≥ c}`, which in the
simple-root coordinates `p = a - b`, `q = b - c` is
`{(p, q) ∈ ℕ² | p ≡ q mod 3}`; its indecomposable elements `(3,0)`, `(1,1)`,
`(0,3)` satisfy `(3,0) + (0,3) = 3·(1,1)`, so it is not free. The statement
does not use V.3.24; its proof must replace it (see below).

## Why the statement is true

- Items 1–2: `K` is normal in `K₀`, so `K x K = x K` and
  `e_K ∗ δ_x = δ_x ∗ e_K` for `x ∈ K₀`; `K₀/K` is finite (`K₀` compact, `K`
  open); distinct `a x` have disjoint supports (Library:
  `doubleCoset_mul_mul_of_mem_normalizer`, `massIndicator_mul`).
- Item 3: Renard's computation with `e_K = e_{K_N} ∗ e_{K_M} ∗ e_{K_{N̄}}`,
  `z₁ K_N z₁⁻¹ ⊆ K_N`, `z₂⁻¹ K_{N̄} z₂ ⊆ K_{N̄}`, `z K_M z⁻¹ = K_M`
  (Library: `massIndicator_mul`, `IwahoriSandwich`).
- Item 4: the generators commute by item 3, since `C_∅` is commutative.
- Item 5: for fixed `f ∈ F₀`, the `c ∈ C_∅` with `cf` dominant are the lattice
  points of a translated rational cone, a finite union of translates
  `C⁺ c_k` (Gordan's lemma). Renard's computation gives
  `a_{z₁} a_{z₂ t} = a_{z₁ z₂ t}` when the conjugated subgroups
  `z₂⁻¹ K_{N̄} z₂` and `(z₁z₂)⁻¹ K_{N̄} (z₁z₂)` have the same cosets `Γ t K`.
  The monoid `C⁺` (modulo `C_{A_G}`) is finitely generated by Gordan's lemma
  but need not be free (see the source issue above). Choose a surjective
  monoid map `ℕ^e → C⁺/C_{A_G}` from a finite generating set; it is
  order-preserving for the divisibility orders. Pull back the antitone
  function `z ↦ ∑_t |z⁻¹ K_{N̄} z t K / K|` to `ℕ^e`; Dickson's lemma gives
  finitely many critical points there, and their images generate. This
  replaces Renard's argument on `ℕ^d`.
- Item 6: Cartan decomposition (V.5.1; published `AvailableCartanStatement`
  for the parahoric of `x`, contained in `K₀`): every element of `Z(F)^+` is
  `c f u` with `cf ∈ C̃⁺` and `u` in the kernel `⁰Z` of the valuation, which
  lies in `K₀`; hence `G = K₀ C̃⁺ K₀`. Then `G = ⋃ K x_i C̃⁺ x_j K`, the
  `a_{x_i t x_j} = a_{x_i} a_t a_{x_j}` (item 2) span `H(G, K)`, and each
  `a_t` lies in the `A`-span of the `D_k`.
- Item 7: the same argument with right modules.

## Remaining obligations

The proof is a separate obligation. Its inputs are the Cartan decomposition
(published `AvailableCartanStatement`; check the Library for its proof), the
V.5.2 properties carried by the hypothesis on `K`, the Library's Hecke
sandwich constructions, finite generation of the dominant cone monoid
(Gordan's lemma) and the transport of the antitone finite-frontier argument
along a surjection from a finite orthant. The Library's orthant modules
(`ResidualCosetStabilization`, `FiniteResidualSandwich`) work on orthants
`ℕ^d`; they do not by themselves supply the comparison with `C_∅^+`, which
is a separate lattice obligation.

The finiteness Lemma for the generated subalgebra `M` remains an
outstanding obligation of the whole-book task (see "Not stated").

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.BruhatTits.Cartan.AvailableCartanStatement` | `KPBuildingAssignment`, `IsAvailableFor`, the base datum, `IsSpecialApartmentVertex`, `specialCompactSubgroup`, `parahoricDominantSet` |
| `Langlands.BruhatTits.SpecialCompact.StandardBasisProperty` | `IsCompatibleStandardSplitComponent`, `StandardParabolicBasisMember`, `simpleRelativeRoots` |
| `Langlands.Representation.Plancherel.RenardRepresentativeData` | `C0`, `tildeC0Plus`, `IsFiniteLatticeTransversal` |
| `Langlands.Representation.Hecke.DoubleCosetSandwich` | `HeckeAlgebra.Corner`, `massIndicator` |
| `Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups` | `rationalPoint_isTopologicalGroup` |
