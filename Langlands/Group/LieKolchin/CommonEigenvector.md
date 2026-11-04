# Common eigenvectors of connected solvable groups

Worker 277.

This module proves the abstract Lie–Kolchin theorem
`exists_common_eigenvector_of_isSolvable`. The setting is a field `k` that is
algebraically closed. `G` is a solvable group whose topology makes it a preconnected
space. Left translations, inversion and the maps `y ↦ ⁅a, y⁆` are continuous (the
hypotheses `hmul`, `hinv`, `hcomm`). `ρ : G →* Module.End k V` acts on a nonzero
finite-dimensional `k`-vector space `V`. The closedness hypothesis `hR` says that
`{g | Λ (ρ g) = c}` is closed for every linear functional `Λ` on `Module.End k V` and
every `c : k`. The conclusion is a nonzero `v : V` that is an eigenvector of every `ρ g`.

## Declarations

- `exists_common_eigenvector`: a commuting family of endomorphisms of a nonzero
  finite-dimensional space over an algebraically closed field has a common eigenvector.
  The proof is strong induction on the dimension (`exists_common_eigenvector_aux`). If
  every member is a scalar, any nonzero vector works. Otherwise some `f i` is not a
  scalar. Take an eigenvalue `μ` of `f i`. The eigenspace `W` of `μ` is a nonzero proper
  subspace. It is invariant under every `f j`, because the family commutes. Apply the
  induction hypothesis to the restrictions to `W`.
- `weightSpace ρ χ`: for a monoid representation `ρ : A →* Module.End k V` and a
  function `χ : A → k`, the simultaneous eigenspace `⨅ a, eigenspace (ρ a) (χ a)`. The
  lemma `mem_weightSpace` characterizes it by `ρ a w = χ a • w` for all `a`.
  `disjoint_weightSpace` shows that the weight spaces of distinct functions are
  disjoint. `iSupIndep_weightSpace` shows that the family of all weight spaces is
  independent. That proof is induction on finite sets: for `χ ∉ insert ψ s`, choose `a`
  with `χ a ≠ ψ a`; the operator `ρ a - ψ a • 1` kills the `ψ` part and preserves the sum
  over `s`.
- `isClosed_linear_eq`, `isClosed_mapsTo` and `isClosed_eigen` are consequences of
  `hR`. Vector-valued linear conditions `L (ρ g) = m` are intersections of scalar ones in
  a basis of the target, so they are closed. Hence the set of `g` with `ρ g` mapping a
  subspace `W` into a subspace `U` is closed; it is cut out by the conditions
  `(ρ g w) mod U = 0` for `w ∈ W`. So is the set of `g` with `ρ g v = c • v`.
- `restrictHom ρ Γ W hW`: the restriction of `ρ` to a subgroup `Γ` that preserves `W`,
  as a homomorphism `Γ →* Module.End k W`.
- `exists_common_eigenvector_derivedSeries`: the inductive step, by induction on `m`.
  If `derivedSeries G (i + m) = ⊥`, then `derivedSeries G i` has a common eigenvector.
  This is described in the next section.
- `exists_common_eigenvector_of_isSolvable`: the main theorem. Solvability gives `n` with
  `derivedSeries G n = ⊥`. Apply the inductive step with `i = 0`, `m = n`.

## The inductive step

For `m = 0` the subgroup `derivedSeries G i` is trivial, and any nonzero vector works.
For the step write `Γ = derivedSeries G i` and `N = derivedSeries G (i + 1) = ⁅Γ, Γ⁆`.

1. The induction hypothesis gives a common eigenvector `v` of `N`, with eigenvalue
   function `χ` on `N`. Let `W` be the weight space of `χ` for `ρ` restricted to `N`.
   It is nonzero because it contains `v`.
2. `N` is normal in `G`. For `g : G`, `ρ g` maps `W` into the weight space of the
   conjugate function `a ↦ χ (g⁻¹ a g)`. Since weight spaces are independent and `V` is
   finite-dimensional, the set `T` of functions with nonzero weight space is finite.
3. For each `ψ` in `T`, the set `S ψ` of `g` with `ρ g W ⊆ weightSpace ψ` is closed. The
   sets `S ψ` cover `G`. They are pairwise disjoint, because `ρ g v ≠ 0` and distinct
   weight spaces meet only in zero. `Γ` is connected by `isConnected_derivedSeries`, and
   `1 ∈ Γ ∩ S χ`. By `subset_of_finite_closed_cover`, `Γ ⊆ S χ`, so `Γ` stabilizes `W`.
4. Let `r` be the restriction of `ρ` to `Γ` acting on `W`. Each `a ∈ N` acts on `W` as
   the scalar `χ a`. The determinant of `r` is a homomorphism to `kˣ` and so kills
   commutators. Hence `χ a ^ dim W = 1` for `a ∈ N`.
5. `N` is connected. It is covered by the finitely many closed sets
   `{g | ρ g v = ζ • v}`, `ζ` a `dim W`-th root of unity. These are pairwise disjoint
   because `v ≠ 0`, and `1` lies in the one for `ζ = 1`. Thus `χ = 1` on `N`, and `N` acts
   trivially on `W`.
6. Hence `r x * r y = r ⁅x, y⁆ * r y * r x = r y * r x` for `x, y ∈ Γ`. The operators
   `r x` commute, and `exists_common_eigenvector` gives a common eigenvector of `Γ` in `W`.

## Provenance and comparison with the source

This is the rational-point form of J. S. Milne, *Algebraic Groups* (2017),
Theorem 16.30 (Lie–Kolchin), printed pp. 334–335. Source:
`milne-2017-algebraic-groups`. The implemented route is a reorganization of Milne's proof:

- Milne inducts on the dimension of `G`. He uses a smooth connected normal subgroup of
  smaller dimension and a simple representation. Here the induction runs down the
  derived series. The normal subgroup used at each stage is the next derived subgroup,
  and no simple representation is chosen: the argument works in the weight space `W`.
- Milne's step "`G(k)` permutes the finitely many eigenspaces, the stabilizer is closed
  of finite index, so it is everything" corresponds to steps 2–3. The finite closed
  cover replaces the cosets of the stabilizer.
- Milne's step "`N(k)` consists of products of commutators, so `χ^d = 1`, and `N` is
  connected, so `χ = 1`" corresponds to steps 4–5. The topological input is
  `isConnected_derivedSeries` instead of Milne's 6.8.
- Milne finishes with the commutative case 16.14. Here `exists_common_eigenvector`
  plays that role.

All topological statements are about the abstract group `G`, under the closedness
hypothesis `hR` and the separate continuity hypotheses. Their verification for rational
points of a group scheme is in `Langlands.GroupScheme.Absolute.LieKolchinRationalTriangularization`.
