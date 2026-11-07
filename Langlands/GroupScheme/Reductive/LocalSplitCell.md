# Root parametrizations and big-cell maps over a ring

Module `Langlands.GroupScheme.Reductive.LocalSplitCell`.

This module fixes the vocabulary for the open cell of a split reductive group over a ring
and states two inputs to the Isomorphism Theorem over a reduced local ring. It proves only
small naturality lemmas, no theorems about reductive groups.

Throughout, `R` is a commutative ring, `G` a group scheme over `Spec R`,
`i : splitTorus (Spec R) I ⟶ G` a homomorphism from the coordinate split torus `𝔾ₘ^I`, and
the character lattice of `𝔾ₘ^I` is `I → ℤ`.

## Definitions

- `LocalSplitCell.Ga R` is the additive group `𝔾ₐ` over `Spec R`, as the Library's
  `VectorGroup.groupScheme (CommRingCat.of R) 1`.
- `rootPoint u Z c` is the point `u(c) : Z ⟶ G` for `u : 𝔾ₐ ⟶ G` and a global function `c`
  on the test scheme `Z`. The lemma `comp_rootPoint` says it is natural in `Z`.
- `IsRootParametrization i m u` says that `u : 𝔾ₐ ⟶ G` parametrizes the root group of the
  character `χ_m` (exponent vector `m : I → ℤ`). It has three fields:
  1. `represents`: `u` represents the Library's relative root subgroup functor
     `RelativeRoot.subgroup i χ_m`. This means `u` is a monomorphism and its points are
     exactly the root-subgroup points on every test scheme.
  2. `isClosedSubgroup`: `u` is a closed immersion.
  3. `equivariant`: `i(t) u(c) i(t)⁻¹ = u(χ_m(t) c)` on every test scheme.

  This is Conrad's `exp_a : W(g_a) → G` of *Reductive group schemes* (2014), Thm. 4.1.4,
  after a trivialization `W(g_a) ≅ 𝔾ₐ` of the root line. Such a trivialization exists, for
  example, when the root line is free; we do not fix it.
- `weylPoint u u'` is the point `u'(-1) u(1) u'(-1)` of `G` over the base. For `u = exp_a`
  and `u' = exp_{-a}` with dual normalizations this is Conrad's `w_{-a}(-1) = w_a(1)`
  (Cor. 5.1.9(4)). In `SL₂` with the standard root groups it is `[[0, 1], [-1, 0]]`.
- `IsWeylPoint i n f` says that the point `n` normalizes the torus. Conjugation by `n` on
  the torus is the torus automorphism `splitTorus.exponentIso f`, which pulls the character
  `χ_m` back to `χ_{f m}`. For a reflection `f = s_a`, this is the action of the Weyl
  element of Conrad's Cor. 5.1.9(1).
- `cellObj R I m n` is the product `𝔾ₐᵐ × 𝔾ₘ^I × 𝔾ₐⁿ` over `Spec R`.
- `orderedProduct u e Z c` is the ordered product `∏ₖ u_{e k}(c k)`, factors in increasing
  order of `k`.
- `cellPoint` evaluates the big-cell formula `(∏ₖ u_{neg k}(vₖ)) · i(t) · (∏ₖ u_{pos k}(wₖ))`
  on points. `negCoord`, `torusCoord` and `posCoord` are the three components of a point of
  `cellObj`.
- `cellMap i u neg pos : cellObj R I m n ⟶ G` is the big-cell map. The lemma `comp_cellMap`
  says that on every point `x` it equals `cellPoint` evaluated at the components of `x`.

## Statements (interfaces)

Both statements have the hypotheses of the Library's
`LocalSplitReducedIsomorphismTheoremStatement` for one group:

- `R` is local and reduced;
- `G` is reductive with affine structure morphism;
- `i` is a closed subgroup, and its base change to every residue field is a maximal torus;
- `P` is a fibrewise root datum for `(G, i)` (`IsFibrewiseRootDatumOf`);
- `b` is a base of `P`.

`LocalSplitRootGroupStatement` asserts that there is a family `u : J → (𝔾ₐ ⟶ G)` such that

- every `u α` is a root parametrization for `P.root α`;
- for every simple root `a ∈ b.support`, the point `weylPoint (u a) (u (-a))` is a Weyl point
  for the reflection `P.reflection a`. Here `-a` is written `P.reflectionPerm a a`.

This combines Conrad Thm. 4.1.4 (root groups over a base) with the normalization of
Cor. 5.1.9: `u_{-a}` is rescaled so that it is dual to `u_a`. The statement asks the
normalization only for simple roots, which is all a pinning uses.

`LocalSplitBigCellStatement` asserts the following. For every family `u` of root
parametrizations (no normalization needed) and all enumerations
`neg : Fin m ≃ {α // ¬ b.IsPos α}` and `pos : Fin n ≃ {α // b.IsPos α}` of the negative and
positive roots, `cellMap i u neg pos` is an open immersion. This is Conrad Thm. 5.1.13 over a
nonempty base, specialized to `Spec R`. There, `U_{-Φ⁺} × T × U_{Φ⁺} → G` is an open
immersion and each `U_{±Φ⁺}` is directly spanned by its root groups in any order.

## Provenance

Source: Brian Conrad, *Reductive group schemes* (SGA3 summer school notes, 2014): Thm. 4.1.4,
Cor. 5.1.9 and Thm. 5.1.13 (PDF pp. 110, 140-141 and 143). Conrad works over any non-empty base
scheme; the statements here specialize to `Spec R` for a local ring `R`. The hypothesis
`[IsReduced R]` is not in Conrad. It is the setting of the reduced Isomorphism Theorem
`LocalSplitReducedIsomorphismTheoremStatement` that these statements feed into, and the
proofs may use it. The hypotheses on `(G, i, P)` are those of that statement.
