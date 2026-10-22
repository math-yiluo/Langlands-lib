# Shapiro's lemma through restriction and evaluation

Let `G` be a group, `S ≤ G` a subgroup, `k` a commutative ring, and `A` a
`k`-linear representation of `S`. All of `k`, `G` and the representations
live in one universe `Type u`. Mathlib's coinduced representation
`Rep.coind S.subtype A` (written `Coind_S^G A` below) consists of the
functions `f : G → A` with `f (s * x) = s • f x` for `s ∈ S`. The group `G`
acts by `(g • f) x = f (x * g)`. Serre's `B*` and Milne's `Ind_H^G` are the
same module.

This module proves that restricting cochains to `S` and evaluating the
coefficients at the identity gives an isomorphism
`Hⁿ(G, Coind_S^G A) ≅ Hⁿ(S, A)` in every degree `n`. Mathlib already has an
isomorphism `groupCohomology.coindIso`. Mathlib builds it from projective
resolutions and the restriction–coinduction adjunction, and it does not say
what the map does on cochains. Later work on semilocal idele cohomology needs
the explicit map, so this module proves that the explicit map is an
isomorphism. All declarations are in the namespace `Langlands.Shapiro`.

## The map

- `coindEval A : Res_S (Coind_S^G A) ⟶ A` is evaluation at the identity,
  `f ↦ f 1`. It is `S`-equivariant: `f (1 * s) = f (s * 1) = s • f 1`.
  `coindEval_hom_apply` is the formula.
- `shapiroMap A n : Hⁿ(G, Coind_S^G A) ⟶ Hⁿ(S, A)` is Mathlib's
  `groupCohomology.map S.subtype (coindEval A) n`. It is induced by the cochain
  map `φ ↦ (s₁, …, sₙ) ↦ φ(s₁, …, sₙ)(1)`.
- `cochainsMap_coindEval_naturality` (true by `rfl`) and
  `shapiroMap_naturality` say this is natural in `A`. For `φ : A ⟶ B`, first
  apply `Coind(φ)` over `G` and then the Shapiro map of `B`. This equals the
  Shapiro map of `A` followed by `φ` over `S`.

## Degree zero

`coindInvariantsEquiv A` is a `k`-linear equivalence between the
`G`-invariants of `Coind_S^G A` and the `S`-invariants of `A`. A `G`-invariant
function satisfies `f x = f (1 * x) = (x • f) 1 = f 1`, so it is constant. A
constant function `x ↦ a` lies in `Coind_S^G A` exactly when `s • a = a` for
all `s ∈ S`. The equivalence sends `f` to `f 1`.

`shapiroMap_zero_comp_H0Iso` identifies `shapiroMap A 0` with this
equivalence through Mathlib's `H0Iso`. Hence `isIso_shapiroMap_zero` holds.

## Coinduction is exact, and acyclic inputs stay acyclic

- `coind_shortExact`: applying `Rep.coindFunctor k S.subtype` to a short
  exact sequence of `S`-representations gives a short exact sequence of
  `G`-representations. Coinduction is a right adjoint, so it preserves the
  kernel of the second map and monomorphisms. Mathlib also shows that it
  preserves epimorphisms.
- `isZero_coinduced A n`: the Library's coinduced module
  `Langlands.Tate.coinduced A` (coinduction from the trivial subgroup) has
  zero cohomology in degree `n + 1`. This uses Mathlib's `coindIso` together
  with the vanishing of positive-degree cohomology of the trivial group.
- `isZero_coind_of_isZero`: if `Hⁿ(S, B) = 0` then
  `Hⁿ(G, Coind_S^G B) = 0`. This also uses Mathlib's `coindIso`. That abstract
  isomorphism is used only for these two vanishing statements.

## Compatibility with connecting maps

`shapiroCochainsSequenceMap X` is the map of short complexes of cochain
complexes from the cochains of the coinduced sequence of `X` (over `G`) to
the cochains of `X` (over `S`). Its three components are the cochain-level
Shapiro maps. `shapiroMap_δ` says that for a short exact `X`, the connecting
maps of the two long exact sequences commute with the Shapiro maps:
`δ_G ≫ shapiroMap X₁ (n + 1) = shapiroMap X₃ n ≫ δ_S`. The proof is Mathlib's
`HomologicalComplex.HomologySequence.δ_naturality`, applied to this map of
short exact sequences of complexes.

## The isomorphism in all degrees

`isIso_shapiroMap A n` is proved by induction on `n`, for all `A` at once,
by dimension shifting. Let `0 → A → C → Q → 0` be the Library's short exact
sequence `Langlands.Tate.shiftUpSequence A`, where `C` is
`Langlands.Tate.coinduced A`. Its coinduction to `G` is short exact. In
degree `n + 1` the cohomology of `C` vanishes over `S`, and so does the
cohomology of `Coind_S^G C` over `G`. So both connecting maps
`H^n(Q) → H^{n+1}(A)` are surjective.

- Surjectivity: `δ_G ≫ shapiroMap A (n + 1)` equals
  `shapiroMap Q n ≫ δ_S`. The right-hand side is surjective, since
  `shapiroMap Q n` is an isomorphism by induction. So `shapiroMap A (n + 1)`
  is surjective.
- Injectivity: suppose `x ∈ H^{n+1}(G, Coind A)` maps to `0`. Write
  `x = δ_G y`. Then `δ_S (shapiroMap Q n y) = 0`. By exactness over `S`,
  `shapiroMap Q n y` is the image of some `z ∈ Hⁿ(S, C)`. By induction
  `z = shapiroMap C n z'`. Naturality and injectivity of `shapiroMap Q n`
  show that `y` is the image of `z'` under `Coind(C → Q)`. Then
  `x = δ_G y = 0` by exactness of the long exact sequence over `G`.

`shapiroIso A n` is the resulting isomorphism, and `shapiroIso_hom` says its
forward map is `shapiroMap A n`.

## Sources

The explicit form of the map is the one in Serre's exercise and in Milne's
example below. Serre suggests the same dimension-shifting proof. Milne
proves Shapiro's lemma with injective resolutions and then checks that the
explicit map agrees in degree `0`, extending to all degrees by dimension
shifting. The Lean statements are general group-cohomology facts. The
specific packaging is internal: Mathlib representations, the Library's
coinduced shift sequence, and Mathlib's `coindIso` used only for vanishing.

- Jean-Pierre Serre, *Local Fields*, GTM 67, Chapter VII §5, the exercise
  at the end of the section, printed pp. 116–117 (PDF pp. 122–123). Let `B*`
  be the maps `φ : G → B` with `φ(hs) = hφ(s)`, with `(sφ)(g) = φ(gs)` and
  `θ(φ) = φ(1)`. Then `θ` is compatible with `H → G` and induces
  isomorphisms `H^q(G, B*) → H^q(H, B)`. The suggested proof uses the
  co-induced case and the fact that `H^q(G, B*)` is a cohomological functor
  of `B`.
- J. S. Milne, *Class Field Theory* v4.03, Chapter II, Proposition 1.11
  (Shapiro's lemma), printed p. 62 (PDF p. 71), and Example 1.27(a), printed
  pp. 68–69 (PDF pp. 77–78). The map `φ ↦ φ(1_G)` is compatible with
  `H ↪ G`, and the induced map `Hʳ(G, Ind_H^G M) → Hʳ(H, M)` is the Shapiro
  isomorphism.
