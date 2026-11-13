# Proof of Renard VI.4.5, Corollary: the inertia block M(G)[π] is indecomposable

Author: Worker 5104.

`Langlands.CuspidalSupport.rationalInertiaBlockIndecomposable` proves the published
`Langlands.CuspidalSupport.RationalInertiaBlockIndecomposableStatement.{uF, uV}`,
with both universes arbitrary. Its type is exactly that proposition; the
statement's Lean/Markdown pair and its imports are unchanged. Source: David
Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, VI.4.5, Corollary, printed p.160 / PDF p.166 (registered source
`renard-2026-representations-groupes-reductifs-padiques`).

The proof uses two supporting modules of the same contribution:

- `Langlands.Representation.Induction.OpenNormalRestrictionSemisimple`
  (semisimplicity of the restriction of a compact induction to an open normal
  subgroup, and nonzero restricted maps from its subquotients);
- `Langlands.Representation.CuspidalSupport.RationalSummandInductionMembership`
  (`rationalSummandInduction_mem_block`: the compact induction
  `Π = c-Ind_{⁰G}^{G(F)} ρ` of an irreducible summand `ρ ↪ π|_{⁰G}` lies in the
  inertia block of `π`).

It does not use the VI.4.1 equivalence or the description of the center of the
block.

Write `H = G(F)` with its canonical topology, `H⁰ = rationalCommonNormKernel G`
(Renard's `⁰G`) and `B = RationalInertiaBlock G (rationalInertiaBaseLift G π)`.
Morphisms in `B` are those of the ambient smooth category, and an element `c` of
Mathlib's `CatCenter B` is a natural endomorphism of the identity functor, with
components `c.app X : X ⟶ X`.

## Lemma: a central element vanishing on Π

`isZero_of_catCenter_app_eq_id G hG π hπ ρ hρ j hj hmem c hc0 X hcX`. Let `π` be
irreducible, `ρ` an irreducible smooth representation of `H⁰` with an injective
`H⁰`-intertwiner `j : ρ → π|_{H⁰}`, and `hmem` the membership of `Π` in `B`. Let
`c` be a central element of `B` whose component at `Π` is zero (`hc0`: it sends
every vector to `0`), and `X` an object of `B` with `c.app X = 𝟙 X`. Then `X` is a
zero object.

Proof, by contradiction. If `X` were not zero, its carrier would be nontrivial:
otherwise `SmoothRep.isZero_iff_subsingleton` makes `X` zero in the ambient
category, and `IsZero.of_full_of_faithful_of_isZero` for the fully faithful
inclusion of `B` makes it zero in `B`. The published
`SmoothRep.exists_isIrreducible_isSubquotient_of_nontrivial` then gives an
irreducible subquotient `σ` of `X`, presented by `SmoothRep.isSubquotient_iff_exists`
as an injective `i : B₀ → X` and a surjective `q : B₀ → σ`. Since `B₀` and `σ` are
subquotients of `X`, both lie in `B` (`rationalInertiaBlockProperty_of_isSubquotient`),
and `i`, `q` are morphisms of `B`.

1. `c` is the identity on `σ`. Naturality of `c` along `i` and `c.app X = 𝟙 X`
   give `i ∘ c_{B₀} = i`; since `i` is injective, `c_{B₀}` is the identity.
   Naturality along `q` and surjectivity of `q` then give that `c_σ` is the
   identity.
2. A nonzero map `Π → σ`. Because `X` is in `B`, the irreducible subquotient `σ`
   is inertia-related to the lift of `π`: `σ ≅ π ⊗ χ` for an unramified `χ`. The
   published Renard VI.3.2(iii), `rationalNormKernelTwistEquivalence` (first
   part), turns this into an equivalence `ψ` of the restrictions to `H⁰` of the
   lift of `π` and of `σ`. The composite `φ = ψ ∘ e ∘ j : ρ → σ|_{H⁰}`, where `e` is
   the universe-lift equivalence (`Induction.restrictAlongEquiv` of
   `SmoothRep.universeLiftEquiv π`), is injective. Frobenius reciprocity for the
   open subgroup `H⁰` (the published `Induction.cosetSum`) gives a `G`-intertwiner
   `f = cosetSum φ : Π → σ`, and `cosetSum_comp_unitMap` gives
   `f (unit v) = φ v` for the unit `unit = Induction.unitMap` of the adjunction.
3. Contradiction. Pick `v ≠ 0` in `ρ` (an irreducible representation is
   nontrivial, `IsSimpleModule.nontrivial`). Naturality of `c` along `f` gives
   `c_σ (f (unit v)) = f (c_Π (unit v))`. The left side is `f (unit v) = φ v` by
   step 1; the right side is `f 0 = 0` by `hc0`. So `φ v = 0`, contradicting the
   injectivity of `φ`.

## Main proof

After the premises are introduced, the proof recreates the instances fixed by
the statement (affine structure map, affineness of `G.X.left`, smoothness, the
canonical topology and the published topological-group instance).

1. The published Renard VI.3.2(i), `rationalNormKernelOrbit` (first part), gives
   an irreducible `H⁰`-subrepresentation `W` of `π|_{H⁰}`. Let
   `ρ = restrictionSummand H⁰ π W`, irreducible by
   `restrictionSummand_isIrreducible`, with the injective inclusion
   `restrictionSummandι` into `π|_{H⁰}`.
2. `rationalSummandInduction_mem_block` puts `Π = c-Ind_{H⁰}^H ρ` in `B`; call this
   object `Q`.
3. The published Renard VI.4.3, Corollary (i), `rationalNormKernelEnd_isDomain`,
   makes `End Q.obj = End Π` a domain.
4. For the decomposition `P` of `B`, the published `Renard.decompositionIdem hP`
   is a central element `z` of `B` that is the identity on objects of `P true`
   (`decompositionIdem_app_of_true`) and zero on objects of `P false`
   (`decompositionIdem_app_of_false`), and it is idempotent
   (`decompositionIdem_isIdempotentElem`). Its component `z_Π ∈ End Π` is
   therefore an idempotent of a domain, so `z_Π = 0` or `z_Π = 1`
   (`IsIdempotentElem.iff_eq_zero_or_one`).
5. If `z_Π = 0`, take `b = true`: every object `X` of `P true` has `z_X = 𝟙 X`, so
   the lemma applied to `c = z` makes `X` zero.
6. If `z_Π = 1`, take `b = false` and `c = 1 - z`. By `CatCenter.app_sub`, its
   component at `Π` is `1 - z_Π = 0`, and at every object `X` of `P false` it is
   `𝟙 X - 0 = 𝟙 X`. The lemma makes `X` zero.

## Relation to the source

Renard deduces the Corollary from the isomorphism of the center of `M(G)[π]` with
the center of `End Π`, which rests on the VI.4.1 equivalence, and from the fact
that this ring is a domain (VI.4.3): an idempotent of the center is 0 or 1. The
Lean proof keeps the idea of the idempotent `z`, but it only evaluates `z` at `Π`
and replaces the isomorphism of centers by the lemma above, which needs Frobenius
reciprocity, VI.3.2(i) and (iii), and the membership of `Π` in the block.

The proof uses neither the cuspidality of `π` nor the torus, cocharacter,
root-system, closedness, local-compactness, nonarchimedean or Hausdorff premises
of the statement; they are introduced and left unused. No premise is added.
