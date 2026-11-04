# Reduction of the infinite-field envelope compatibility

Worker 1523. This module proves a conditional theorem. It does not prove any of
the three statements it assumes.

## Main theorem

`torusGeneratedEnvelopeAlgebraicClosureInfinite_of` takes three Library
propositions as explicit hypotheses:

- `hbc : MaximalTorusBaseChangeStatement.{u}`: a closed torus is maximal exactly
  when its base change to a field extension is maximal (Milne, Theorem 17.82);
- `hconj : MaximalTorusConjugacyStatement.{u}`: over an algebraically closed
  field, two maximal tori of a smooth connected affine group are conjugate by a
  rational point (Milne, Theorem 17.10);
- `hdense : RationalMaximalTorusConjugateDensityStatement.{u}`: over an infinite
  field `k`, the points of `G_k̄` that conjugate `(T₀)_k̄` onto the base change of
  a closed `k`-torus are Zariski-dense, where `T₀` is a maximal `k`-torus.

It concludes `TorusGeneratedEnvelopeAlgebraicClosureInfiniteStatement.{u}`. That
is, for every infinite field `k` and every smooth affine `G` over `Spec k` with
connected underlying space,
`(closedTorusEnvelope G).baseChange (toAlgebraicClosure k) =
closedTorusEnvelope G_k̄` as subgroup functors.

## Proof

Write `K = AlgebraicClosure k`, `F` for base change along
`toAlgebraicClosure k`, and `G_K = F.obj G`.

1. **Criterion.** By `closedTorusEnvelope_baseChange_eq_iff_containsTori`, the
   equality holds once the left side contains every closed `K`-torus of `G_K`.
   Let `D = smoothTorusGeneratedEnvelope G`. By `range_baseChangeHom`, the left
   side is the range of the closed subgroup `inc = F.map D.inclusion` of `G_K`.
   `G_K` is again smooth, affine, and connected
   (`connectedSpace_baseChange_of_smooth_affine`).
2. **Ground-field tori.** For every closed `k`-torus `j : T ⟶ G`, the range of
   `F.map j` lies in the range of `inc`. The reason is that `range j` lies in the
   envelope, and base change of subgroup functors is monotone.
3. **A maximal `k`-torus.** `TorusExistence.exists_isMaximalTorus` gives a
   maximal torus `j₀ : T₀ ⟶ G`. By `hbc`, `F.map j₀` is a maximal torus of `G_K`.
4. **Conjugates of `(T₀)_K` lie in `D_K`.** Fix a `K`-point `g` of `G_K`.
   `(T₀)_K` is a torus, hence smooth (`IsTorus.smooth`) and reduced. So
   `SubgroupFunctor.range_le_of_algClosed_points` reduces the inclusion
   `range (F.map j₀ ≫ int(g)) ≤ range inc` to `K`-points. Fix a `K`-point `t` of
   `(T₀)_K` with image `s` in `G_K`.
   - `conjByPoint G_K s : G_K.X ⟶ G_K.X` is the morphism `x ↦ x s x⁻¹`, defined
     in the group of endomorphisms of `G_K.X` as `𝟙 * (constant s) * 𝟙⁻¹`. By
     `comp_conjByPoint_base`, its value at a base point `g'` is `s` moved by the
     inner automorphism of `g'`.
   - The preimage `Z` of the closed set `range inc` under `conjByPoint G_K s` is
     closed in the underlying space of `G_K`.
   - Let `g'` be a point counted by `hdense`, with
     `range (F.map j₀ ≫ int(g')) = range (F.map j)` for a closed `k`-torus `j`.
     Then `g' s g'⁻¹` lies in `range (F.map j)`, so by step 2 it lies in
     `range inc`. Hence the image point of `g'` lies in `Z`.
   - By `hdense`, these image points form a dense set, so the closed set `Z` is
     everything. In particular, the single image point of `g s g⁻¹` lies in the
     image of `inc`.
   - `mem_range_of_range_subset` turns this topological containment into
     factorization. Pull the closed immersion back along the point
     `Spec K ⟶ G_K`. This gives a closed immersion into `Spec K` that is
     surjective. `Spec K` is reduced, so it is an isomorphism
     (`isIso_of_isClosedImmersion_of_surjective`), and its inverse supplies the
     factorization.
5. **All `K`-tori.** Let `i : S ⟶ G_K` be a closed `K`-torus.
   `exists_isMaximalTorus_factor` factors `i` as `f ≫ i'` with `i'` a maximal
   torus. By `hconj` there are `g` and `φ` with
   `F.map j₀ ≫ int(g) = φ ≫ i'`. Hence
   `range i ≤ range i' ≤ range (φ ≫ i') = range (F.map j₀ ≫ int(g)) ≤ range inc`
   by step 4.

## Supporting lemmas (namespace `EnvelopeInfiniteReduction`)

- `IsClosedTorusRankAbove G i₀ n` says the following: some closed subgroup of `G`
  through which `i₀` factors becomes isomorphic to `𝔾_m^I` over some extension
  field, with `Nat.card I = n`.
- `exists_isMaximalTorus_factor`: in a smooth affine group over a field, every
  closed torus factors through a maximal torus. The proof reruns
  `TorusExistence.exists_isMaximalTorus` with the extra factorization
  requirement. Ranks are bounded by the Lie kernel dimension
  (`TorusExistence.card_le_finrank`), and the proof takes the greatest attained
  rank (`Nat.findGreatest`). A factorization through a torus of no larger rank is
  an isomorphism (`splitTorus.isIso_of_mono_of_iso` over a common splitting
  field, then `TorusExistence.isIso_of_isIso_baseChange`).
- `mem_range_of_range_subset`: over a field, a base point whose image lies in the
  image of a closed subgroup is a point of that subgroup.
- `conjByPoint`, `comp_conjByPoint`, `comp_conjByPoint_base`: conjugation of a
  fixed base point by the universal point, and its values on points.

## Provenance

The route follows the infinite-field argument in Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition, proof of Proposition A.2.11, printed
p.478. There the universal maximal torus over `Tor_G` is shown to map into `G_t`
because `Tor_G(k)` is dense. Here the density is used on `G_k̄`, in the form of
`RationalMaximalTorusConjugateDensityStatement`, and conjugacy over `k̄` replaces
the universal torus. The Lean proof is an internal formalization from published
Library results together with the three explicit hypotheses.
