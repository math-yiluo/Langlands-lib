# The rational-side contradiction

Module `Langlands.GroupScheme.Reductive.RadicalFieldExtension.RationalSide`.

This module proves `RationalSideStatement` from the interface module `RationalSideInterface`.
It is an internal step in the proof of
`Langlands.GroupScheme.AlgebraicallyClosedRadicalFieldExtensionStatement`. It contains no new
definitions or statements from the literature. The auxiliary lemmas below are derived facts
used only by this proof.

## Results

- `pow_card_eq_zero_of_isNilpotent`: a nilpotent square matrix `A` over a field, indexed by a
  finite type `N`, satisfies `A ^ card N = 0`.
- `evaluation_eq_zero_of_mem_rationalPointClosure`: a global function on a group scheme over
  a field `k` that vanishes at every rational point of a set `S` also vanishes at every
  rational point of `rationalPointClosure G S`. These are the rational points located in the
  closure of the locations of `S`.
- `isNilpotent_of_mem_pointClosureSubgroup`: let `ρ` be a matrix representation, and suppose
  `ρ(g) - 1` is nilpotent for every `g` in a subgroup `Γ` of rational points. Then `ρ(x) - 1`
  is nilpotent for every `x ∈ pointClosureSubgroup G Γ`.
- `exists_lift_of_rationalPoints`: over an algebraically closed field `k`, let `P` be reduced
  and locally of finite type, let `i : Y ⟶ X` be a closed immersion and let `f : P ⟶ X`. If
  every rational point of `P` maps under `f` into the image of `i`, then `f` factors through
  `i`.
- `isNormal_range_of_rationalPointClosure`: let `G` and `Z` be smooth over an algebraically
  closed field. Let `ζ : Z ⟶ G` be a closed subgroup whose underlying set is the closure of
  the locations of a normal subgroup `Γ` of `G(k)`. Then `range ζ` is a normal subgroup
  functor of `G`.
- `isNormal_range_identityComponentι_comp`: let `Z` be smooth and affine and let `ζ : Z ⟶ G`
  be a closed subgroup with normal range. Then the identity component of `Z`, embedded in
  `G` by `identityComponentι Z ≫ ζ`, also has normal range.
- `rationalSide : RationalSideStatement`.

## Proof

**The auxiliary lemmas.**

- `pow_card_eq_zero_of_isNilpotent`: the characteristic polynomial of a nilpotent matrix is
  `X ^ card N` (`Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent`). Then Cayley–Hamilton
  (`Matrix.aeval_self_charpoly`) applies.
- `evaluation_eq_zero_of_mem_rationalPointClosure`: the `RationalZariski.topology` on rational
  points is induced by `location`. So a point of `rationalPointClosure G S` lies in the closure
  of `S` in that topology. The zero set of a function is closed there
  (`RationalZariski.isClosed_evaluation_eq_zero`).
- `isNilpotent_of_mem_pointClosureSubgroup`: let `M` be the matrix of global functions given
  by the entries of `ρ`. Evaluation at a rational point `y` sends `(M - 1) ^ card N` to
  `(ρ(y) - 1) ^ card N`. For `g ∈ Γ` this is zero by the first lemma. So every entry of
  `(M - 1) ^ card N` vanishes on `Γ`, hence on the point closure by the second lemma.
- `exists_lift_of_rationalPoints`: `P` is a Jacobson space
  (`LocallyOfFiniteType.jacobsonSpace`). Over an algebraically closed field, every closed point
  of `P` comes from a rational point (`pointOfClosedPoint`). So the closed set
  `f⁻¹(range i)` contains all closed points, and hence equals `P`. Then
  `FiniteIndexTransfer.exists_lift_of_range_subset` gives the factorization, since `P` is
  reduced and `i` is a closed immersion.
- `isNormal_range_of_rationalPointClosure`: `G × Z` is smooth over `k`, so it is reduced
  (`SmoothReducedProof.isReduced_of_smooth_over_field`). Consider the scheme-theoretic
  conjugation `SubgroupFunctor.conjugationMap ζ (𝟙 G) : G × Z → G`. At a rational point
  `(g, z)` its value is `g · ζ(z) · g⁻¹`. Conjugation by the constant point `g` is a morphism
  `G ⟶ G` that maps `Γ` into `Γ`, because `Γ` is normal. By
  `comp_mem_rationalPointClosure` it then maps the point closure of `Γ` into itself. Hence the
  conjugation map sends every rational point into the image of `ζ`, and by
  `exists_lift_of_rationalPoints` it factors through `ζ`. By
  `SubgroupFunctor.isNormalizedBy_range_iff_exists_conjugationMap`, `range ζ` is normalized by
  all of `G`.
- `isNormal_range_identityComponentι_comp`: normality of `range ζ` gives an automorphic action
  of `G` on `Z` by conjugation (`AutomorphicAction.ofNormalizedConjugation`). It restricts to
  the identity component (`AutomorphicAction.onIdentityComponent`). Then
  `AutomorphicAction.onIdentityComponent_act_comp` and
  `SubgroupFunctor.lift_comp_normalizedConjugation_comp` identify the restricted action with
  conjugation in `G`.

**The main theorem.** Let `Z` with `ζ : Z ⟶ G` be the smooth closed subgroup on the closure of
the locations of `Γ` (`rationalPointClosureSubgroup`). Let `Z⁰` be its identity component and
`j = identityComponentι Z ≫ ζ`. Then `j` is a closed immersion, so a closed subgroup. `Z⁰` is
smooth and connected. Every rational point of `Z⁰` maps under `j` into
`pointClosureSubgroup G Γ`.

1. *Unipotence.* The point closure of `Γ` is solvable (`isSolvable_pointClosureSubgroup`).
   `j` is injective on rational points, so the rational points of `Z⁰` form a solvable group.
   `ρ.restrict j` is a closed immersion. By `isNilpotent_of_mem_pointClosureSubgroup`, every
   rational point of `Z⁰` acts unipotently through it. So
   `isUnipotent_of_isNilpotent_rationalMatrix` (module `Unipotence`) gives that `Z⁰` is
   unipotent.
2. *Normality.* Combine `isNormal_range_of_rationalPointClosure` with
   `isNormal_range_identityComponentι_comp`.
3. *Triviality.* `HasTrivialUnipotentRadical G` applied to `j` gives `range j = ⊥`. Evaluated
   on the universal point of `Z⁰`, this says `j = 1` as a morphism of schemes.
4. *The generic point of `V(𝔭)`.* Let `ξ ∈ G` be the point that `Spec Γ(G, 𝒪)` sends to `𝔭`
   (`G` is affine). The points that `ξ` specializes to are those whose prime contains `𝔭`.
   The prime of a rational point `x` is the kernel of evaluation at `x`
   (`BorelFieldExtension.toSpecΓ_asIdeal_of_field`). So every closed point of
   `closure {ξ}` is a rational point that kills `𝔭`. By hypothesis it lies in `Γ`, and so in
   the image of `ζ`. Since `G` is Jacobson (`closure_inter_closedPoints`), `ξ` itself lies in
   the image of `ζ`, say `ξ = ζ(ξ')`. This step follows step 1 of
   `BorelFieldExtensionKSide`.
5. *`ξ` lies on `Z⁰`.* `𝔭` is contained in the augmentation ideal, so `ξ` specializes to the
   identity point of `G`. `ζ` is an embedding sending the identity to the identity, so `ξ'`
   specializes to the identity point of `Z`. Its identity component is open
   (`IdentityComponent.isClopen_identitySet`), so `ξ'` lies in it, and `ξ = j(w)` for some
   `w`.
6. *Contradiction.* Since `j = 1`, `ξ = j(w)` is the identity point of `G`. Its prime is the
   augmentation ideal, so `𝔭` equals the augmentation ideal. This contradicts the strict
   inclusion.
