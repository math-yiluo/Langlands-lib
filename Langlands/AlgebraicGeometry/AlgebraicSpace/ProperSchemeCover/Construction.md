# The weak Chow construction

This module builds the scheme `U` and the surjective morphism `φ : h_U → X` of the weak
Chow lemma for a separated algebraic space (Stacks Project, Tag 089I, adapted to a
single fibre power with padded tuples). Represented properness of `φ` is proved in the
later modules `Closedness` and `RelativeProper`.

## Auxiliary lemmas

- `exists_glue_hom_le`: morphisms `h_{U_i} → X` on the members of an open cover of an
  open `V` of a scheme `T` over `S`, agreeing on the pairwise intersections, glue to a
  morphism `h_V → X`. This is `OpenGluing.exists_glue_le` (Zariski sheaf condition of
  the fppf sheaf `X`) transported along the Yoneda bijection `uliftYonedaEquiv`.
- `exists_lift_openImmersion`: a morphism over `S` whose range lies in the range of an
  open immersion `o` factors through `o`.
- `dense_range_of_comp_openOverι`: if `e` has dense range in `T` and factors through
  an open `V`, the factorization has dense range in `V`.
- `exists_lift_of_dense`: let `T` be reduced, `j : A ⟶ B` a closed immersion and
  `f : T ⟶ B`. If `e ≫ f` factors through `j` for some `e` with dense range, then `f`
  factors through `j`. Proof: the preimage of the closed range of `j` contains the
  dense range of `e`, so it is everything, and
  `ReducedClosedSubspace.exists_lift_isClosedImmersion_over` applies.
- Instances: `(openOverι T V).left` is an open immersion, and an open subscheme of a
  reduced scheme is reduced.

## Input data

`ChowData X` packages, for an algebraic space `X` over `S`:

- `X` separated;
- an étale surjective chart `π : h_W → X` with `W → S` quasi-compact;
- a fibre power `P` of `W` over `X` with `n + 1` factors such that every point of `W`
  is the first coordinate of a point of the complete locus `completeLocus` (module
  `CompleteTuples`);
- a scheme `Y` separated over `S`, an open immersion `o : O ⟶ Y` with `O`
  quasi-compact, and a closed immersion `ι : W ⟶ O`;
- a scheme `M` proper over `S` with morphisms `p i : M ⟶ Y` and `ε : P ⟶ M` such that
  `ε ≫ p i = pr i ≫ ι ≫ o` for all `i`.

In the application `Y` is projective space, `O` a standard affine open, and `M` the
product of `n + 1` copies of `Y`, with projections `p i`.

## The construction

Write `G` for the complete locus of `P`.

- `Z`: the reduced closed subscheme of `M` on the closure of `ε(G)`, with closed
  immersion `ζ : Z ⟶ M`. `Z` is reduced and proper over `S`.
- `Gbar`: the reduced closed subscheme of `P` on the closure of `G`, with closed
  immersion `gbar`, and `εbar : Gbar ⟶ Z` with `εbar ≫ ζ = gbar ≫ ε`
  (`ReducedClosedSubspace.exists_lift_reducedOver`).
- `A := ζ⁻¹(ε(G))` is dense in `Z` (`dense_A`), and `A ⊆ εbar(gbar⁻¹(G))`
  (`A_subset`). Hence `εbar` has dense range.
- `opens i := (ζ ≫ p i)⁻¹(O)`, an open of `Z` containing the range of `εbar`.
- `fac i : opens i ⟶ W` with `fac i ≫ ι ≫ o = (opens i ↪ Z) ≫ ζ ≫ p i`
  (`fac_spec`). Proof: `ζ ≫ p i` restricted to `opens i` factors through `O`; this
  factorization composed with the dense-range lift of `εbar` factors through the
  closed immersion `ι` (it equals `gbar ≫ pr i ≫ ι`), so `exists_lift_of_dense`
  applies. `comp_fac_eq` and `comp_fac_eq_of_εbar` characterize composites with
  `fac i` (`ι ≫ o` is a monomorphism).
- `fac_agree`: on `opens i ⊓ opens j` the composites `π ∘ fac i` and `π ∘ fac j` agree.
  Proof: since `X` is separated, the pairing `W ×_X W ⟶ W ×_S W` is a closed immersion
  (`isClosedImmersion_spacePullbackLift`). The pair `(fac i, fac j)` on the reduced
  scheme `opens i ⊓ opens j` factors through it after composition with the
  dense-range lift of `εbar`, where it becomes `(gbar ≫ pr i, gbar ≫ pr j)`, a pair
  with equal images in `X`. By `exists_lift_of_dense` it factors through `W ×_X W`, so
  its two components have equal images in `X`.
- `X' := ⨆ i, opens i` and `U := X'` as a scheme over `S`.
- `φ : h_U → X`: glued from the `π ∘ fac i` by `exists_glue_hom_le`. `φ_spec` states
  that `φ` restricts to `π ∘ fac i` on `opens i`.
- `εU : Gbar ⟶ U`, the factorization of `εbar`, satisfies
  `h(εU) ≫ φ = h(gbar ≫ pr 0) ≫ π` (`εU_φ`).

## Results

- `isSurjective_φ`: `φ` is surjective. Proof: by `isSurjective_of_isPullback` (the
  chart `π` is surjective) it suffices that the projection `U ×_X W → W` is surjective.
  A point `w` of `W` is `pr 0 (t)` for a complete point `t = gbar(x)`. The pair
  `(εU, gbar ≫ pr 0)` lifts to `U ×_X W` by `εU_φ`, and the image of `x` maps to `w`.
- `U_hom`: `U → S` is `X'.ι ≫ ζ ≫ (M → S)`. Hence `U → S` is locally of finite type
  and separated (instances): an open immersion followed by a closed immersion
  followed by a proper morphism.
