# No specializations between points with the same image

Author: Worker 1038.

Module `Langlands.AlgebraicGeometry.AlgebraicSpace.SameImageSpecialization`, namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace`.

## Results

- `eq_of_specializes_tower` (pure topology). Let `t, s : R → V` be maps of topological spaces,
  with `V` a T0 space. Assume:
  - generalizations lift along `t` (`GeneralizingMap t`);
  - `s` is continuous;
  - `s` has no nontrivial specializations inside its fibres;
  - `K ⊆ V` is finite and `t r ∈ K` implies `s r ∈ K`.

  If `t r₀ ∈ K` and `s r₀ ⤳ t r₀`, then `s r₀ = t r₀`.

  Proof: the tower argument of Stacks Project, Decent Algebraic Spaces, Lemma 68.7.1
  (Tag 03IM). Repeatedly lifting the generization `s r ⤳ t r` along `t` gives points `r_n` and
  a chain `w_{n+1} ⤳ w_n` in `K`, where `w_n = t r_n`. If two consecutive terms agreed, the
  fibre condition on `s` would make the previous terms agree, back down to
  `s r₀ = t r₀`. Otherwise all specializations are strict and T0 makes the `w_n` pairwise
  distinct, which contradicts the finiteness of `K`.
- `eq_of_specializes_of_isDiscrete`: a map whose fibres are discrete subsets has no nontrivial
  specializations inside fibres. `eq_of_specializes_of_locallyQuasiFinite` applies this to a
  locally quasi-finite morphism of schemes (Mathlib's `Scheme.Hom.isDiscrete_preimage_singleton`).
- `SameImage.eq_of_specializes_of_etale`. Let `a : h_V ⟶ Y` be étale, and let `K` be a finite
  set containing `v` and closed under `SameImage a`. If `SameImage a v v'` and `v' ⤳ v`, then
  `v' = v`. The tower lemma is applied to the projections `t = snd` and `s = fst'` of the
  represented pullback `V ×_Y V`:
  - both projections are étale (`IsEtale.projection`);
  - `t` is generalizing (`Flat.generalizingMap`);
  - `s` is locally quasi-finite (`locallyQuasiFinite_of_etale`).
- `SameImage.finite_of_cover`. Suppose `f : h_U ⟶ Y` is finite and surjective (`IsFinite`,
  `IsSurjective`) with `U` quasi-compact and quasi-separated, and `a : h_V ⟶ Y` is étale with
  `V` quasi-compact. Then every `SameImage a`-class in `V` is finite. It lies in the image,
  under `U ×_Y V ⟶ V`, of a fibre of the étale quasi-compact morphism `U ×_Y V ⟶ U`.
- `SameImage.eq_of_specializes`. Let `X` be a quasi-compact algebraic space, `U` a
  quasi-compact quasi-separated scheme and `f : h_U ⟶ X.presheaf` finite and surjective. If
  `SameImage f x y` and `x ⤳ y`, then `x = y`.

  Proof: take a quasi-compact étale surjective atlas `V` (from `IsQuasiCompact X`).
  1. Lift `y` to `U ×_X V` and lift the generization `x ⤳ y` along the étale projection to `U`.
  2. The two points of `V` below are related and specialize, so they are equal by the
     previous results.
  3. The two lifted points then lie in one fibre of the finite projection to `V`, which has
     no nontrivial specializations.

Provenance: internal. The topological core follows the proof of Stacks Project, Decent
Algebraic Spaces, Lemma 68.7.1 (Tag 03IM), with "the second part of Lemma 68.4.2" replaced by
the finiteness of classes coming from the finite surjective quasi-compact quasi-separated
cover. The Stacks statement assumes conditions on the space; here only the stated
hypotheses are used. The source is the Stacks Project, Decent Algebraic Spaces, version
ed88ff78, printed p. 15.
