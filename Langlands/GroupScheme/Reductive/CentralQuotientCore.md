# The geometric core of the central-quotient theorem

Authors: Worker 1428 (Lean proof and Markdown) and Worker 1499 (Markdown
revision and submission).

This internal helper module of the proof of
`Langlands.GroupScheme.CentralQuotientReductiveStatement` proves the
statement over an algebraically closed field. It is derived content: the
statements are chosen for this proof and are not items of the cited
literature. Everything is in the namespace
`Langlands.GroupScheme.CentralQuotient`. The overall structure follows the
published full-centre core `CenterQuotient.hasTrivialUnipotentRadical_of_isFppfQuotient_center`
(`Adjoint/CenterQuotientCore`). The last step differs: there the kernel is
the full centre, and here it is any subgroup functor `N ≤ center G`.

Notation: `K` is an algebraically closed field and all group schemes are over
`Spec K`. `rationalPoints G` is the group of `K`-points. `center G` is the
Library centre subgroup functor (`Rational/Characters`).

## Finiteness of the central subgroup

- `finite_rationalPoints_of_central_preimage`: let `G` be smooth and affine
  with trivial unipotent radical. Let `a : A ⟶ G` be a monomorphism from an
  affine group `A` locally of finite type, all of whose rational points map
  into `center G`. Let `π : A ⟶ Z` be surjective on rational points, and let
  `z : Z ⟶ U` be a monomorphism into an affine unipotent group `U`. Then `Z`
  has finitely many rational points.

  Proof. Let `M` be the identity component of the reduced subgroup `A_red`
  (Library `reducedSubgroup`, `identityComponentι`), mapped into `G` through
  `A`. It is smooth, affine and connected, and its rational points map into
  the centre, so it is central by Lemma C (`isCentral_of_rationalPoints`).
  Lemma D (`finite_range_of_isCentral`), applied to `M ⟶ A ⟶ Z ⟶ U`, shows
  that the image of `M(K)` in `U(K)` is finite. The image of `M(K)` in `A(K)`
  has finite index (Lemma F, `finiteIndex_map_rationalIdentitySubgroup`). So
  the image of `A(K)` in `U(K)` is finite (`finite_range_of_finite_map`).
  Since `π` is surjective on rational points and `z` is a monomorphism, `Z(K)`
  injects into that image.

  Lemma D is applied with target `U`, not `Z`, because `Z` is not known to be
  unipotent as a group scheme on its own here. All three lemmas are in
  `CentralPreimageTrivial`.

## The core

- `hasTrivialUnipotentRadical_of_isFppfQuotient` (**main result**): let `G`
  be smooth, affine and connected with trivial unipotent radical, and let `Q`
  be affine and locally of finite type. Let `q : G ⟶ Q` and `N` be a subgroup
  functor of `G` with `N ≤ center G` and `RelativeRoot.IsFppfQuotient N q`.
  Then `Q` has trivial unipotent radical.

  Proof. Let `j : U ⟶ Q` be a closed subgroup with `U` smooth, connected and
  unipotent and normal range, and suppose that the range of `j` is
  nontrivial.

  1. Conjugation by `Q` preserves the range of `j`, so it induces an action
     of `Q` on `U` (`AutomorphicAction.onRepresentedSubgroup`). The published
     `hasNontrivialSmoothStableCentralSubgroup_of_isUnipotent` (used in the
     full-centre core) gives a closed subgroup `z : Z ⟶ U`. Here `Z` is smooth,
     affine and connected, its points are central in `U`, its range is
     stable under the action, and it is nontrivial. Stability makes the range
     of `z ≫ j` normal in `Q`.
  2. Let `A = q⁻¹(Z)` (`SubgroupPreimage.groupScheme q (z ≫ j)`), with
     inclusion into `G` and projection to `Z`. It is a closed normal subgroup
     of `G` (`SubgroupPreimage.isClosedSubgroup`, `SubgroupPreimage.isNormal`).
  3. Any two rational points of `A` commute in `G`. Their images in `Q` are
     images of rational points of `U` that are central in `U`. So
     `commute_of_lift` (`CentralQuotientCommutator`) applies with `C = U`; it
     uses `N ≤ center G`. By the published
     `mem_center_of_isNormal_of_commute`, the rational points of the closed
     normal subgroup `A` are central in `G`.
  4. The projection `A ⟶ Z` is surjective on rational points. `q` is
     surjective, so each rational point of `Q` in the image of `Z` lifts to a
     rational point of `G` (`HomogeneousClosedImmersion.exists_rational_lift`),
     and the pullback property of `A` gives the lift to `A`.
  5. `A` is affine and locally of finite type, being closed in `G`. So
     `finite_rationalPoints_of_central_preimage`, with `U` unipotent, shows
     that `Z(K)` is finite. By `id_eq_one_of_finite_rationalPoints`, the
     smooth connected `Z` is trivial, contradicting step 1.

## Provenance

The suggested argument in the statement's Markdown (Milne, *Algebraic
Groups*, 2017, source `milne-2017-algebraic-groups`; Proposition 14.21,
printed p.284; Corollary 16.48, printed p.341; Corollary 14.18, printed p.284)
works with the full preimage of `U` and the structure of nilpotent groups.
The implemented route instead follows the Library full-centre core. It
reduces to a smooth connected central subgroup `Z` of `U` that is stable
under conjugation. It then shows that `Z(K)` is finite, using the
finiteness lemmas of `CentralPreimageTrivial` instead of the splitting of
nilpotent groups.
