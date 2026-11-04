# Reflection of semisimplicity under arbitrary field extension

Author: Worker 1429.

This module proves `Langlands.GroupScheme.SemisimpleFieldReflectionStatement`
in arbitrary universe `u`: the theorem `semisimpleFieldReflectionStatement`
has exactly the type `SemisimpleFieldReflectionStatement.{u}`. That statement
says the following. Let `k K : Type u` be fields with an `Algebra k K`, and let
`G` be an actual group scheme over `Spec k`. If the actual scalar extension
`G_K = (GroupScheme.baseChange b).obj G`, with
`b = Spec.map (CommRingCat.ofHom (algebraMap k K))`, is semisimple, then `G`
is semisimple. `IsSemisimple G_K` is the only hypothesis on `G`.

Throughout, `b` is surjective, flat and quasi-compact by the published
`fieldExtension_fpqc`. This holds for every field extension, including
transcendental extensions and inseparable extensions of imperfect fields.

## Reflection of the trivial unipotent radical

`HasTrivialUnipotentRadical.of_fieldExtension` assumes that `G` over `k` has
affine structure morphism (`IsAffineHom G.X.hom`) and that
`HasTrivialUnipotentRadical G_K` holds. It concludes
`HasTrivialUnipotentRadical G`. The proof follows the published
`IsConnectedReductive.hasTrivialUnipotentRadical_of_unipotentFieldExtension`,
with the given extension `k → K` in place of `k → k̄`.

Let `i : H ⟶ G` be a closed subgroup over `k` such that `H` is smooth,
connected and unipotent and the range of `i` is normal. Its base change
`i_K : H_K ⟶ G_K` has these properties:

- `i_K` is a closed subgroup, by `IsClosedSubgroup.baseChange`.
- `H_K` is smooth, because smoothness is stable under pullback.
- `H` is affine because it is a closed subgroup of an affine group
  (`IsClosedSubgroup.isAffineHom`). Hence `H_K` is connected, by
  `connectedSpace_baseChange_of_smooth_affine`.
- `H_K` is unipotent, by `IsUnipotent.baseChange`. This also uses that `H` is
  affine.
- The range of `i_K` is normal. `SubgroupFunctor.range_baseChangeHom`
  identifies this range with the base change of the range of `i`, and
  `SubgroupFunctor.IsNormal.baseChange` shows that this base change is
  normal.

The hypothesis on `G_K` therefore gives `range i_K = ⊥`, that is,
`(range i).baseChange b = ⊥`. Since `b` is fpqc,
`SubgroupFunctor.eq_bot_of_baseChange_eq_bot` gives `range i = ⊥`.

## Reflection of connected reductivity

`IsConnectedReductive.of_fieldExtension` derives `IsConnectedReductive G`
from `IsConnectedReductive G_K` alone. It proves the four fields of the
structure separately.

- **Smoothness.** The published `smooth_of_baseChange` uses fpqc descent of
  smoothness along `b`.
- **Connectedness.** The published `connectedSpace_of_baseChange` uses that
  the projection `G_K → G` is a continuous surjection, because `b` is
  surjective.
- **Affineness.** `G_K` is affine over `Spec K`, so its underlying scheme
  `pullback G.X.hom b` is affine. The published `fieldExtensionAffineDescent`
  makes `G.X.left` affine, and hence `G.X.hom` is an affine morphism. This
  argument is the one used in `HasFiniteCenter.of_fieldExtension`.
- **Geometric unipotent radical.** Write `a : Spec k̄ → Spec k` and
  `c : Spec K̄ → Spec K` for the algebraic-closure maps (`toAlgebraicClosure`).
  `IsAlgClosed.lift` gives a `k`-algebra map `ι : k̄ → K̄`, where `K̄` is a
  `k`-algebra through `k → K → K̄`. Let `d : Spec K̄ → Spec k̄` be the map of
  spectra of `ι`. The ring identity `ι ∘ (k → k̄) = (K → K̄) ∘ (k → K)`, which
  is `ι.commutes`, gives the scheme equation `c ≫ b = d ≫ a`. The geometric
  hypothesis on `G_K` is radical triviality for `(G_K)_{K̄}`. The published
  `baseChangeCompIso` and `HasTrivialUnipotentRadical.of_iso` transport it to
  `G` base-changed along `c ≫ b = d ≫ a`, and then to `(G_{k̄})_{K̄}`. Since `G`
  is affine, so is `G_{k̄}`. The previous section, applied to the extension
  `k̄ → K̄`, then gives `HasTrivialUnipotentRadical G_{k̄}`. This is the last
  field of `IsConnectedReductive G`.

## Semisimplicity

`IsSemisimple.of_fieldExtension` combines the connected-reductivity
reflection with the published `IsSemisimple.hasFiniteCenter_of_fieldExtension`.
That theorem produces an actual finite closed representative of the full
scheme-theoretic centre of `G` over `k`. Here the full centre is the centre
functor on all test schemes over `Spec k`, with its restriction maps and
including nonreduced tests (`IsSchemeTheoreticCenter`, `HasFiniteCenter`).
Finally, `semisimpleFieldReflectionStatement` introduces the universally
quantified data and applies `IsSemisimple.of_fieldExtension`.

## Provenance and scope

This is an internal derivation from implemented Library results:

- fpqc descent of smoothness, from Mathlib `LocalFlatDescent` through
  `smooth_of_baseChange`;
- field-extension affineness descent;
- preservation of unipotence and of connectedness of smooth affine groups
  under field extension;
- base change of closed subgroups, ranges and normality;
- fpqc reflection of trivial subgroup functors;
- the published finite-centre reflection.

No reflection assertion is assumed as a hypothesis, and no new axiom or
external literature claim is introduced. Only the standard axioms `propext`,
`Classical.choice` and `Quot.sound` are used.

The fields and the extension are arbitrary. In particular, transcendental
extensions, inseparable extensions and imperfect fields of positive
characteristic are all covered. No reductivity, smoothness, affineness,
connectedness, centre representability or finiteness, or effective-descent
premise is placed on `G`.
