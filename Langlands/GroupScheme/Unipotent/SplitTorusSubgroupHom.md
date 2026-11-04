# Closed subgroups of split tori meet unipotent subgroups trivially

Worker 1405 wrote this module. It proves a split-torus case of Milne, *Algebraic Groups*
(2017), Corollary 14.17, printed p. 284 (PDF p. 300, registered source
`milne-2017-algebraic-groups`). That corollary says a unipotent algebraic subgroup and an
algebraic subgroup of multiplicative type of a common group meet trivially. Milne deduces it
from Proposition 14.16, since both properties pass to subgroups (12.9, 14.7). This module uses
a different route. It never shows that the intersection is of multiplicative type or unipotent.
Instead it shows that the coordinate bialgebra of a closed subgroup of a split torus has a basis
of group-like elements. The Library's Hopf-algebra weight argument `bialgHom_eq_algebraMap_counit`
(`Langlands.GroupScheme.Unipotent.HopfFixed`) then kills every homomorphism from such a subgroup
to a unipotent group. This extends the split-torus argument of
`Langlands.GroupScheme.Unipotent.SplitTorusHom` from split tori to their closed subgroups.

Checking points over fields is not enough here. In characteristic `p` a nontrivial
infinitesimal group such as `μ_p` has only the trivial point over every field. So the argument
has to go through the coordinate bialgebra.

## Coalgebra lemmas (namespace `Langlands.GroupScheme.Unipotent`)

These hold for coalgebras over any field `K`.

* `isGroupLikeElem_of_comul_eq`: a nonzero `c` with `Δ c = c ⊗ c` is group-like. The counit
  identity `(ε ⊗ id) (Δ c) = 1 ⊗ c` gives `ε(c) • c = c`, so `ε(c) = 1` because `c ≠ 0`.
* `span_groupLike_of_surjective`: let `r : A → C` be a surjective coalgebra map, and let `A`
  have a basis `b` with `Δ (b i) = b i ⊗ b i`. Then the group-like elements of `C` span `C`.
  By induction on the span of `b`, each `r (b i)` is either `0` or group-like, using the
  previous lemma.
* `groupLikeBasis`: if the group-like elements span `C`, they form a basis of `C`. Mathlib's
  `linearIndep_groupLikeVal` gives linear independence.
  `groupLikeBasis_comul` records `Δ g = g ⊗ g` for this basis.

## Corepresented groups (namespace `Langlands.GroupScheme.Unipotent`)

Let `e` and `d` corepresent the point-group functors `F` and `H` by `B` and `C`.

* `pointsTrans_eq_one_of_groupLike_basis`: suppose `B` satisfies `OneMemStable` and `C` has a
  basis `g` with `Δ (g i) = g i ⊗ g i`. Then every homomorphism
  `φ : Corepresented.groupScheme H d ⟶ Corepresented.groupScheme F e` sends every algebra point
  to `1`. The Library's `coordinateRestrictionBialgHom` turns `φ` into a bialgebra map
  `B → C`. By `bialgHom_eq_algebraMap_counit` this map equals `algebraMap ∘ ε`, and
  `pt_comp_coordinateRestriction` and `pt_comp_counit` translate this into points.
* `hom_eq_zero_of_groupLike_basis`: such a `φ` equals `0`. Use
  `Corepresented.hom_ext_affinePoints` and compare on affine points with
  `Corepresented.pointsTrans_app`.

These two lemmas generalize the Library's `pointsTrans_diagonalizable_eq_one` and
`diagonalizable_hom_eq_zero` from the monomial basis of `k[Λ]` to any group-like basis.

## Split tori (namespace `Langlands.GroupScheme`)

* `IsSplitTorus.hom_eq_zero_of_isClosedSubgroup`: let `S` be a split torus over `Spec k`, let
  `incl : Z ⟶ S` be a closed subgroup, and let `U` be a unipotent group scheme. Assume `Z` and `U`
  have affine underlying schemes. Then every homomorphism `ψ : Z ⟶ U` is `0`. The proof:
  * Identify `S` with the diagonalizable group `k[ℤ^I]` by `Diagonalizable.splitIso` and the given
    splitting.
  * Identify `Z` and `U` with corepresented groups by `AffineCoordinates.groupSchemeIso`.
  * Since `incl` is a closed immersion, the Library's `Chevalley.coordinateRestriction_surjective`
    makes the coordinate restriction `k[ℤ^I] → O(Z)` surjective. It is a coalgebra map.
  * The monomial basis of `k[ℤ^I]` is group-like (`diagonalizable_comul_basis`), so
    `span_groupLike_of_surjective` and `groupLikeBasis` give `O(Z)` a group-like basis.
  * `IsUnipotent.of_iso` moves unipotence to the corepresented copy of `U`, and
    `oneMemStable_of_isUnipotent` gives `OneMemStable`. Then
    `hom_eq_zero_of_groupLike_basis` kills the transported `ψ`.
* `IsSplitTorus.eq_one_of_comp_eq_comp`: let `s : S ⟶ P` be a monomorphism from a split torus
  and `j : U ⟶ P` a closed subgroup with `U` unipotent, both affine. Take points `a` of `S` and `n`
  of `U` on any relative test scheme `T` with `a ≫ s = n ≫ j`. Then `a = 1`. The Library's
  `subgroupIntersection s j` is the pullback of `s` and `j`. Its first projection is a closed
  subgroup of `S` (`isClosedSubgroup_subgroupIntersectionFst`), so it is affine. The previous
  theorem makes its second projection to `U` equal to `0`. Hence `n = 1` by the pullback
  property, and `a = 1` since `s` is a monomorphism.

Only `S` and `U` need to be affine. No smoothness, connectedness or finite-type hypothesis is used.
