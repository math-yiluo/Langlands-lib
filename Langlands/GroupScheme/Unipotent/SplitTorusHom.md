# Homomorphisms from split tori to unipotent group schemes are trivial

Worker 1395 wrote this module. It proves the split-torus case of Milne, *Algebraic Groups* (2017),
Corollary 14.18(b): there are no nontrivial homomorphisms from a group of multiplicative type to a
unipotent group. The case covered here is a split torus mapping to an affine unipotent group scheme
over a field `k`. Milne derives 14.18 from 14.16 (complete reducibility of multiplicative groups).
This module instead uses the Hopf-algebra weight argument `bialgHom_eq_algebraMap_counit` from
`Langlands.GroupScheme.Unipotent.HopfFixed`.

## Diagonalizable source (namespace `Langlands.GroupScheme.Unipotent`)

* `diagonalizable_comul_basis`: in the coordinate bialgebra `k[Λ]` of the Library's diagonalizable
  group `Diagonalizable.grpCorepresentation k Λ`, the monomial basis `AddMonoidAlgebra.basis Λ k`
  is grouplike. This is the Library's `Diagonalizable.comul_single`.
* `pointsTrans_diagonalizable_eq_one`: let `φ` be a homomorphism from the diagonalizable group
  scheme to a corepresented group scheme `Corepresented.groupScheme F e` whose coordinate bialgebra
  satisfies `OneMemStable`. Then the induced natural transformation of point groups sends every
  algebra point to `1`. The Library's `coordinateRestrictionBialgHom` turns `φ` into a bialgebra
  map `B → k[Λ]`. By `bialgHom_eq_algebraMap_counit` this map equals `algebraMap ∘ ε`, and
  `pt_comp_coordinateRestriction` and `pt_comp_counit` translate this into points.
* `diagonalizable_hom_eq_zero`: such a `φ` equals `0`. Use `Corepresented.hom_ext_affinePoints`,
  comparing on affine points with `Corepresented.pointsTrans_app`.

## Split tori (namespace `Langlands.GroupScheme`)

* `SubgroupFunctor.range_zero`: the zero homomorphism has image subgroup functor `⊥`, for group
  schemes over any base scheme. Every point `y ≫ 1` is `1` by `MonObj.comp_one`.
* `IsSplitTorus.hom_eq_zero_of_isUnipotent`: let `S` be a split torus and `U` a unipotent group
  scheme over `Spec k` with `IsAffine U.X.left`. Then every `j : S ⟶ U` is `0`. The proof
  composes `j` with two isomorphisms:
  * from the Library's `Diagonalizable.splitIso` (`k[ℤ^I]` is the split torus) and the given
    splitting of `S`;
  * `AffineCoordinates.groupSchemeIso U`, which presents an affine group scheme as the
    corepresented group of its coordinate functor.

  Unipotence moves along the second isomorphism by `IsUnipotent.of_iso`. Then
  `oneMemStable_of_isUnipotent` (from `Unipotent.CoordinateBialgebra`) gives `OneMemStable`, and
  `diagonalizable_hom_eq_zero` kills the composite.
* `IsSplitTorus.range_eq_bot_of_isUnipotent`: hence `SubgroupFunctor.range j = ⊥`.

No closed-subgroup, smoothness or finite-type hypothesis is used. Only `U` needs to be affine.
