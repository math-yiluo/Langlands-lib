# Base change of level towers and the Galois action on their colimit cohomology

This internal construction base-changes a tower of schemes on compact open
levels along a ring extension `F → L`. It obtains the action of
`L ≃ₐ[F] L` on the colimit over levels of étale cohomology of the
base-changed tower, with coefficients pulled back from a base of the
original tower. The action is by morphisms of smooth `G`-representations, so
it commutes with the action of `G`. All declarations are in namespace
`Langlands.Shimura.LevelTowerGalois`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, studies the cohomology of a tower of Shimura varieties over a number
field, base-changed to an algebraic closure. This cohomology carries commuting
actions of the finite adelic group and of the absolute Galois group. Examples
are the prime-to-ℓ finite adeles after (3.5) on printed p. 307, and
`GG(A_f^{ℓ,p})` as `K(N)^{ℓ,p}` varies in Proposition 4.10 on printed
p. 311. This module constructs the commuting actions for an arbitrary tower
over `Spec F`, an arbitrary extension `L`, and coefficients pulled back from
a base of the tower. Harris's passages are only motivation.

The module constructs no Shimura varieties and none of Harris's automorphic
coefficient systems. It proves no topology on `L ≃ₐ[F] L` and no continuity
of its action. For an algebraic Galois extension, continuity would require
comparing the base change to `L` with the colimit over finite subextensions,
which is not done here. The published `EtaleGaloisTower` module treats the
colimit over finite Galois subextensions for a single scheme. No comparison
with the cohomology of a limit scheme is made.

## Inputs

Let `G : Type u` be a group with a topology. Let
`T : CompactOpenLevel G ⥤ Scheme.{u}` be a tower on the published transporter
category of compact open levels. Let `F` and `L` be commutative rings in
universe `u` with `Algebra F L`. The structure maps are a natural
transformation `s : T ⟶ (Functor.const _).obj (Spec F)`, so
`T.map a ≫ s_V = s_U` for `a : U ⟶ V` (`structure_naturality`).

## The base-changed tower

- `baseChangeTower F L s` sends a level `U` to the published
  `baseChange F L s_U = T(U) ×_{Spec F} Spec L`. An arrow `a` goes to the
  morphism of fiber products given by `T.map a` on the first factor and the
  identity on the second factor. The functor laws are checked on both
  projections. `baseChangeTower_map_fst` and `baseChangeTower_map_snd` record
  the two projections of a level map.
- `etale_baseChangeTower_map` states that, if the level maps of `T` are
  étale, so are those of the base-changed tower. This follows from Mathlib's
  `MorphismProperty.pullbackMap`, since étale morphisms are stable under
  base change and composition.
- `baseChangeProjection F L s : baseChangeTower F L s ⟶ T` is the first
  projection at every level.
- `baseChangeTower_selfArrow` assumes that each `k ∈ U` acts on `T(U)` by the
  identity. It then proves the same for the base-changed tower.

## The Galois action on the tower

- `towerGaloisAut s σ`, for `σ : L ≃ₐ[F] L`, is the natural automorphism of
  the base-changed tower whose component at `U` is the published
  `baseChangeAut s_U σ`. This acts by the identity on the first factor and by
  `Spec σ` on the second (`towerGaloisAut_hom_app`). Naturality is checked on
  both projections.
- `towerGaloisAction F L s : (L ≃ₐ[F] L) →* (Aut (baseChangeTower F L s))ᵐᵒᵖ`
  assembles these. As for the published `galoisAut` of a single base change,
  it lands in the opposite automorphism group, because the induced morphisms
  of spectra compose contravariantly. The homomorphism laws are the published
  `baseChangeMap_one` and `baseChangeMap_comp` at every level
  (`towerGaloisAction_hom_app`).
- `towerGaloisAction_over` fixes projections `p : T ⟶ (Functor.const _).obj X`
  of the original tower to a scheme `X`. It states that every Galois
  automorphism lies over `X` through `baseChangeProjection F L s ≫ p`. This
  holds because the published `baseChangeMap` commutes with the first
  projection.

## Colimit cohomology with the Galois action

Assume that the level maps of `T` are étale and that `G` is a topological
group. Let `R : Type u` be a commutative ring, and let `hT` be the
level-triviality hypothesis for `T`.

- `galoisCohomologyFunctor F L s p R hT n` is a functor from module sheaves
  `M` on `X` to `Action (SmoothRep R G) (L ≃ₐ[F] L)`. It is the
  `automorphismActionFunctor` of `LevelTowerCanonicalCoefficients` for the
  base-changed tower, its projections `baseChangeProjection F L s ≫ p`, and
  `towerGaloisAction F L s`. Its underlying smooth representation is the
  colimit over shrinking levels of
  `H^n(T(U) ×_{Spec F} Spec L, (p_U ∘ pr₁)^* M)`, with `G` acting through
  the conjugate levels (`galoisCohomologyForgetIso`).
- `galoisCohomologyFunctor_ρ` states that `σ` acts by the smooth pullback
  along the automorphism `towerGaloisAut s σ` at every level. By
  `canonicalPullback_ι`, it sends the image of a class of level `U` to the
  image of its pullback along the base change of `Spec σ`. Each `σ` acts by
  a morphism of smooth `G`-representations, so the two actions commute.

For a tower of Shimura varieties over a number field `F` and `L` an algebraic
closure of `F`, taking `X = Spec F` and `p = s` gives the
colimit over levels of `H^n(Sh_U ×_F L, s^* M)`. It carries the commuting actions
described above. Constant coefficients are the case where `M` is a constant
sheaf on `Spec F`.

## Provenance

This is an internal construction from published results:

- the base change `baseChange`, `baseChangeMap`, `baseChangeAut` and their
  laws in `EtaleGaloisAction`;
- `automorphismActionFunctor` and the smooth pullbacks in
  `LevelTowerCanonicalCoefficients`;
- Mathlib's fiber products, `pullback.hom_ext`, `pullback.lift_fst`,
  `pullback.lift_snd` and `MorphismProperty.pullbackMap`.

No action, smoothness or compatibility is supplied as input. Harris's
passages are cited only as motivation, and no statement from them is
formalized.
