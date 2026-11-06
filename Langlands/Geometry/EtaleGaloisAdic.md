# Continuous Galois actions on inverse limits of Galois-tower étale cohomology

This internal construction combines the smooth Galois representations on
colimit étale cohomology over finite Galois towers (`EtaleGaloisTower`) with
Worker 61's inverse limit topology on limits of discrete representations
(`Cohomology.DivisibleSystem.ContinuousLimit`). For an inverse system of
coefficient sheaves on a scheme `X` over a field `K` (for instance the
reductions modulo `ℓ^m` of an `ℓ`-adic coefficient system), it forms the
inverse limit over `m` of the colimit cohomology, with the inverse limit
topology of the discrete levels. It proves that the Galois action is jointly
continuous for the Krull topology. All declarations are in namespace
`Langlands.Geometry.EtaleGaloisTower`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, Theorem 5.7 on printed p. 313, uses `λ`-adic Galois representations
on the étale cohomology of Shimura varieties. Such representations are
inverse limits of torsion cohomology with continuous Galois actions. The
published `ContinuousLimit` records, with its sources, that limits of smooth
discrete levels carry jointly continuous actions. This module supplies the
Galois-tower levels with non-constant coefficients. It identifies neither the
limit with `ℓ`-adic cohomology of `X ×_{Spec K} Spec L`, nor the colimit with
cohomology of that base change. It proves no finiteness and constructs no
Shimura or coefficient-system specialization.

## Inputs

Let `K L : Type u` be fields with `Algebra K L`, `f : X ⟶ Spec K`, and
`R : Type u` a commutative ring. The section assumes the published ambient
instances `HasDerivedCategory.{wS}` at every product vertex of the scheme
diagram of `galoisTower f` and `HasDerivedCategory.{wR} (ModuleCat R)`. The
group `L ≃ₐ[K] L` carries Mathlib's Krull topology.

## Declarations

- `galoisAdicSystem L f R q` sends an inverse system
  `F : ℕᵒᵖ ⥤ ModuleSheaf X R` to the inverse system
  `m ↦ colimitCohomologyFunctor R (galoisTower f) q (F m)` of Galois
  representations. It is postcomposition with the published colimit
  cohomology functor.
- `isSmooth_galoisAdicSystem` states that every level is smooth. It is the
  published `isSmooth_colimitCohomology` for the levelwise smooth Galois
  tower `isLevelwiseSmooth_galoisTower`.
- `GaloisAdicSpace L f R q F` is the published `ContinuousLimit.ConeSpace` of
  the limit cone of this inverse system. It is the inverse limit of the
  levels with the coarsest topology making every projection to a discrete
  level continuous. Its instance `T2Space` is the published
  `t2Space_of_isLimit`.
- `continuous_galoisAdicAction` states that the action
  `(σ, x) ↦ σ · x` of `L ≃ₐ[K] L` on `GaloisAdicSpace` is jointly continuous,
  by the published `ContinuousLimit.continuous_action` applied to the smooth
  levels.
- `galoisAdicContRepresentation` is the representation by continuous linear
  maps, the published `contRepresentation`. `galoisAdicContAction` is, for a
  topological coefficient ring acting continuously, the published
  `contAction`: an object of `ContAction (TopModuleCat R) (L ≃ₐ[K] L)`.
- `galoisAdicTopRepFunctor L f R q` is, for a discrete coefficient ring, the
  composite of `galoisAdicSystem` with the published `limitTopRepFunctor`. It
  is a functor from inverse systems of coefficient sheaves on `X` to
  topological representations of `L ≃ₐ[K] L`.

## Provenance

This is an internal composition of the published `EtaleGaloisTower` and
`ContinuousLimit` constructions; it adds no new proof technique. Harris (1999),
registered as `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
Theorem 5.7 on printed p. 313, is cited only as motivation. The continuity
sources are those recorded in the published `ContinuousLimit` Markdown.
