# Morphisms over `X` into a disjoint union of copies of `X`

Author: Worker 384.

This module proves that morphisms `U → ∐_{s ∈ S} X` lying over a given
morphism `p : U → X` correspond to the locally constant maps from the
underlying space of `U` to `S`. Such a morphism is determined by its index map
(`copiesOverHom_ext`), and every locally constant map is the index map of one
(`exists_copiesOverHom`). This is the geometric input of the proof of
`SetInducedSpace.MorphismOfSitesStatement` (module `SetInducedSiteProof`).
All statements are proved. Namespace:
`Langlands.Analytic.SaturatedAtlasPresentation.SetInducedSpace`.

Throughout, `K : Type u` is a complete ultrametric normed field and all
analytic spaces are objects of `LocalizedCategory.{u, max z v, max z v}`
(module `LocalizedDisjointUnion`), with index types in `Type z`. Points of an
analytic space `Y` are the elements of its underlying topological space
`localizedSpaceFunctor.obj Y`. The underlying space of the chosen disjoint union
`(localizedSigmaCofan Xf).pt` of a family `Xf : J → LocalizedCategory` is, by
definition, the sigma type `Σ j, (presentationOf (Xf j)).presentation.space`.

## Points of disjoint unions

- `localizationFunctor_map_nonemptyReplacementHom_comp_localizedSigmaCofan_inj`: the inclusion
  `j` of `localizedSigmaCofan Xf`, precomposed with the image of the
  quasi-isomorphism `nonemptyReplacementHom`, is the image of the inclusion
  `j` of the presentation-level `sigmaCofan`. So the inclusion is the fraction
  `(L π)⁻¹ ≫ L(inclusion j)`.
- `localizedSpaceFunctor_map_localizedSigmaCofan_inj`: hence, by the Library lemma
  `numerator_point_eq_of_fraction_equation` (module
  `NearIdentityDomainRestriction`), the inclusion `j` sends a point `x` to
  `⟨j, x⟩`.
- `sigma_map_apply`: a morphism `m` out of the disjoint union sends `⟨j, x⟩`
  to the image of `x` under `inj j ≫ m`.
- `index Xf φ x := (localizedSpaceFunctor.map φ x).1`, for
  `φ : U ⟶ (localizedSigmaCofan Xf).pt`: the index of the summand containing
  the image of `x`.
- `isLocallyConstant_index`: the index map is locally constant, because the
  summands of a sigma type are open and the point map of `φ` is continuous.
- `index_comp`: the index of `a ≫ φ` at `x` is the index of `φ` at the image
  of `x` under `a`.
- `index_comp_inj`: the index of `a ≫ inj j` is constantly `j`.

## The open domains of the copies

Fix `S : Type z` and `X`. Write `C = localizedSigmaCofan fun _ : S => X` and
`codiag X : C.pt ⟶ X` for the codiagonal
`Cofan.IsColimit.desc (isColimitLocalizedSigmaCofan fun _ : S => X) (fun _ => 𝟙 X)`,
which is the identity on every copy (`inj_codiag`, `inj_codiag_assoc`).

- `copySet X s`: the points `⟨s, x⟩` of the copy `s`, that is,
  `Sigma.fst ⁻¹' {s}`. It is open (`isOpen_copySet`, Mathlib's
  `isOpen_sigma_fst_preimage`). `copyDomain X s` is the corresponding open
  domain of `C.pt` (Library `openDomain`, module `InvariantAnalyticDomains`).
- `pairwise_disjoint_copySet`, `exists_mem_copySet`: the sets `copySet X s`
  are pairwise disjoint and cover the points of `C.pt`.
- `isColimitCopyDomains`: hence `C.pt`, with the canonical morphisms
  `domainι` of the domains `copyDomain X s`, is a coproduct of these domains.
  This is `isColimitOpenPartition` (module `OpenPartitionCoproduct`), which
  says that an analytic space partitioned into open subsets is the coproduct
  of the corresponding open domains.
- `inj_mem_copySet`: the inclusion `inj s` lands in `copySet X s`, by
  `localizedSpaceFunctor_map_localizedSigmaCofan_inj`.
- `domainι_copyDomain_comp_codiag_inj`: on the domain of the copy `s`, the
  codiagonal followed by `inj s` is the canonical morphism of the domain:
  `domainι (copyDomain X s) ≫ codiag X ≫ inj s = domainι (copyDomain X s)`.
  Proof: let `Φ : C.pt ⟶ C.pt` be the morphism that is
  `domainι (copyDomain X t) ≫ codiag X ≫ inj t` on the domain of each copy
  `t` (by `isColimitCopyDomains`). Then `inj t ≫ Φ = inj t` for every `t`:
  `inj t` factors as `ℓ ≫ domainι (copyDomain X t)` through the domain
  (Library `domainLift`, since `inj t` lands in `copySet X t`), so
  `inj t ≫ Φ = ℓ ≫ domainι ≫ codiag X ≫ inj t = inj t ≫ codiag X ≫ inj t = inj t`.
  By the coproduct property of `C`, `Φ = 𝟙`, and the claim is the defining
  property of `Φ` on the domain of the copy `s`.
- `eq_comp_codiag_inj`: a morphism `f : W ⟶ C.pt` whose index map is
  constantly `s` satisfies `f = f ≫ codiag X ≫ inj s`. Proof: `f` factors
  through `domainι (copyDomain X s)` by `domainLift`; apply the previous
  lemma.

## Morphisms over `X` into the copies

Fix also `U` and a locally constant map `c` from the points of `U` to `S`.

- `fibreDomain c hc s`: the fibre `c ⁻¹' {s}`, which is open, as an open
  domain of `U`.
- `isColimitFibreDomains`: `U`, with the canonical morphisms of these
  domains, is their coproduct (`isColimitOpenPartition` again: the fibres are
  pairwise disjoint and cover `U`).
- `overHom p c hc : U ⟶ C.pt`: the morphism equal to
  `domainι (fibreDomain c hc s) ≫ p ≫ inj s` on the fibre over `s`
  (`domainι_comp_overHom`).
- `overHom_comp_codiag`: `overHom p c hc ≫ codiag X = p`, checked on every
  fibre with `inj_codiag`.
- `index_overHom`: the index map of `overHom p c hc` is `c`: a point `x` is
  the image of the point `⟨x, rfl⟩` of the fibre over `c x`
  (`domainι_apply`), and the index of `domainι ≫ p ≫ inj (c x)` is `c x`
  (`index_comp_inj`).
- `eq_overHom`: if `φ : U ⟶ C.pt` satisfies `φ ≫ codiag X = p` and its index
  map is `c`, then `φ = overHom p c hc`. Proof: on the fibre over `s`, the
  index map of `domainι (fibreDomain c hc s) ≫ φ` is constantly `s`, so by
  `eq_comp_codiag_inj` this morphism equals
  `domainι ≫ φ ≫ codiag X ≫ inj s = domainι ≫ p ≫ inj s`; conclude by
  `isColimitFibreDomains`.

The two main results write the codiagonal in its expanded form
`Cofan.IsColimit.desc (isColimitLocalizedSigmaCofan fun _ : S => X) (fun _ => 𝟙 X)`.
For the underlying space `X.V` of an action this is, by definition, the
Library's `projectionHom X S` (module `SetInducedSpace`).

- `copiesOverHom_ext`: if `φ ψ : U ⟶ C.pt` both lie over `p` (their
  composites with the codiagonal are `p`) and have the same index map, then
  `φ = ψ`. Both are `overHom p c` for `c` the index map of `φ`, which is
  locally constant by `isLocallyConstant_index`.
- `exists_copiesOverHom`: for every locally constant `c` there is a morphism
  `φ : U ⟶ C.pt` over `p` with index map `c`, namely `overHom p c hc`.

## Provenance: derived

The result is the standard universal property of a disjoint union of analytic
spaces, used implicitly where Berkovich constructs `X_Σ`: Berkovich, *Étale
equivariant sheaves on p-adic analytic spaces* (unfinished manuscript,
1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.2, printed p.4:

> For a G-set Σ, let X_Σ denote the disjoint union ∐_{σ∈Σ} X_σ (X_σ are
> copies of X) ...

In a disjoint union every copy is an open and closed subspace, and the copies
cover the union. A morphism over `X` into `∐_σ X_σ` therefore decomposes its
source into the open and closed pieces `U_σ`, the fibres of the locally
constant index map, and on `U_σ` it is `p` followed by the inclusion of the
copy `σ`. The Lean proof implements exactly this decomposition with the
Library's open domains, `domainLift`, and the gluing of morphisms along a
partition of the source into open subsets (`isColimitOpenPartition`, the
disjoint-open case of Berkovich, *Étale cohomology for non-Archimedean
analytic spaces*, Publ. Math. IHÉS 78 (1993), Proposition 1.3.2).
