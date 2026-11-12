# Étale and quasi-étale `G`-sheaves on analytic spaces

Author: Worker 26. Uses the published twisted category
`Langlands.Sheaf.Equivariant.TwistedOver` and local action systems
`Langlands.Sheaf.Equivariant.LocalAction` and
`Langlands.Sheaf.Equivariant.LocalActionDiscretePart` (Workers 13, 26). It also uses
Worker 21's analytic sites: the étale site `EtaleSite`, its translations
(`Langlands.Geometry.Analytic.EtaleSiteTranslation`), the quasi-étale site
`QuasiEtaleSite`, lifts of actions `ActionLift`, distinguished étale morphisms
`IsDistinguishedEtale` and compact analytic spaces `IsCompactSpace`
(`Langlands.Geometry.Analytic.LocalActionLifts`).

## Purpose

Let a group `G` act on a `K`-analytic space `X`. Berkovich defines étale and
quasi-étale `G`-sheaves on `X` in two steps. First, `G^d`-sheaves are sheaves with
an action of `G` with the discrete topology that is compatible with the action on
`X`. Second, a discreteness condition uses the actions of open subgroups of `G`
on objects `U → X` that lift the action on `X`. This module specializes the
general framework of `TwistedOver` and `LocalAction` to Worker 21's analytic
sites. It defines

- the twisted étale and twisted quasi-étale sites of `X`, whose sheaves are the
  `G^d`-sheaves;
- the local action of a lift of the action of `G` to an object, and the local
  action systems of lifts on distinguished étale objects and on compact
  quasi-étale objects;
- the categories `EtaleGSheaf` and `QuasiEtaleGSheaf`, which model Berkovich's
  `T_G(X_ét)` and `T_G(X_qét)`.

## Data

- `K : Type u` is a complete ultrametric normed field. `X` is an object of Worker
  21's `LocalizedCategory.{u, v, v} (K := K)` of `K`-analytic spaces.
  `G : Type z` is a group and `ρ : G →* Aut X` an action of `G` on `X`. No
  topology on `G` and no continuity of `ρ` is needed for the twisted sites. The
  lift systems and the `G`-sheaf categories use `[TopologicalSpace G]`.
- `A` is a concrete category (the coefficients of the sheaves), as in
  `LocalAction`.

## The twisted sites

- `etale_isTranslationInvariant ρ` is the instance
  `IsTranslationInvariant (etaleTopology X)` for the morphism property `etale`.
  The translation of `TwistedOver` by `g` is Worker 21's `EtaleSite.translate (ρ g)`
  (both are `MorphismProperty.Comma.mapRightIso` along `ρ g`), and Worker 21's
  instance `EtaleSite.isCocontinuous_translate_functor` shows that it is
  cocontinuous.
- `twistedEtaleTopology ρ` is the twisted topology `twistedTopology ρ (etaleTopology X)`
  on `TwistedOver etale ρ`.
- `QuasiEtaleSite.translate e : QuasiEtaleSite X ≌ QuasiEtaleSite Y`, for an
  isomorphism `e : X ≅ Y`, is `mapRightIso` along `e`. It keeps the source of an
  object and composes the structure morphism with `e`.
- `QuasiEtaleSite.map_translate_inverse_mem e hR`: if `R` is a quasi-étale covering
  of `V` (a member of `quasiEtalePrecoverage Y V`), then its image under the
  inverse translation is a quasi-étale covering of the translated object. Proof:
  a quasi-étale covering is described by finite families of subsets of the source
  of `V`, by the arrows of `R` and by charts of their sources. Translation does not
  change sources or arrows, so the same families work.
- `quasiEtale_isTranslationInvariant ρ` is the instance
  `IsTranslationInvariant (quasiEtaleTopology X)`. It is proved with Worker 21's
  criterion `isCocontinuous_toGrothendieck_of_equivalence` and the previous lemma.
- `twistedQuasiEtaleTopology ρ` is `twistedTopology ρ (quasiEtaleTopology X)` on
  `TwistedOver quasiEtale ρ`.

By `TwistedOver.isSheaf_iff_isSheaf_comp`, a presheaf on the twisted étale
(resp. quasi-étale) category is a sheaf exactly when its restriction to the étale
(resp. quasi-étale) site of `X` is a sheaf. `TwistedOver.md` explains how
presheaves on the twisted category carry the bijections `F(U) ≅ F(gU)` of a
`G^d`-sheaf. That equivalence is not formalized.

## Local actions of lifts

Let `P` be a morphism property of analytic spaces, `U` an object of
`TwistedOver P ρ` and `l : ActionLift ρ (TwistedOver.hom U)` a lift: an open subgroup
`l.subgroup`, a continuous action `l.action : l.subgroup →* Aut U.obj.left`, and
equivariance of the structure morphism.

- `actionLift_inv_mul_hom l g h`: `(l.action (g * h)⁻¹).hom` is
  `(l.action g⁻¹).hom ≫ (l.action h⁻¹).hom`.
- `liftOpenSubgroup l : OpenSubgroup G` is `l.subgroup` with its openness.
- `liftAction l : liftOpenSubgroup l →* (End U)ᵐᵒᵖ` sends `h` to the twisted
  endomorphism with twist `h⁻¹` and arrow `(l.action h⁻¹).hom`
  (`liftAction_twist`, `liftAction_left`). This is Berkovich's convention, recorded
  in `TwistedOver.md`: `h` acts on `F(U)` through the morphism `h⁻¹ : U → U`.
- `isLift_liftAction l hH`: for a subgroup `H ≤ l.subgroup`, the restriction of
  `liftAction l` to `H` is a lift in the sense of `TwistedOver.IsLift`.
- `isDiscreteSection_liftAction_of_agreeOn F h hs`: if two lifts `l` and `l'` agree
  on an open subgroup (`ActionLift.AgreeOn`), a section of a presheaf `F` on the
  twisted category is discrete for `liftAction l` if it is discrete for
  `liftAction l'`.
- `liftSystem P ρ Adm` is the local action system on `TwistedOver P ρ` for a
  predicate `Adm` on objects of `P.Over ⊤ X`. An action `a` of an open subgroup `H`
  on `U` is admissible when `Adm U.obj` holds and `a` is the restriction to `H` of
  `liftAction l` for some lift `l` with `H ≤ l.subgroup`.
- `isLiftSystem_liftSystem Adm`: every admissible action of `liftSystem P ρ Adm` is
  a lift (`LocalActionSystem.IsLiftSystem`).

## `G`-sheaves

- `distinguishedLiftSystem ρ` is the lift system on the twisted étale category for
  the objects whose structure morphism is distinguished étale
  (`IsDistinguishedEtale`).
- `compactLiftSystem ρ` is the lift system on the twisted quasi-étale category for
  the objects with compact source (`IsCompactSpace`, which includes
  Hausdorffness).
- `EtaleGSheaf ρ A` is the full subcategory `SmoothSheaf` of sheaves on the twisted
  étale site whose sections are locally discrete for `distinguishedLiftSystem ρ`
  (`LocalActionSystem.IsLocallyDiscrete`). For every section `s` over `U`, the
  arrows `W ⟶ U` that factor through a morphism `V ⟶ U` from a distinguished étale
  object `V`, such that the restriction of `s` to `V` is discrete for some lift
  on `V`, form a covering sieve of `U`.
- `QuasiEtaleGSheaf ρ A` is the full subcategory `DiscreteSheaf` of sheaves on the
  twisted quasi-étale site such that, for every object `U` with compact source and
  every lift `l` on `U`, every section over `U` is discrete for `liftAction l`
  (`LocalActionSystem.IsDiscrete`).

The general results of `LocalAction` and `LocalActionDiscretePart` apply to these
categories, for example the discrete-part coreflector on discrete sheaves.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished
1995–1996 manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
(folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`),
§1.4, printed pp. 7–8 = PDF pp. 7–8, read in the original by Worker 26.

- p.7: "for any quasi-étale morphism `U → X` with compact `U` the action of `G` on
  `X` extends in a canonical way to a continuous action of some open subgroup
  `G_U ⊂ G` on `U`". Further, "an étale morphism `𝒰 → X` is said to be
  distinguished if it can be represented as a composition `𝒰 ↪ U → X` (arrows `j`
  and `φ`), where `U` is compact, `φ` is quasi-étale and `j` identifies `𝒰` with a
  distinguished open subset of `U`, i.e., with such one whose complement in `U` is
  an analytic domain". Then `𝒰` carries a canonical continuous action of an open
  subgroup `G_𝒰`, and two such actions coincide on an open subgroup. In Worker 21's
  `IsDistinguishedEtale`, `U` is the source of the étale morphism and `Ubar` the
  compact space.
- Definition 1.4.1 (pp. 7–8): "A quasi-étale (resp. étale) `G`-sheaf on `X` is a
  quasi-étale (resp. étale) `G^d`-sheaf `F` such that for any quasi-étale morphism
  `U → X` with compact `U` the action of `G_U` on `F(U)` is discrete. The category
  of quasi-étale (resp. étale) `G`-sheaves on `X` will be denoted by `T_G(X_qét)`
  (resp. `T_G(X_ét)`)."
- p.8: "It is easy to see that an étale `G^d`-sheaf `F` is a `G`-sheaf if and only
  if for any étale morphism `U → X` and any element `f ∈ F(U)` each point of `U`
  has a distinguished open neighborhood `𝒰` such that the stabilizer of `f|𝒰` is
  open in `G_𝒰`."

The quasi-étale topology is Berkovich's (*Vanishing cycles for formal schemes*,
1994, §3), as formalized in Worker 21's `QuasiEtaleSite`.

## Provenance and correspondence

This module specializes derived infrastructure. The modelling choices below are
ours:

- `G^d`-sheaves are modelled as sheaves on the twisted sites, as in `TwistedOver`.
- Lifts. Berkovich uses the canonical action of `G_U` given by the Key Lemma.
  The Lean systems accept every lift. By Worker 21's statement
  `QuasiEtaleActionLiftStatement`, which formalizes this consequence of the Key
  Lemma, lifts exist on compact quasi-étale objects when `X` is Hausdorff and `ρ` is
  continuous, and any two lifts agree on an open subgroup. Then, by
  `isDiscreteSection_liftAction_of_agreeOn`, a section is discrete for one lift
  exactly when it is discrete for every lift. At the Library base of this module the
  statement has no proof. This module uses neither the statement nor any existence
  or uniqueness of lifts. In particular, when an object has no lift, the conditions impose
  nothing on it.
- `QuasiEtaleGSheaf` is Definition 1.4.1 for the quasi-étale topology: discreteness
  over every object with compact source.
- `EtaleGSheaf` follows the criterion of p.8 rather than the étale case of
  Definition 1.4.1. The étale case of Definition 1.4.1 evaluates an étale sheaf on
  quasi-étale objects, through the comparison morphism between the two sites, and
  that comparison is not available in the Library. The p.8 criterion stays inside
  the étale site. Berkovich asks for distinguished open neighbourhoods of the points
  of `U`. The Lean condition asks that the arrows through distinguished étale
  objects carrying a lift on which `s` is discrete form a covering sieve of the
  twisted étale topology. This is the general notion
  `LocalActionSystem.IsLocallyDiscrete`. The criterion of p.8 gives such coverings
  by open neighbourhoods. No comparison between the two formulations is proved
  here.
- Discreteness over all distinguished étale objects, that is
  `DiscreteSheaf` for `distinguishedLiftSystem`, is not used. Distinguished étale
  objects need not be compact, and Berkovich requires discreteness only over
  compact objects.

## Not formalized here

Berkovich's Theorem 1.4.2, the equivalence of `T_G(X_qét)` and `T_G(X_ét)` with
sheaves on `X(G)`, is not formalized. Nor are the comparison between étale and
quasi-étale `G`-sheaves, the Key Lemma, and the equivalence of the Lean
conditions with Berkovich's. Points of the étale site, which compactly supported
cohomology on these sites requires (see `TwistedCompactSupport`), are Worker 21's
open dependency.
