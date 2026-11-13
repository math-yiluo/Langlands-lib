# Left induction to sheaves on a twisted site

Author: Worker 26. Builds on the following modules:

- `Langlands.Sheaf.Equivariant.TwistedOver` (through
  `Langlands.Sheaf.Equivariant.TwistedCompactComparison`): the twisted category
  `TwistedOver P ρ` of a `G`-object `X`, whose morphisms `Hom U V` carry a twist `g : G` and
  an underlying arrow. It also provides the inclusion `ι P ρ : P.Over ⊤ X ⥤ TwistedOver P ρ`
  (twist one), the translations `translate P ρ g`, the relabelling arrows
  `relabel ρ g U : ι U ⟶ ι (gU)` (twist `g`, identity underlying arrow), `untwist`, the
  twisted topology `twistedTopology ρ J`, and restriction `restriction ρ J A`.
- `Langlands.Sheaf.Equivariant.TwistedGodement` (through the same import): the right adjoint
  `induction ρ J A` of restriction, given by right Kan extension along `ι`.
- Mathlib: left Kan extensions, `Functor.sheafPullbackConstruction`, final functors, the AB4
  structure of `ModuleCat`, and preservation of injectives by right adjoints.

All declarations are in the namespace `Langlands.Sheaf.Equivariant.TwistedOver`.

## Purpose

Restriction of module sheaves from the twisted site to the site over `X` already has the
right adjoint `induction`. This module gives it a left adjoint that preserves finite limits.
So restriction sends injective sheaves on the twisted site to injective sheaves over `X`.
`TwistedRepCohomology` uses this to identify the cohomology of the restriction of a twisted
sheaf with the right derived functors of representation-valued global sections. The argument
is the twisted-site analogue of Worker 13's `Langlands.Sheaf.Equivariant.Induction` (for the
ordinary-topological transport site).

## Translates are final

Let `C : Type u` be a category, `P` a morphism property of `C` with `[P.RespectsIso]`, `X : C`,
`G : Type uG` a group and `ρ : G →* Aut X`. Fix `V : TwistedOver P ρ`. An object of
`CostructuredArrow (ι P ρ).op (op V)` is an object `W` over `X` with a twisted arrow
`V ⟶ ι W`.

- `translateArrows ρ V : Discrete G ⥤ CostructuredArrow (ι P ρ).op (op V)` sends `g` to the
  translate `gV` with the relabelling arrow `relabel ρ g V.obj`.
- `twist_eq_of_hom_translateArrows`: a morphism from a costructured arrow `d` to the
  translate by `g` forces `g` to be the twist of the arrow of `d`, since arrows in the image
  of `ι` have twist one.
- `translateArrows_hom_subsingleton` (instance): such morphisms are unique, because the
  relabelling arrow is an epimorphism and `ι` is faithful.
- `toTranslate ρ V d`: every costructured arrow `d` factors through the translate by its
  twist, via `untwist` and `relabel_comp_ι_map_untwist`.
- `translateArrows_final` (instance): `translateArrows ρ V` is final. For each `d` the
  category of factorizations through translates is nonempty (`toTranslate`) and any two
  objects are joined by a morphism (both translates have the same index, and morphisms are
  unique).

## Exactness of left Kan extension

Let `R : Type w` be a commutative ring.

- `discrete_hasColimitsOfShape` and `discrete_hasExactColimitsOfShape`: if `G` is `w`-small,
  coproducts of `w`-modules indexed by `G` exist and are exact. Both are transported along
  `Discrete.equivalence (equivShrink G)` from Mathlib's instances for small index types.

From here on assume `[HasColimitsOfShape (Discrete G) (ModuleCat R)]`.

- `costructuredArrow_hasColimitsOfShape ρ R V` (instance): colimits of modules over
  `CostructuredArrow (ι P ρ).op V` exist, by finality of `translateArrows`.
- `hasPointwiseLeftKanExtension` and `hasLeftKanExtension` (instances): every module
  presheaf over `X` has a pointwise left Kan extension along `(ι P ρ).op`.
- `lanEvaluationIsoColimit ρ R V`: the value at `V` of the left Kan extension functor
  `(ι P ρ).op.lan` is the colimit over the costructured arrows of `V`. This restates
  Mathlib's `lanEvaluationIsoColim` without its smallness hypotheses (which do not hold
  here), with the same proof.

With also `[HasExactColimitsOfShape (Discrete G) (ModuleCat R)]`:

- `costructuredArrow_hasExactColimitsOfShape` (instance): colimits over these costructured
  arrow categories are exact, by Mathlib's `hasExactColimitsOfShape_of_final` applied to
  `translateArrows`.
- `lan_preservesFiniteLimits` (instance): `(ι P ρ).op.lan` preserves finite limits, checked
  objectwise through `lanEvaluationIsoColimit`.

The colimit over the costructured arrows of `V` is, mathematically, the direct sum of the
values on the translates `gV`. The module uses only finality and does not construct this
isomorphism. For nontrivial `G` these categories are not connected (twists are preserved),
so `ι` is not representably flat and Mathlib's flatness criterion does not apply.

## Sheaves

Let `J` be a translation-invariant Grothendieck topology on `P.Over ⊤ X`, with
`[HasSheafify (twistedTopology ρ J) (ModuleCat R)]`.

- `leftInduction ρ R J : Sheaf J (ModuleCat R) ⥤ Sheaf (twistedTopology ρ J) (ModuleCat R)`:
  Mathlib's `Functor.sheafPullbackConstruction.sheafPullback` along `ι`, that is, left Kan
  extension along `(ι P ρ).op` followed by sheafification for the twisted topology.
- `leftInductionAdjunction ρ R J : leftInduction ρ R J ⊣ restriction ρ J (ModuleCat R)`:
  Mathlib's `sheafAdjunctionContinuous`.
- `leftInduction_preservesFiniteLimits` (instance, given exact coproducts indexed by `G`): it
  is the composite of `sheafToPresheaf`, `(ι P ρ).op.lan` and sheafification, each of which
  preserves finite limits.
- `restriction_preservesInjectiveObjects` (instance, same hypotheses): restriction sends
  injective module sheaves on the twisted site to injective module sheaves over `X`, by
  Mathlib's `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`.

## Provenance and scope

This is internal infrastructure (ours). Berkovich, *Etale equivariant sheaves on p-adic
analytic spaces* (unfinished 1995–1996 manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`), obtains the
action of `G` on `H^q_c(X, b^*F)` and `H^q(X, b^*F)` in §1.5–1.6 through Godement
resolutions and Proposition 1.5.1. The route here differs: an exact left adjoint of
restriction, so that injectives remain injective after forgetting the twist. The module
proves no statement about cohomology. No topology on `G` and no smoothness or discreteness
condition is used.
