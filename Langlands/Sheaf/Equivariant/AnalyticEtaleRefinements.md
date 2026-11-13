# Admissible refinements on the twisted étale site

Author: Worker 26. Uses the published `Langlands.Sheaf.Equivariant.AnalyticGSheaves`
(twisted étale site `twistedEtaleTopology`, the local actions `liftAction` and
`liftOpenSubgroup` of lifts, the local action system `distinguishedLiftSystem`,
Worker 26) and `Langlands.Sheaf.Equivariant.LocalActionSmoothPart` (the class
`LocalActionSystem.HasAdmissibleRefinements`, the predicate
`IsRestrictionEquivariant` and the sieve `fiberRefinementSieve`, Worker 26). From
Worker 21 it uses the étale site `EtaleSite`, its topology `etaleTopology` and point
functor `EtaleSite.points`, distinguished étale morphisms `IsDistinguishedEtale`,
and lifts `ActionLift` (`Langlands.Geometry.Analytic.EtaleSite` and
`Langlands.Geometry.Analytic.LocalActionLifts`). It also uses the twisted category
`TwistedOver` with `translate`, `untwist` and `rho_mul_hom`
(`Langlands.Sheaf.Equivariant.TwistedOver`).

## Purpose

Let a topological group `G` act on a `K`-analytic space `X` by `ρ : G →* Aut X`. The
étale `G`-sheaves `EtaleGSheaf ρ A` are the locally discrete sheaves on the twisted
étale site for the local action system `distinguishedLiftSystem ρ`. This system
consists of the lifts of the action to distinguished étale objects. The published
modules `LocalActionSmoothPart` and `AnalyticEtaleCompactCohomology` assume the class

    (distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)

for the abelian structure of étale `G`-sheaves of modules, for enough injectives,
and for their derived compactly supported cohomology. This module reduces that class
to three new propositions about the plain étale site of `X`. The three propositions
remain hypotheses. This module does not prove any of them.

The module has three parts.

1. A generic part, in `Langlands.Sheaf.Equivariant.LocalActionSystem`, for an
   arbitrary local action system on an arbitrary site.
2. Translates of lifts and stability of distinguished étale morphisms under
   isomorphisms of the target, in `Langlands.Analytic.SaturatedAtlasPresentation`.
3. The three conditions and the reduction, in `Langlands.Sheaf.Equivariant.Analytic`.

## Data and universes

- `K : Type u` is a complete ultrametric normed field. `X` is an object of Worker 21's
  `LocalizedCategory.{u, v, v} (K := K)`.
- `G : Type z` is a group with a topology, and `ρ : G →* Aut X`. Translates of lifts
  and the two theorems that use them also assume `[IsTopologicalGroup G]`.
- In the generic part, `T` is a category with a Grothendieck topology `J`, and `L` is
  a local action system on `T` for `G`.

## Generic part

- `admissibleSieve_le_fiberRefinementSieve f₁ f₂ k₁ k₂ hk` (theorem): for a cospan
  `f₁ : V₁ ⟶ U`, `f₂ : V₂ ⟶ U` and a cone `k₁ : W ⟶ V₁`, `k₂ : W ⟶ V₂` with
  `k₁ ≫ f₁ = k₂ ≫ f₂`, the sieve `L.admissibleSieve W` is contained in
  `L.fiberRefinementSieve f₁ f₂ k₁ k₂`. If `e : W' ⟶ W` factors as `k ≫ f` through an
  object `V` with an admissible local action, then `V` itself, with the arrows
  `f ≫ k₁` and `f ≫ k₂`, is the required common refinement.
- `hasAdmissibleRefinements_iff L J` (theorem): `L.HasAdmissibleRefinements J` holds
  if and only if two conditions hold. First, every arrow `p : V' ⟶ V` between objects
  with admissible local actions `a` and `a'` satisfies
  `IsRestrictionEquivariant a a' p`. Second, `L.Covers J` holds. The first condition
  is the first field of the class. `L.Covers J` follows from the class by the
  published `HasAdmissibleRefinements.covers`. Conversely, `L.Covers J` and the
  previous inclusion of sieves give the second field.

## Translates of lifts

- `IsDistinguishedEtale.comp_iso hf e` (theorem): if `f : U ⟶ X` is distinguished
  étale and `e : X ≅ Y` is an isomorphism, then `f ≫ e.hom` is distinguished étale.
  The factorization `U ≅ O ⊂ Ū → X` of `f` gives the factorization of `f ≫ e.hom`
  through `Ū → X → Y`. Étale and quasi-étale morphisms are stable under composition
  with isomorphisms.
- `ActionLift.translateSubgroup l g` (definition): for a lift `l : ActionLift ρ f`
  with subgroup `H` and `g : G`, the conjugate subgroup `g H g⁻¹`. The theorem
  `mem_translateSubgroup` states that `y` lies in it if and only if `g⁻¹ * y * g ∈ H`.
- `ActionLift.translateHom l g` (definition): the continuous homomorphism
  `y ↦ g⁻¹ * y * g` from `g H g⁻¹` to `H`. The theorem `coe_translateHom` states this
  formula.
- `ActionLift.translate l g` (definition): a lift `ActionLift ρ (f ≫ (ρ g).hom)` with
  subgroup `g H g⁻¹`, on which `y` acts as `g⁻¹ * y * g` acts for `l`. Its
  equivariance is the identity
  `l.action (g⁻¹ y g) ≫ f ≫ ρ g = f ≫ ρ (g⁻¹ y g) ≫ ρ g = f ≫ ρ g ≫ ρ y`.
  Here `ρ (g * g') = ρ g' ≫ ρ g`, which is the published `rho_mul_hom`. The
  morphism `f ≫ (ρ g).hom` is the structure morphism of the translate of `f` by `g`
  (`TwistedOver.translate`). The theorem `translate_action` states that the action is
  this composite, by definition.

## The three conditions

- (A) `HasDistinguishedEtaleNeighbourhoods X`: for every object `U` of `EtaleSite X`
  and every point `x` of `U`, there are an object `V` of `EtaleSite X` and an arrow
  `f : V ⟶ U` over `X` such that `V.hom` is distinguished étale and `x` lies in the
  image of the point map of `f`. This condition involves only the étale site of `X`,
  not the action.
- (B) `HasDistinguishedEtaleLifts ρ`: every object `V` of `EtaleSite X` with
  `V.hom` distinguished étale admits a lift `ActionLift ρ V.hom`. Such a lift consists
  of an open subgroup `H` of `G`, a continuous action of `H` on `V.left`, and the
  `H`-equivariance of `V.hom`.
- (C) `HasCompatibleDistinguishedEtaleLifts ρ`: for all objects `U` and `V` of
  `EtaleSite X` whose structure morphisms are distinguished étale, every arrow
  `f : V ⟶ U` over `X`, and all lifts `a : ActionLift ρ U.hom` and
  `b : ActionLift ρ V.hom`, there is a subgroup `N` of `G` such that `N` is open,
  `N ≤ a.subgroup`, `N ≤ b.subgroup`, and for every `g ∈ N`,
  `(b.action g).hom ≫ f.left = f.left ≫ (a.action g).hom`. In words, `f` intertwines
  the two lifted actions on an open subgroup.

(C) only concerns arrows over `X`, that is, untwisted arrows. The reduction handles
twisted arrows with translates of lifts.

## The reduction

`hasAdmissibleRefinements_distinguishedLiftSystem ρ hA hB hC` (theorem, assuming
`[IsTopologicalGroup G]`) proves

    (distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)

from (A), (B) and (C), by `hasAdmissibleRefinements_iff` and the following two
theorems.

`covers_distinguishedLiftSystem ρ hA hB` (theorem) proves
`(distinguishedLiftSystem ρ).Covers (twistedEtaleTopology ρ)` from (A) and (B).

1. A sieve on an object `U` of the twisted site covers for `twistedEtaleTopology ρ`
   exactly when its pullback along the inclusion `ι etale ρ` covers `U.obj` for
   `etaleTopology X`. By Worker 21's `mem_etaleTopology_of_jointlySurjective`, it
   suffices that every point of `U.obj` is in the image of an arrow of the pullback.
2. For a point `x`, (A) gives a distinguished étale `V` and an arrow `f : V ⟶ U.obj`
   whose image contains `x`. (B) gives a lift `l` on `V`.
3. The arrow `(ι etale ρ).map f` lies in the admissible sieve of `U`. The object
   `(ι etale ρ).obj V` carries the local action `liftAction l` on
   `liftOpenSubgroup l`. This action is admissible, with the lift `l` itself and the
   inclusion of its subgroup into itself.

`isRestrictionEquivariant_distinguishedLiftSystem ρ hC ha ha' p` (theorem, assuming
`[IsTopologicalGroup G]`) proves the first condition of `hasAdmissibleRefinements_iff`
from (C).

1. Admissible local actions `a` on `V` and `a'` on `V'` are restrictions of
   `liftAction l` and `liftAction l'` for lifts `l` and `l'` on the distinguished
   étale objects `V.obj` and `V'.obj`. Here `liftAction l` lets `h` act by the
   twisted endomorphism with twist `h⁻¹` and arrow `l.action h⁻¹`.
2. Let `p : V' ⟶ V` be a twisted arrow with twist `g`. Then
   `p.left ≫ V.hom = V'.hom ≫ (ρ g).hom`, so `p.left` is an arrow over `X` from the
   translate `(translate etale ρ g).obj V'.obj`, whose structure morphism is
   `V'.hom ≫ (ρ g).hom`. This arrow is `untwist g p`. The translate is distinguished
   étale by `IsDistinguishedEtale.comp_iso` and carries the lift `l'.translate g`.
3. (C) for `untwist g p`, `l` and `l'.translate g` gives an open subgroup `N` such
   that `l'.action (g⁻¹ y g) ≫ p.left = p.left ≫ l.action y` for all `y ∈ N`.
4. Let `K'` be an open subgroup contained in the subgroup of `a`. Put
   `M = H' ⊓ g⁻¹ (N ⊓ K') g`, where `H'` is the subgroup of `a'`. For `h ∈ M`, take
   `k = g h g⁻¹ ∈ K'`. The twisted morphisms `a' h ≫ p` and `p ≫ a k` have twists
   `g h⁻¹` and `k⁻¹ g = g h⁻¹`. Their arrows are `l'.action h⁻¹ ≫ p.left` and
   `p.left ≫ l.action k⁻¹`. These agree by step 3 at `y = k⁻¹ ∈ N`, because
   `g⁻¹ k⁻¹ g = h⁻¹`. Twisted morphisms are compared by `TwistedOver.hom_ext`.

## Correspondence with the source

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
defines distinguished étale morphisms in §1.4 (printed p.7) and treats their lifts
there. In the manuscript, `𝒰` is the distinguished étale object and `U` is the
compact space containing it:

> Furthermore, an étale morphism 𝒰 → X is said to be distinguished if it can be
> represented as a composition 𝒰 ↪ U → X [the arrows are j and φ], where U is
> compact, φ is quasi-étale and j identifies 𝒰 with a distinguished open subset of
> U, i.e., with such one whose complement in U is an analytic domain. For such a
> morphism the action of G on X extends in a canonical way to a continuous action of
> an open subgroup G_U ⊂ G. Since U∖𝒰 is a compact analytic domain in U, then 𝒰 is
> invariant under the action of an open subgroup G_𝒰 ⊂ G_U.

He continues: if there is another representation `𝒰 ↪ U' → X`, and so another
extension of the action to an open subgroup `G'_𝒰`, "then one can find an open
subgroup N ⊂ G_𝒰 ∩ G'_𝒰 such that the two actions of N on 𝒰 coincide. (For this it
suffices to apply the Key Lemma to the quasi-étale morphism U ×_X U' → X.)" After
Definition 1.4.1 (printed p.8) he states that an étale `G^d`-sheaf `F` is a `G`-sheaf
if and only if "for any étale morphism U → X and any element f ∈ F(U) each point of U
has a distinguished open neighborhood 𝒰 such that the stabilizer of f|_𝒰 is open in
G_𝒰". In §1.3 (printed p.6) he states that the distinguished étale objects of
`C(x/X)` form a cofinal subcategory.

The correspondence is as follows.

- (A) is the existence of distinguished open neighbourhoods that the remark on p.8
  and the cofinality claim on p.6 presuppose. Berkovich does not prove it in the
  manuscript. (A) is weaker than the existence of distinguished open
  neighbourhoods, because the arrow `V ⟶ U` need not be an open immersion.
- (B) is the existence of the action of `G_𝒰` on `𝒰` on p.7. Berkovich obtains it
  from the Key Lemma (Berkovich 1994, Key Lemma 7.2) on the compact `U` and from the
  invariance of `𝒰` under an open subgroup, because `U∖𝒰` is a compact analytic
  domain. That argument is not formalized here.
- (C) is a compatibility of lifts along arrows over `X`. Restricted to the identity
  arrow of one object, (C) says that two lifts on the same object agree on an open
  subgroup. Berkovich states this for the two canonical extensions coming from two
  representations of `𝒰`. Here it is a hypothesis for arbitrary lifts and arbitrary
  arrows. That is the form the class `HasAdmissibleRefinements` needs, because
  `distinguishedLiftSystem` admits every lift and every twisted arrow. In the
  manuscript, compatibility along an arrow is what makes it an `N`-morphism, as in
  step A.1 of the proof of Theorem 1.4.2 (printed p.8) for quasi-étale morphisms
  of compact spaces.

The conjugate lift `l.translate g` corresponds to the transport of the action to the
translate `ᵍU = U ×_{X,g⁻¹} X` that Berkovich uses on p.7 to define `G`-sheaves for a
discrete group. Over `X`, `ᵍU` is isomorphic to `U` with structure morphism `f`
followed by the action of `g` on `X`. That is the structure morphism
`f ≫ (ρ g).hom` of the translate here. The reduction itself, and the passage from untwisted to twisted
arrows, are derived for this formalization. Berkovich does not state them.

## Scope

- (A), (B) and (C) are new hypotheses. Their proofs belong with the geometry of the
  étale site and with Berkovich's Key Lemma. None of them is proved here.
- No instance is declared. A user supplies the class locally, for example with
  `haveI := hasAdmissibleRefinements_distinguishedLiftSystem ρ hA hB hC`.
- The generic part applies to every local action system. In particular, the second
  field of `HasAdmissibleRefinements` holds whenever objects with admissible local
  actions cover.
