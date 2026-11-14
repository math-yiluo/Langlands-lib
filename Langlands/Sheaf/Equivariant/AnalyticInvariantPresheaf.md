# The presheaf of invariant sections `V(G) ↦ F(V)^G`

Author: Worker 26. Builds on the following modules:

- `Langlands.Sheaf.Equivariant.NaturalActionSections` (imported; same candidate): natural
  actions `NaturalAction K Φ` along a functor `Φ`, the presheaf of invariant sections
  `NaturalAction.invariantPresheaf` and its functor on sheaves
  `NaturalAction.sheafInvariantFunctor R J` with its finite-limit instance, and, for an action
  `b` of a topological group `G` on `U` whose restriction to the open subgroup `⊤` is
  admissible, `isSmooth_actionRepresentation_of_isAdmissible_top` and
  `discreteSectionsSmoothOfTop` with their instances.
- `Langlands.Geometry.Analytic.EquivariantQuasiEtaleSite` and
  `Langlands.Geometry.Analytic.EquivariantEtaleSite` (Worker 21, imported): Berkovich's
  categories `EquivariantQuasiEtaleSite X = Qét(X(G))` and `EquivariantEtaleSite X = Ét(X(G))`
  of a `G`-space `X`, as `(GSpace.quasiEtale).Over ⊤ X` and `(GSpace.etale).Over ⊤ X`, and the
  forgetful functors `toQuasiEtaleSite X` and `toEtaleSite X` to the quasi-étale and étale
  sites of `GSpace.forget.obj X`. Through the imports, `GSpace.{u, v, v} K G` (from
  `Langlands.Geometry.Analytic.ContinuousAnalyticAction`): actions `X.obj` of `G` on
  analytic spaces `X.obj.V`, given by `X.obj.ρ` and `X.obj.ρAut : G →* Aut X.obj.V`, with
  Hausdorff underlying space and continuous action (`X.property`).
- `Langlands.Sheaf.Equivariant.TwistedOver` (through the imports): the twisted category
  `TwistedOver P ρ`, whose morphisms are pairs of a twist `g` and an arrow covering the
  action of `g` (`homMk`, `Hom.twist`, `Hom.left`, `hom_ext`), the inclusion `ι P ρ`, the
  base object `base P ρ` (`X` with identity structure map) and the action
  `baseAction P ρ` of `G` on it (`g` acts by the twisted endomorphism given by `g⁻¹`).
- `Langlands.Sheaf.Equivariant.AnalyticGSheaves` (imported): the twisted topologies
  `twistedQuasiEtaleTopology ρ` and `twistedEtaleTopology ρ`, the lift systems
  `compactLiftSystem ρ` (an admissible action on a compact object is the restriction of the
  local action of a lift `ActionLift ρ f` to an open subgroup of its subgroup) and
  `distinguishedLiftSystem ρ`, and the categories `QuasiEtaleGSheaf ρ A` (discrete sheaves for
  `compactLiftSystem ρ`) and `EtaleGSheaf ρ A` (locally discrete sheaves for
  `distinguishedLiftSystem ρ`).
- `Langlands.Geometry.Analytic.LocalActionLifts` (Worker 21, through the imports):
  `ActionLift ρ f` (an open subgroup, a continuous action of it on the source of `f`, and the
  equivariance of `f`) and `IsCompactSpace`.
- `Langlands.Sheaf.Equivariant.TwistedGlobalSections` (through the imports):
  `sheafGlobalSectionsRep J R`, the representation of `G` on global sections, which is the
  sections over `base P ρ` with the action `baseAction P ρ`.
- `Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleGlobalComplex` and
  `Langlands.Sheaf.Equivariant.AnalyticEtaleCohomology` (imported): Berkovich's `Γ_{X(G)}` as
  `quasiEtaleGSheafInvariantSections ρ R` and `etaleGSheafInvariantSections ρ R`, the
  `G`-invariants (`smoothInvariantsFunctor`, from
  `Langlands.Cohomology.DivisibleSystem.PermutationProjective`) of the smooth part of the
  global sections.
- `Langlands.Sheaf.Equivariant.TwistedCompactComparison` (imported):
  `smoothPartInvariantsIso R G`, which identifies the invariants of the smooth part of a
  representation with its invariants.
- Mathlib: `MorphismProperty.Over.mk`, `CategoryTheory.evaluation`, `NatIso.ofComponents`,
  `Functor.isoWhiskerLeft`, `comp_preservesFiniteLimits`, `Rep.invariantsFunctor`.

All declarations are in the namespace `Langlands.Sheaf.Equivariant.Analytic`.

## Purpose

Let `X` be a `G`-space. In step A.4 of the proof of his Theorem 1.4.2, Berkovich defines,
for a quasi-étale `G`-sheaf `F` on `X`, the presheaf `(b_*F)^G` on `Qét(X(G))` by
`(b_*F)^G(V(G)) = F(V)^G`; the étale case is step B.2. This module constructs that presheaf on
`Qét(X(G))` and on `Ét(X(G))`, for all sheaves of modules on the twisted site of `X` and for
`G`-sheaves. It identifies the value at `X(G)` with `Γ_{X(G)}(F)`. For a quasi-étale
`G`-sheaf and compact `V`, it shows that the representation of `G` on `F(V)` is smooth.

Not done here: that `(b_*F)^G` is a sheaf for the topology of `Qét(X(G))` (Berkovich
asserts it; a proof needs `G`-equivariant fibre products, which the Library does not have),
the functor `b_*` itself, and the isomorphisms `b^*((b_*F)^G) ≅ F` and `E ≅ (b_*b^*E)^G` of
steps A.4 and A.5.

## Setting

`K : Type u` is a complete ultrametric normed field, `G : Type z` a group with a topology,
and `X : GSpace.{u, v, v} K G`. The action on the underlying space is
`X.obj.ρAut : G →* Aut X.obj.V`; the twisted sites are those of `X.obj.ρAut`. `R` is a
commutative ring. Each section lists its further hypotheses.

## Lifts

- `gSpaceActionLift f : ActionLift X.obj.ρAut (GSpace.forget.map f)`, for a `G`-morphism
  `f : U ⟶ X`: the action of `G` on `U`, as a lift with open subgroup `⊤`. Continuity is that
  of the action on `U`; equivariance is that of `f`.

## Quasi-étale

- `quasiEtaleToTwisted X : EquivariantQuasiEtaleSite X ⥤ TwistedOver quasiEtale X.obj.ρAut`:
  `toQuasiEtaleSite X` followed by the inclusion `ι`. It forgets the action on `V`.
- `quasiEtaleGEndo X V g`: the twisted endomorphism of `(quasiEtaleToTwisted X).obj V` with
  twist `g` and arrow the action `V.left.obj.ρ g` of `g` on `V`; it covers the action of `g`
  on `X` because `V.hom` is a `G`-morphism. `quasiEtaleGEndo_twist`, `quasiEtaleGEndo_left`;
  `quasiEtaleGEndo_mul`: `quasiEtaleGEndo X V (g * g') = quasiEtaleGEndo X V g' ≫ quasiEtaleGEndo X V g`;
  `quasiEtaleGEndo_one`.
- `quasiEtaleNaturalAction X : NaturalAction G (quasiEtaleToTwisted X)`: `g` acts on `V` by
  `quasiEtaleGEndo X V g⁻¹` (`quasiEtaleNaturalAction_act_apply`), so that `g` acts on
  sections by restriction along it. The commutation with a morphism `f : V ⟶ W` of
  `Qét(X(G))` holds by `hom_ext`: both twists are `k⁻¹`, and the arrows agree because `f` is a
  `G`-morphism.
- `equivariantQuasiEtaleBase X`: the object `X(G)` of `Qét(X(G))` (identity of `X`).
  `quasiEtaleToTwisted_obj_base`: it goes to `base quasiEtale X.obj.ρAut`.
  `quasiEtaleNaturalAction_act_base`: there the action is `baseAction quasiEtale X.obj.ρAut`.
  Both are equalities proved by `rfl`.

Let `R : Type uR` be a commutative ring and modules be in `ModuleCat.{w} R`.

- `quasiEtaleInvariantPresheaf X R : Sheaf (twistedQuasiEtaleTopology X.obj.ρAut) (ModuleCat R) ⥤ ((EquivariantQuasiEtaleSite X)ᵒᵖ ⥤ ModuleCat R)`:
  `(quasiEtaleNaturalAction X).sheafInvariantFunctor R (twistedQuasiEtaleTopology X.obj.ρAut)`.
  Its value at a sheaf `F` and an object `V(G)` is the module `F(V)^G` of invariant sections.
- `mem_quasiEtaleInvariantPresheaf_iff`: a section `s ∈ F(V)` is invariant exactly when
  `F.obj.map (quasiEtaleGEndo X V g⁻¹).op` fixes it for every `g`.
- `quasiEtaleInvariantPresheaf_preservesFiniteLimits` (instance).
- `quasiEtaleInvariantPresheafBaseIso X R`, for modules in `ModuleCat.{uR} R`: evaluation at
  `X(G)` after `quasiEtaleInvariantPresheaf X R` is
  `sheafGlobalSectionsRep (quasiEtaleTopology X.obj.V) R ⋙ Rep.invariantsFunctor R G`.
  The components are identities, by the two `rfl` equalities above.
- `quasiEtaleGSheafInvariantPresheaf X R`: the same presheaf on quasi-étale `G`-sheaves, the
  composite of `discreteSheafInclusion` with `quasiEtaleInvariantPresheaf X R`.
- `quasiEtaleGSheafInvariantPresheaf_preservesFiniteLimits` (instance), assuming
  `[HasSheafify (twistedQuasiEtaleTopology X.obj.ρAut) (ModuleCat R)]` and
  `[(compactLiftSystem X.obj.ρAut).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology X.obj.ρAut)]`,
  under which the inclusion of discrete sheaves is left exact.
- `quasiEtaleGSheafInvariantPresheafBaseIso X R`, for `[IsTopologicalGroup G]` and
  `R : Type (max u (v + 1) uL)`: evaluation at `X(G)` after
  `quasiEtaleGSheafInvariantPresheaf X R` is `quasiEtaleGSheafInvariantSections X.obj.ρAut R`,
  Berkovich's `Γ_{X(G)}`. It is `quasiEtaleInvariantPresheafBaseIso` whiskered by the inclusion,
  followed by the inverse of `smoothPartInvariantsIso R G` whiskered by the global sections.

## Smoothness on compact objects

Let `V` be an object of `Qét(X(G))` and `hV : IsCompactSpace (GSpace.forget.obj V.left)`.

- `isAdmissible_quasiEtaleNaturalAction X V hV`: the restriction to `⊤` of the action of `G`
  on `(quasiEtaleToTwisted X).obj V` is admissible for `compactLiftSystem X.obj.ρAut`: `V` is
  compact, and the action is the local action of the lift `gSpaceActionLift V.hom`.
- `isSmooth_quasiEtaleGSheaf_sections X R F V hV`: for a quasi-étale `G`-sheaf `F`, the
  representation of `G` on `F(V)` is smooth.
- `quasiEtaleGSheafSectionsSmooth X R V hV : QuasiEtaleGSheaf X.obj.ρAut (ModuleCat R) ⥤ SmoothRep R G`:
  `F ↦ F(V)` as a smooth representation (`discreteSectionsSmoothOfTop`), with the instance
  `quasiEtaleGSheafSectionsSmooth_additive`.
- `quasiEtaleGSheafInvariantPresheafEvaluationIso X R V hV`: evaluation at `V(G)` after
  `quasiEtaleGSheafInvariantPresheaf X R` is
  `quasiEtaleGSheafSectionsSmooth X R V hV ⋙ smoothInvariantsFunctor R G` (identity
  components).
- `quasiEtaleGSheafSectionsSmooth_preservesFiniteLimits` (instance), under the same `HasSheafify`
  and `HasFiniteEquivariantRefinements` assumptions as above.

## Étale

The étale constructions repeat the quasi-étale ones with `EquivariantEtaleSite X`,
`toEtaleSite X`, `twistedEtaleTopology`, `etaleTopology` and `EtaleGSheaf`:
`etaleToTwisted`, `etaleGEndo` (with `etaleGEndo_twist`, `etaleGEndo_left`, `etaleGEndo_mul`,
`etaleGEndo_one`), `etaleNaturalAction` (with `etaleNaturalAction_act_apply`),
`equivariantEtaleBase`, `etaleToTwisted_obj_base`, `etaleNaturalAction_act_base`,
`etaleInvariantPresheaf` (with `mem_etaleInvariantPresheaf_iff`,
`etaleInvariantPresheaf_preservesFiniteLimits`), `etaleInvariantPresheafBaseIso` (for modules
in `ModuleCat.{uR} R`), and `etaleGSheafInvariantPresheaf`, the composite of
`smoothSheafInclusion` with `etaleInvariantPresheaf X R`.

- `etaleGSheafInvariantPresheaf_preservesFiniteLimits` (instance), assuming
  `[HasSheafify (twistedEtaleTopology X.obj.ρAut) (ModuleCat R)]` and
  `[(distinguishedLiftSystem X.obj.ρAut).HasAdmissibleRefinements (twistedEtaleTopology X.obj.ρAut)]`,
  under which the inclusion of locally discrete sheaves is left exact.
- `etaleGSheafInvariantPresheafBaseIso X R`, for `[IsTopologicalGroup G]` and
  `R : Type (max u (v + 1) uL)`: evaluation at `X(G)` is
  `etaleGSheafInvariantSections X.obj.ρAut R`, Berkovich's `Γ_{X(G)}` for étale `G`-sheaves.

The smoothness statements are not made in the étale case. The Library defines étale
`G`-sheaves by local discreteness. Deducing smoothness of `F(V)` for compact `V` would need
an argument with finite coverings that is not formalized.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`).
Printed page numbers equal PDF page numbers.

- §1.4, printed p.7, for discrete `G`: "Given a `G`-sheaf `F`, then for any quasi-étale (resp.
  étale) morphism `U(H) → X(G)`, where `H` is a subgroup of `G`, the set `F(U)` is endowed
  with a canonical action of the group `H`. Indeed, for `h ∈ H` the morphism `h⁻¹ : U → U`
  induces an isomorphism `U ≅ hU = U ×_{X,h⁻¹} X` over `X`. The latter induces a bijection
  `σ(h) : F(hU) ≅ F(U)`, and the action of `H` on `F(U)` is defined by `hf = σ(h)(^h f)`."
- Definition 1.4.1, printed pp.7–8: "A quasi-étale (resp. étale) `G`-sheaf on `X` is a
  quasi-étale (resp. étale) `G^d`-sheaf `F` such that for any quasi-étale morphism `U → X`
  with compact `U` the action of `G_U` on `F(U)` is discrete."
- Proof of Theorem 1.4.2, step A.4, printed p.9: "Let now `F` be a quasi-étale `G`-sheaf on
  `X`. For `(V(G) → X(G)) ∈ Qét(X(G))` one has `b_*F(V(G)) = F(V)`. The group `G` acts on
  `F(V)`, and therefore we can define a sheaf `(b_*F)^G` on `X(G)~_qét` by
  `(b_*F)^G(V(G)) = F(V)^G`."
- Step B.2, printed p.9: "As in the quasi-étale case (see A.4), one defines for any
  `F ∈ T_G(X_ét)` a sheaf `(b_*F)^G ∈ X(G)~_ét`."
- §1.2, printed p.4: "We denote by `Γ_{X(G)}` the global sections functor on `X(G)~_qét`
  (resp. `X(G)~_ét`), i.e., `Γ_{X(G)}(F) = F(X(G))`." Through Theorem 1.4.2 the Library
  carries this functor to `G`-sheaves as `quasiEtaleGSheafInvariantSections` and
  `etaleGSheafInvariantSections` (`F ↦ F(X)^G`). Applied to `(b_*F)^G`, Berkovich's
  definition gives `(b_*F)^G(X(G)) = F(X)^G`. This is the content of the two base
  isomorphisms.

## Provenance and correspondence

Derived. The twisted sites with the lift systems of `AnalyticGSheaves` model Berkovich's
`G^d`-sheaves and `G`-sheaves. A section over the object `V` of the twisted site is a section
of Berkovich's `F(V)`. The action of `g` on it is restriction along the twisted endomorphism
with twist `g⁻¹` and arrow `ρ_V(g⁻¹)`. This is the same convention as the Library's
`baseAction`, and at `V = X` it gives the Library's action on global sections. Matching it
with Berkovich's formula `hf = σ(h)(^h f)` is a matter of conventions and is not formalized.

Berkovich defines `(b_*F)^G` for `G`-sheaves. Here it is defined for every module sheaf on the
twisted site (a `G^d`-sheaf) and then restricted to `G`-sheaves. The smoothness for compact
`V` is the discreteness in Definition 1.4.1 for the action of the whole group `G`, which
extends the action on `X` through the `G`-space structure of `V`; here it is
`gSpaceActionLift`. Berkovich calls `(b_*F)^G` a sheaf; this module defines it only as a
presheaf.
