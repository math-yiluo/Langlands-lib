# The inverse image `b^*` along `b : X → X(G)`

Author: Worker 26. Builds on the following modules:

- `Langlands.Sheaf.Equivariant.NaturalActionInverseImage` (imported; same candidate): for a
  natural action `a` along `Φ : E ⥤ T`, the inflation `a.inflation`, and, assuming left Kan
  extensions along `a.inflation.op`, the functors `inverseImagePresheafFunctor`,
  `inverseImageFunctor` and `sheafInverseImageFunctor` with their adjunctions
  `inverseImagePresheafAdjunction`, `inverseImageAdjunction` and
  `sheafInverseImageAdjunction`, the colimit formula `inverseImagePresheafObjIsoColimit`,
  and the comparison `inverseImagePresheafObjIsoUntwistedColimit` with the colimit over
  untwisted arrows.
- `Langlands.Sheaf.Equivariant.AnalyticInvariantSheaf` (imported), and through it
  `Langlands.Sheaf.Equivariant.AnalyticInvariantPresheaf`: the natural actions
  `quasiEtaleNaturalAction X` and `etaleNaturalAction X` of `G` along
  `quasiEtaleToTwisted X = toQuasiEtaleSite X ⋙ ι` and `etaleToTwisted X = toEtaleSite X ⋙ ι`,
  in which `g` acts by a twisted endomorphism with twist `g⁻¹`. Also the presheaf functors
  `quasiEtaleInvariantPresheaf X R` and `etaleInvariantPresheaf X R`, and, under the image
  pullback hypothesis `hX`, the continuity instances `quasiEtaleToTwisted_isContinuous X hX`
  and `etaleToTwisted_isContinuous X hX` and the sheaf functors
  `quasiEtaleInvariantSheaf X R hX` and `etaleInvariantSheaf X R hX` (Berkovich's
  `(b_*F)^G`). `HasImagePullbacks` is from `Langlands.Sheaf.ImagePullbackContinuity`.
- `Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleCompactCohomology` and
  `Langlands.Sheaf.Equivariant.AnalyticEtaleCompactCohomology` (imported):
  `twistedQuasiEtale_hasSheafify` and `twistedEtale_hasSheafify`, giving sheafification on the
  twisted sites of `ρ : G →* Aut X` for modules over `R : Type (max u (v + 1) uL)` when
  `[Small.{max u (v + 1) uL} G]`.
- `Langlands.Geometry.Analytic.EquivariantQuasiEtaleSite` and
  `Langlands.Geometry.Analytic.EquivariantEtaleSite` (Worker 21, through the imports):
  `EquivariantQuasiEtaleSite X = Qét(X(G))` and `EquivariantEtaleSite X = Ét(X(G))`, their
  forgetful functors `toQuasiEtaleSite X` to `QuasiEtaleSite (GSpace.forget.obj X)` and
  `toEtaleSite X` to `EtaleSite (GSpace.forget.obj X)`, and their topologies
  `equivariantQuasiEtaleTopology X` and `equivariantEtaleTopology X`.
- `Langlands.Sheaf.Equivariant.AnalyticGSheaves` (through the imports): the twisted
  topologies `twistedQuasiEtaleTopology ρ` and `twistedEtaleTopology ρ` on
  `TwistedOver quasiEtale ρ` and `TwistedOver etale ρ`.
- Mathlib: `small_lift`, `AddCommGrpCat.hasColimitsOfShape`, `ModuleCat.hasColimitsOfShape`,
  `Functor.HasLeftKanExtension.mk`, `Functor.pointwiseLeftKanExtensionUnit`,
  `CostructuredArrow`, `CategoryTheory.Prod.fst`, `SingleObj`, `Sheaf`.

All declarations are in the namespace `Langlands.Sheaf.Equivariant.Analytic`.

## Purpose

Let `X` be a `G`-space. In the proof of his Theorem 1.4.2, Berkovich compares sheaves `E` on
`X(G)` with `G`-sheaves `F` on `X` through two functors: the inverse image `b^*` along
`b : X → X(G)` and `F ↦ (b_*F)^G`. `AnalyticInvariantPresheaf` and `AnalyticInvariantSheaf`
construct `(b_*F)^G`. This module constructs the inverse image as its left adjoint, on the
quasi-étale and on the étale side.

The inverse image takes values in sheaves on the twisted site of `X`. These model
Berkovich's sheaves on `X` with an action of the discrete group `G^d` (see the Provenance
section of `TwistedOver.md`), so the action of `G` on the inverse image is part of the
structure. At every object `U` of the twisted site, the inverse image presheaf of `E` is the
colimit of `E(V(G))` over Berkovich's category `C(U/X(G))°`. This is his formula for `b^*`
before sheafification (§1.2, printed p.3).

## Setting

`K : Type u` is a complete ultrametric normed field, `G : Type z` a group with a topology, and
`X : GSpace.{u, v, v} K G`. The twisted sites are those of `X.obj.ρAut : G →* Aut X.obj.V`.
`R : Type (max u (v + 1) z uL)` is a commutative ring, and all modules live in
`ModuleCat.{max u (v + 1) z uL} R`.

Universe choice: the colimits below are indexed by comma categories built from
`Qét(X(G)) × SingleObj Gᵐᵒᵖ`. Instance search shows that these comma categories are
`Small.{max u (v + 1) z}`, so they are small in the universe of the modules, which then
have the colimits. The same universe contains `G`, as needed for sheafification on the
twisted sites. Declarations of this module take explicit universe arguments
`.{u, v, uL, z}` at use sites.

## Quasi-étale

- `quasiEtaleInflation_hasPointwiseLeftKanExtension X R F`: every module presheaf `F` on
  `Qét(X(G)) × SingleObj Gᵐᵒᵖ` has a pointwise left Kan extension along
  `(quasiEtaleNaturalAction X).inflation.op`. Proof: each comma category is
  `Small.{max u (v + 1) z uL}` (`small_lift`), so `AddCommGrpCat` and therefore
  `ModuleCat R` have colimits of that shape.
- `quasiEtaleInflation_hasLeftKanExtension X R F`: the corresponding left Kan extension
  (`Functor.HasLeftKanExtension.mk` with `Functor.pointwiseLeftKanExtensionUnit`).
- `quasiEtaleInverseImagePresheaf X R`, from module presheaves on `Qét(X(G))` to module
  presheaves on `TwistedOver quasiEtale X.obj.ρAut`: `inverseImagePresheafFunctor` of
  `quasiEtaleNaturalAction X`.
- `quasiEtaleInverseImagePresheafAdjunction X R`: it is left adjoint to
  `(quasiEtaleNaturalAction X).invariantFunctor R`.
- `quasiEtaleInverseImagePresheafObjIsoColimit X R E U`: the value of the inverse image
  presheaf of `E` at an object `U` of the twisted site is the colimit of `E(V)` over
  `CostructuredArrow (quasiEtaleNaturalAction X).inflation.op (op U)`, the pairs of an object
  `V(G)` of `Qét(X(G))` and a twisted arrow `U → V`.
- `quasiEtaleUntwisted_hasColimit X R E U`, for an object `U` of
  `QuasiEtaleSite (GSpace.forget.obj X)`: `E` composed with the projection has a colimit over
  `CostructuredArrow (toQuasiEtaleSite X).op (op U)`. Proof as above.
- `quasiEtaleInverseImagePresheafObjIsoUntwistedColimit X R E U`: the value of the inverse
  image presheaf of `E` at `ι U` is the colimit of `E(V(G))` over
  `CostructuredArrow (toQuasiEtaleSite X).op (op U)`. Its objects are the pairs of an object
  `V(G)` of `Qét(X(G))` and an arrow `U → V` over `X`. This is
  `inverseImagePresheafObjIsoUntwistedColimit` with `Ψ = toQuasiEtaleSite X`. The hypothesis
  `htw` holds by `rfl`. Since `ι` is the identity on objects, every object of the twisted site
  is of the form `ι U`.
- `twistedQuasiEtale_hasSheafify_inverseImage X R`: module sheaves on
  `twistedQuasiEtaleTopology X.obj.ρAut` have sheafification in the universe
  `max u (v + 1) z uL`. This is `twistedQuasiEtale_hasSheafify` at the universe `max z uL`,
  with `Small.{max u (v + 1) z uL} G` from `small_lift`.
- `quasiEtaleInverseImage X R`, from module presheaves on `Qét(X(G))` to module sheaves on
  `twistedQuasiEtaleTopology X.obj.ρAut`: the inverse image presheaf followed by
  sheafification (`inverseImageFunctor`).
- `quasiEtaleInverseImageAdjunction X R`:
  `quasiEtaleInverseImage X R ⊣ quasiEtaleInvariantPresheaf X R`.

Let `hX : HasImagePullbacks (EquivariantQuasiEtaleSite.toQuasiEtaleSite X)`.

- `quasiEtaleSheafInverseImage X R hX`, from module sheaves on
  `equivariantQuasiEtaleTopology X` (that is, on `X(G)_qét`) to module sheaves on
  `twistedQuasiEtaleTopology X.obj.ρAut`: `sheafInverseImageFunctor`, using
  `quasiEtaleToTwisted_isContinuous X hX`.
- `quasiEtaleSheafInverseImageAdjunction X R hX`:
  `quasiEtaleSheafInverseImage X R hX ⊣ quasiEtaleInvariantSheaf X R hX`, the left adjoint of
  `F ↦ (b_*F)^G`.

## Étale

The étale declarations repeat the quasi-étale ones with `EquivariantEtaleSite X`,
`etaleNaturalAction X`, `toEtaleSite X`, `EtaleSite (GSpace.forget.obj X)`,
`TwistedOver etale X.obj.ρAut`, `twistedEtaleTopology X.obj.ρAut`,
`equivariantEtaleTopology X`, `etaleInvariantPresheaf X R` and `etaleInvariantSheaf X R hX`:

- `etaleInflation_hasPointwiseLeftKanExtension`, `etaleInflation_hasLeftKanExtension`;
- `etaleInverseImagePresheaf X R`, `etaleInverseImagePresheafAdjunction X R`,
  `etaleInverseImagePresheafObjIsoColimit X R E U`;
- `etaleUntwisted_hasColimit X R E U` and
  `etaleInverseImagePresheafObjIsoUntwistedColimit X R E U`, for `U` an object of
  `EtaleSite (GSpace.forget.obj X)`;
- `twistedEtale_hasSheafify_inverseImage X R`;
- `etaleInverseImage X R` with `etaleInverseImageAdjunction X R`
  (`etaleInverseImage X R ⊣ etaleInvariantPresheaf X R`);
- for `hX : HasImagePullbacks (EquivariantEtaleSite.toEtaleSite X)`,
  `etaleSheafInverseImage X R hX` with `etaleSheafInverseImageAdjunction X R hX`
  (`etaleSheafInverseImage X R hX ⊣ etaleInvariantSheaf X R hX`).

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`).
Printed page numbers equal PDF page numbers.

- Example 1.1.3, printed p.3: "Let `X` be a `G`-space. In what follows we'll use the
  following two morphisms `a : X(G^d) → X(G)` and `b : X → X(G)`, where `G^d` denotes the
  group `G` endowed with the discrete topology and `X = X({1})`."
- §1.2, printed p.3: "For a morphism `Y(H) → X(G)`, let `C(Y(H)/X(G))` denote the category of
  morphisms `Y(H) → V(G)` over `X(G)`, where `V` is quasi-étale (resp. étale) over `X`. Then
  `ϕ^*F` is the sheaf associated with the presheaf
  `(U'(G') → X'(G')) ↦ ϕ_pF(U'(G')) := lim→ F(V(G))`, where the limit is taken over the dual
  category `C(U'(G')/X(G))°`."
- Proof of Theorem 1.4.2, step A.4, printed p.9: "we can define a sheaf `(b_*F)^G` on
  `X(G)~_qét` by `(b_*F)^G(V(G)) = F(V)^G`. We claim that `b^*((b_*F)^G) ⥲ F`." Step A.5,
  printed p.9: "For `E ∈ X(G)~_qét` one has `E ⥲ (b_*b^*E)^G`." Steps B.1–B.3, printed p.9,
  treat the étale topology.

## Provenance and correspondence

Derived. For `ϕ = b`, an object of `C(U/X(G))` is an object `V(G)` of `Qét(X(G))` with a
morphism `U({1}) → V(G)` over `X(G)`, that is, an arrow `U → V` over `X`. A morphism of
`C(U/X(G))` is a morphism `V(G) → V'(G)` over `X(G)`, that is, a `G`-morphism over `X`
compatible with the arrows from `U`. So `C(U/X(G))°` corresponds to
`CostructuredArrow (toQuasiEtaleSite X).op (op U)`, and
`quasiEtaleInverseImagePresheafObjIsoUntwistedColimit` gives Berkovich's presheaf `b_pE` on
objects. The category `Anop` of §1.1 is not in the Library, so this correspondence is
informal.

The construction differs from Berkovich's in two ways. First, it is defined as the left
adjoint of the invariant sections, and Berkovich's colimit formula is then proved. Second, the
inverse image presheaf lives on the twisted site, so the action of `G` on it comes from the
Kan extension, and sheafification happens on the twisted site. Berkovich sheafifies on
`X_qét` and then obtains the `G`-action from the morphisms of §1.1. The unit and counit of
the adjunctions have the shape of the maps `E → (b_*b^*E)^G` and `b^*((b_*F)^G) → F` of steps
A.4–A.5.

Not claimed:

- that `b^*E` is a discrete (resp. smooth) `G`-sheaf (steps A.1–A.3 and B.1);
- that sheafification on the twisted site agrees with sheafification on `X_qét`;
- Theorem 1.4.2, that is, that the unit and counit are isomorphisms;
- the image pullback hypothesis `hX`, which stays an explicit argument (see
  `AnalyticInvariantSheaf.md`).
