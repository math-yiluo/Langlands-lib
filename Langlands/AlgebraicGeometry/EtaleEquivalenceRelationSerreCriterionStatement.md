# Serre's criterion for affine quotients of étale equivalence relations

Authors: Worker 239, Worker 712.

This module states that an étale equivalence relation `E` on a Noetherian
affine scheme `E.U`, whose relation scheme `E.R` is affine, whose map
`j = (t, s) : E.R ⟶ E.U × E.U` is a closed immersion, and all of whose
modules on the groupoid are acyclic in the ring form of the Library module
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelationComodule`, has an affine
quotient. It uses the Library structure
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelation`, its predicate
`HasAffineQuotient`, and the predicate
`EtaleEquivalenceRelation.ComodulesAcyclic` of the comodule module, all
unchanged. It also uses the Mathlib classes `AlgebraicGeometry.IsClosedImmersion`
(`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`) and
`AlgebraicGeometry.IsNoetherian` (`Mathlib.AlgebraicGeometry.Noetherian`).
The module states the proposition and supplies no proof.

## Formula and quantifiers

The declaration is
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelationSerreCriterionStatement.{u}`.
Its defining formula is

```lean
def EtaleEquivalenceRelationSerreCriterionStatement : Prop :=
  ∀ E : EtaleEquivalenceRelation.{u}, IsAffine E.U → IsNoetherian E.U → IsAffine E.R →
    IsClosedImmersion (prod.lift E.t E.s) → E.ComodulesAcyclic → E.HasAffineQuotient
```

The universe `u` is arbitrary. The quantifier ranges over every étale
equivalence relation `E` with schemes in `Scheme.{u}`, absolute over
`Spec ℤ`.

- `IsAffine E.U`, `IsNoetherian E.U`, `IsAffine E.R` and
  `IsClosedImmersion (prod.lift E.t E.s)` are as in
  `EtaleEquivalenceRelationComodulesAcyclicStatement`: the schemes `E.U`
  and `E.R` are affine, the ring `Γ(E.U, ⊤)` is Noetherian, and
  `j = (t, s)` into the product over `Spec ℤ` is a closed immersion.
- `E.ComodulesAcyclic`, with `B = Γ(E.U, ⊤)`, `C = Γ(E.R, ⊤)`, `C` a
  `B`-algebra through `E.s.appTop` and target ring map `E.t.appTop.hom`,
  says that for every module `θ` on the groupoid with underlying `B`-module
  in `Type u`, and every short exact sequence `0 → M → G → Q → 0` of such
  modules with first term `θ`, every invariant element of `Q` lifts to an
  invariant element of `G`. The Markdown of
  `EtaleEquivalenceRelationComodule` describes these definitions.
- `E.HasAffineQuotient` is the Library predicate: there are an affine
  scheme `M` and a flat, locally finitely presented, surjective morphism
  `q : E.U ⟶ M` such that `IsPullback E.t E.s q q`, that is, `(t, s)`
  identifies `E.R` with `E.U ×_M E.U`.

## Original source and correspondence

The statement is derived: it is not stated in this form in the literature.
It is the comodule form of Serre's criterion for algebraic spaces, Stacks
Proposition 69.16.7 (Tag 07V6), for the quotient `Y = E.U/E.R`. The sources
are:

- `stacks-serre-criterion-algebraic-spaces-2026-11-01` (directory SHA-256
  `87667c307924301da4b8d890a4cd77f1dbee3773a5130a698624e661014c8e5e`):
  `07V6.html` (Proposition 69.16.7: every algebraic space as in
  Situation 69.16.1 is an affine scheme), `07UX.html` (Situation 69.16.1:
  `X` is a quasi-compact and quasi-separated algebraic space with
  `H^1(X, F) = 0` for every quasi-coherent `O_X`-module `F`), `03M3.html`
  (Proposition 66.32.1, the equivalence `F ↦ (φ^*F, α)` between
  quasi-coherent `O_X`-modules and quasi-coherent modules on the groupoid of
  a presentation), `073H.html` (Lemma 69.8.2: `R^i f_* F = 0` for `i > 0`,
  `f` affine and `F` quasi-coherent), `01XB.html` (Lemma 30.2.2) and
  `03DW.html` (Proposition 35.9.3), the last two as in the Markdown of
  `EtaleEquivalenceRelationComodulesAcyclicStatement`.
- `stacks-serre-criterion-supplement-2026-11-01` (directory SHA-256
  `cbea68ccfedf005875025bafa4dda54d8886e6f5410724a4dfbb73b9bb6b207c`):
  `03WD.html` (Section 67.20: Definition 67.20.2 of affine morphisms;
  Lemma 67.20.10: for an affine morphism `f : Y → X` and `A = f_* O_Y`,
  `f_*` is an equivalence from quasi-coherent `O_Y`-modules to
  quasi-coherent `A`-modules, and an `A`-module is quasi-coherent as an
  `A`-module if and only if it is quasi-coherent as an `O_X`-module; in
  particular `f_*` takes quasi-coherent modules to quasi-coherent modules;
  Lemma 67.20.11 (4): a morphism from an
  affine scheme to a separated algebraic space is affine), `0733.html`
  (Lemma 21.14.6 (1): if `R^q f_* F = 0` for `q > 0`, then
  `H^p(F) = H^p(f_* F)` for all `p`) and `03M1.html` (Lemma 66.29.7 (3):
  kernels and cokernels of maps of quasi-coherent modules are
  quasi-coherent).
- `stacks-finite-flat-groupoid-quotient-2026-11-01` (directory SHA-256
  `04098502d60fbca6624b86128e0360936b8a62bff64fa4765db553d0f7466304`):
  `03BS.html` (Definition 66.3.1: an algebraic space over `Spec ℤ` is
  separated if its diagonal is a closed immersion, quasi-separated if its
  diagonal is quasi-compact) and `0AHS.html` (Lemma 66.3.4 and its proof).
- `stacks-coherent-spaces-cohomology-2026-11-01` (directory SHA-256
  `4f4e8706f5e8349c8c7082d80cd5f92c788d4ccdcf93b6a2aec60e48b6e9126e`):
  `07UA.html` (Definition 69.12.1: coherent modules on a locally Noetherian
  algebraic space), `07UB.html` (Lemma 69.12.2: such a module is coherent if
  and only if it is quasi-coherent of finite type, if and only if its
  pullback to every scheme étale over the space is coherent), `07UV.html`
  (Lemma 69.15.1: on a Noetherian algebraic space every quasi-coherent module
  is the filtered colimit of its coherent submodules) and `073E.html`
  (Lemma 69.5.1: on a quasi-compact and quasi-separated algebraic space,
  cohomology commutes with filtered colimits).
- `stacks-noetherian-space-affine-descent-2026-11-01` (directory SHA-256
  `6a433fc04ce2561e2cd3cf5f19526887b8fe5ba9b2db5201025e80104df2e6b1`):
  `03E2.html` (Definition 66.5.1: quasi-compact algebraic spaces),
  `03E5.html` (Lemma 66.7.1 and Definition 66.7.2: an algebraic space is
  locally Noetherian if a scheme étale and surjective over it is),
  `03EA.html` (Definition 66.24.1: Noetherian means quasi-compact,
  quasi-separated and locally Noetherian) and `07VP.html` (the first
  paragraph of the proof of Lemma 69.17.3, which deduces the vanishing of
  `H^1` for quasi-coherent modules from that for coherent modules by
  Lemmas 69.15.1 and 69.5.1).
- `stacks-etale-equivalence-relations-2026-11-01` (directory SHA-256
  `df1ecbfa63c5e31cf736d9ea79dd262976c3098fd9b36f2dd32668d44bf75420`):
  `02WW.html` (Theorem 65.10.5) and `03C5.html` (Lemma 39.20.3), used as in
  the Markdown of `EtaleEquivalenceRelationAffineDescentStatement`.
- `stacks-groupoid-schemes-chapter-pdf-2026-07-14` (file SHA-256
  `4506a39201063afc270cbb68c9c0c1d3c90937c03f98cfee074605b402e7a30f`):
  Definition 39.14.1 (Tag 03LI) and Lemma 39.14.6 (Tag 077S), used as in the
  Markdown of `EtaleEquivalenceRelationComodule`.

The correspondence, which this module does not formalize, is as follows.

1. Let `φ : U → Y` be the étale surjection from `U = E.U`, so that
   `R = E.R = U ×_Y U` with `t` and `s` the two projections (`02WW`). The
   algebraic space `Y` is quasi-compact by Definition 66.5.1 (`03E2`), since
   `U` is affine.
2. `Y` is separated. The proof of (2) ⇒ (1) in Lemma 66.3.4 (`0AHS`) shows
   that `Y` is separated as soon as, for one scheme `W` with a surjective
   étale morphism `W → Y`, the morphism
   `j : W ×_Y W = Y ×_{Y × Y} (W × W) → W × W` is a closed immersion. For
   `W = U` this is `j = (t, s) : R → U × U`, a closed immersion by
   hypothesis. As a closed immersion is quasi-compact, `Y` is also
   quasi-separated (`03BS`).
3. `Y` is Noetherian. It is locally Noetherian by Lemma 66.7.1 and
   Definition 66.7.2 (`03E5`), since `U` is a Noetherian scheme étale and
   surjective over `Y`. With steps 1 and 2 it is Noetherian by
   Definition 66.24.1 (`03EA`).
4. `φ` is affine by Lemma 67.20.11 (4) (`03WD`), as `U` is an affine scheme
   and `Y` is separated.
5. Let `F` be a coherent `O_Y`-module (Definition 69.12.1, `07UA`) and set
   `G = φ_* φ^* F`. It is quasi-coherent by Lemma 67.20.10, since `φ` is
   affine. The unit `F → G` is injective: over an object `V` of the étale
   site of `Y` it is the restriction map of `F` along the étale covering
   `{U ×_Y V → V}`. Its cokernel `Q` is quasi-coherent by `03M1`.
6. `H^1(Y, G) = 0`. By Lemma 69.8.2 (`073H`), `R^q φ_* (φ^* F) = 0` for
   `q > 0`, so `H^1(Y, G) = H^1(U, φ^* F)` by Lemma 21.14.6 (1) (`0733`).
   The latter vanishes because `U` is an affine scheme (`03DW` and `01XB`).
   The long exact cohomology sequence of `0 → F → G → Q → 0` thus makes
   `H^1(Y, F)` the cokernel of `Γ(Y, G) → Γ(Y, Q)`.
7. The sections over `U` lie in universe `u`. `E.ComodulesAcyclic` only
   concerns modules whose underlying type is in `Type u`, the universe of
   `B` and `C`. By Lemma 69.12.2 (`07UB`), `φ^*F` is a coherent module on the
   Noetherian affine scheme `U = Spec B`, so `M_F = Γ(U, φ^*F)` is a finitely
   generated `B`-module, isomorphic to a quotient of some `B^n` and hence to a
   module in `Type u`. The sections `Γ(U, φ^*G) = G(U)` are the sections
   over `U ×_Y U = R` of the pullback of `φ^*F` along one of the projections
   `R → U`. As `R = Spec C` is affine, they form `C ⊗_B M_F` for the
   corresponding algebra structure, again in `Type u`. Pullback along the
   étale `φ` is exact and `Γ(U, -)` is exact on quasi-coherent modules on
   the affine `U` (`01XB`), so `Γ(U, φ^*Q)` is the quotient of `Γ(U, φ^*G)`
   by the image of `M_F`, also in `Type u`.
8. `Γ(Y, G) → Γ(Y, Q)` is surjective. By the exactness in step 7,
   `0 → φ^*F → φ^*G → φ^*Q → 0` is exact, and with the maps `α` of
   Proposition 66.32.1 (`03M3`) it is a short exact sequence of modules on
   the groupoid. Taking sections over `U` gives a short exact sequence of
   `B`-modules, which by step 7 may be replaced by isomorphic modules in
   `Type u`. With `R = Spec C`, the ring form statement
   `EtaleEquivalenceRelationRingFormStatement` and the Markdown of
   `EtaleEquivalenceRelationComodule` translate it into
   `GroupoidCoaction E.t.appTop.hom` structures and maps satisfying `IsHom`,
   the first injective, the second surjective, with range equal to kernel.
   By `E.ComodulesAcyclic` every invariant element of the third term lifts
   to an invariant element of the second. As in step 4 of the Markdown of
   `EtaleEquivalenceRelationComodulesAcyclicStatement`, the invariant
   elements of the ring form of `(φ^*F, α)` are the global sections
   `Γ(Y, F)`, compatibly with morphisms. So `Γ(Y, G) → Γ(Y, Q)` is
   surjective and `H^1(Y, F) = 0` by step 6.
9. `H^1(Y, F) = 0` for every quasi-coherent `O_Y`-module `F`. As in the
   first paragraph of the proof of Lemma 69.17.3 (`07VP`), this follows from
   step 8: on the Noetherian `Y` every quasi-coherent module is the filtered
   colimit of its coherent submodules (Lemma 69.15.1, `07UV`), and on the
   quasi-compact and quasi-separated `Y` cohomology commutes with filtered
   colimits (Lemma 69.5.1, `073E`).
10. By steps 1, 2 and 9, `Y` is as in Situation 69.16.1 (`07UX`, with base
    `S = Spec ℤ`). By Proposition 69.16.7 (`07V6`), `Y` is an affine scheme.
    As in the Markdown of `EtaleEquivalenceRelationAffineDescentStatement`,
    `φ : U → Y` is then étale and surjective, hence flat, locally of finite
    presentation and surjective, and `R = U ×_Y U`. So `M = Y` and `q = φ`
    witness `E.HasAffineQuotient`.

So the statement is a consequence of Proposition 69.16.7. The argument uses
the hypothesis that `E.U` is Noetherian only in steps 3, 7 and 9, to reduce
to coherent modules, whose sections over `U` lie in universe `u`. The
hypothesis `IsAffine E.R` also follows from the closed immersion `j` and
`IsAffine E.U`.

## Scope and role

This statement belongs to the planned proof of
`NoetherianEtaleEquivalenceRelationAffineDescentStatement` (Lemma 69.17.3,
Tag 07VP, for presentations), whose proof in Stacks ends with
Proposition 69.16.7. Together with
`EtaleEquivalenceRelationAffineRelationStatement` and
`EtaleEquivalenceRelationComodulesAcyclicStatement` it gives that
statement. The planned proof works on the ring form: it constructs the
quotient ring from invariants and uses the Noetherian hypothesis, instead of
the cohomology of algebraic spaces. The proof is a separate unit.
