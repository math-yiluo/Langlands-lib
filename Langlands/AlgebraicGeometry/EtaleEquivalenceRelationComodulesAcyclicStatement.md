# Acyclicity of modules on a finitely covered Noetherian étale equivalence relation

Authors: Worker 239, Worker 712.

This module states that an étale equivalence relation `E` on a Noetherian
affine scheme `E.U`, whose relation scheme `E.R` is affine, whose map
`j = (t, s) : E.R ⟶ E.U × E.U` is a closed immersion, and which has a finite
surjective cartesian cover by an étale equivalence relation with an affine
quotient, has only acyclic modules on its groupoid, in the ring form of the
Library module `Langlands.AlgebraicGeometry.EtaleEquivalenceRelationComodule`.
It uses the Library structure
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelation`, its predicate
`HasFiniteSurjectiveCoverWithAffineQuotient`, and the predicate
`EtaleEquivalenceRelation.ComodulesAcyclic` of the comodule module, all
unchanged. It also uses the Mathlib classes `AlgebraicGeometry.IsClosedImmersion`
(`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`) and
`AlgebraicGeometry.IsNoetherian` (`Mathlib.AlgebraicGeometry.Noetherian`).
The module states the proposition and supplies no proof.

## Formula and quantifiers

The declaration is
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelationComodulesAcyclicStatement.{u}`.
Its defining formula is

```lean
def EtaleEquivalenceRelationComodulesAcyclicStatement : Prop :=
  ∀ E : EtaleEquivalenceRelation.{u}, IsAffine E.U → IsNoetherian E.U → IsAffine E.R →
    IsClosedImmersion (prod.lift E.t E.s) →
      E.HasFiniteSurjectiveCoverWithAffineQuotient → E.ComodulesAcyclic
```

The universe `u` is arbitrary. The quantifier ranges over every étale
equivalence relation `E` with schemes in `Scheme.{u}`, absolute over
`Spec ℤ`.

- `IsAffine E.U` and `IsAffine E.R` are Mathlib's absolute affineness of the
  two schemes. `IsNoetherian E.U` is Mathlib's Noetherian scheme (locally
  Noetherian and quasi-compact); for the affine `E.U` it says that the ring
  `Γ(E.U, ⊤)` is Noetherian.
- `prod.lift E.t E.s : E.R ⟶ E.U ⨯ E.U` is `j = (t, s)` into the categorical
  product of schemes, the fibre product over `Spec ℤ`, and
  `IsClosedImmersion` is Mathlib's class of closed immersions.
- `E.HasFiniteSurjectiveCoverWithAffineQuotient` is the Library predicate:
  there are an étale equivalence relation `E'` with
  `E'.HasAffineQuotient` and a cartesian morphism `(f, g) : E' ⟶ E` with
  `f : E'.U ⟶ E.U` finite and surjective.
- `E.ComodulesAcyclic` takes `B = Γ(E.U, ⊤)` and `C = Γ(E.R, ⊤)`, with `C` a
  `B`-algebra through `E.s.appTop` and target ring map `E.t.appTop.hom`. It
  says that every `GroupoidCoaction E.t.appTop.hom M` on a `B`-module
  `M : Type u` is acyclic: for every short exact sequence
  `0 → M → G → Q → 0` of modules on the groupoid (`G Q : Type u`, maps that
  are morphisms of such modules, the first injective, the second surjective,
  with range of the first equal to the kernel of the second), every
  invariant element of `Q` is the image of an invariant element of `G`.
  The Markdown of `EtaleEquivalenceRelationComodule` describes these
  definitions.

The hypotheses `IsAffine E.R` and `IsClosedImmersion (prod.lift E.t E.s)`
follow from `IsAffine E.U` and the cover hypothesis by the published
statement `EtaleEquivalenceRelationAffineRelationStatement`. They are stated
explicitly so that `(Γ(E.U, ⊤), Γ(E.R, ⊤), s, t)` is the ring form of `E` by
the hypotheses alone (statement `EtaleEquivalenceRelationRingFormStatement`),
with the same hypotheses as the Serre criterion statement
`EtaleEquivalenceRelationSerreCriterionStatement`.

## Original source and correspondence

The statement is derived: it is not stated in this form in the literature.
It is the comodule form of the first claim in the proof of Stacks
Lemma 69.17.3 (Tag 07VP): `H^1` of every quasi-coherent module on the
Noetherian target vanishes. Lemma 69.17.3 writes the finite surjective
morphism as `f : Y → X` with `X` Noetherian. Below, as in the Library
statements, `Y = E.U/E.R` is the target and `X = E'.U/E'.R` the source. The
sources are:

- `stacks-noetherian-space-affine-descent-2026-11-01` (directory SHA-256
  `6a433fc04ce2561e2cd3cf5f19526887b8fe5ba9b2db5201025e80104df2e6b1`):
  `07VP.html`, Lemma 69.17.3 and its proof. The first paragraph of the proof
  says that it shows `H^1(X, F) = 0` for every coherent module, deduces the
  same for every quasi-coherent module (Lemmas 69.15.1 and 69.5.1), and then
  concludes with Proposition 69.16.7. Also `03EA.html`, `03E2.html`,
  `03E5.html` and `05Z2.html`, used as in the Markdown of
  `NoetherianEtaleEquivalenceRelationAffineDescentStatement`.
- `stacks-algebraic-space-affine-descent-2026-11-01` (directory SHA-256
  `10fa51455958afc737851009364630c6f8e05ff49d790473a03fa1baaa4c00a0`):
  `07VQ.html`, first paragraph of the proof of Lemma 70.15.1, used as in that
  Markdown.
- `stacks-etale-equivalence-relations-2026-11-01` (directory SHA-256
  `df1ecbfa63c5e31cf736d9ea79dd262976c3098fd9b36f2dd32668d44bf75420`):
  `02WW.html` (Theorem 65.10.5: `U/R` is an algebraic space, `U → U/R` is
  étale and surjective, and `R = U ×_{U/R} U`), `03C5.html` (Lemma 39.20.3)
  and `07S3.html` (Lemma 39.20.7), used as in the Markdown of
  `EtaleEquivalenceRelationAffineDescentStatement`.
- `stacks-serre-criterion-algebraic-spaces-2026-11-01` (directory SHA-256
  `87667c307924301da4b8d890a4cd77f1dbee3773a5130a698624e661014c8e5e`):
  `03M3.html` (Proposition 66.32.1: for a surjective étale `φ : U → X` from a
  scheme with `R = U ×_X U`, `F ↦ (φ^*F, α)` is an equivalence between
  quasi-coherent `O_X`-modules and quasi-coherent modules on the groupoid
  `(U, R, s, t, c)`), `01XB.html` (Lemma 30.2.2: quasi-coherent modules have
  no higher cohomology on affine schemes) and `03DW.html`
  (Proposition 35.9.3: the cohomology of a quasi-coherent module on a scheme
  is the same on the Zariski and the étale site).
- `stacks-serre-criterion-supplement-2026-11-01` (directory SHA-256
  `cbea68ccfedf005875025bafa4dda54d8886e6f5410724a4dfbb73b9bb6b207c`):
  `03M1.html` (Lemma 66.29.7 (3): kernels and cokernels of maps of
  quasi-coherent modules on an algebraic space are quasi-coherent).
- `stacks-groupoid-schemes-chapter-pdf-2026-07-14` (Groupoid Schemes chapter,
  file SHA-256
  `4506a39201063afc270cbb68c9c0c1d3c90937c03f98cfee074605b402e7a30f`):
  Definition 39.14.1 (Tag 03LI, PDF p.28), Lemma 39.14.2 (Tag 077Q) and
  Lemma 39.14.6 (Tag 077S, PDF p.29: with `s`, `t` flat the modules on a
  groupoid form an abelian category, with kernels and cokernels formed on
  the underlying modules on `U`).

The correspondence, which this module does not formalize, is as follows.

1. Let `φ : U → Y` be the étale surjection from `U = E.U`, so that
   `R = E.R = U ×_Y U` with `t` and `s` the two projections (`02WW`). As in
   the Markdown of `NoetherianEtaleEquivalenceRelationAffineDescentStatement`,
   `Y` is a Noetherian algebraic space. As in the Markdown of
   `EtaleEquivalenceRelationAffineDescentStatement`, `X` is an affine scheme
   and `X → Y` is finite and surjective. So Lemma 69.17.3 applies. Its proof
   first shows `H^1(Y, F) = 0` for every quasi-coherent `O_Y`-module `F`.
   This vanishing also follows from the conclusion that `Y` is an affine
   scheme, by `03DW` and `01XB`.
2. Write `U = Spec B` and `R = Spec C`. By the ring form statement and the
   Markdown of `EtaleEquivalenceRelationComodule`, a
   `GroupoidCoaction E.t.appTop.hom M` is a quasi-coherent module on the
   groupoid `(U, R, s, t, c)` in the sense of Definition 39.14.1, with
   underlying `B`-module `M`, and `IsHom` describes its morphisms. The map
   `α` is then an isomorphism by Lemma 39.14.2. By Proposition 66.32.1
   (`03M3`) every such module is isomorphic to `(φ^*F, α)` for a
   quasi-coherent `O_Y`-module `F`, unique up to isomorphism, with
   `M ≅ Γ(U, φ^*F)`.
3. Exactness. The modules on the groupoid form an abelian category in which
   kernels and cokernels are formed on the underlying modules on `U`
   (`077S`). Since `U` is affine, this is the same as forming them on the
   underlying `B`-modules. The quasi-coherent `O_Y`-modules form an abelian
   category whose kernels and cokernels are those of `O_Y`-modules (`03M1`).
   An equivalence of abelian categories preserves kernels and cokernels.
   So a sequence `0 → M → G → Q → 0` as in `IsAcyclic` corresponds to a
   short exact sequence `0 → F_M → F_G → F_Q → 0` of quasi-coherent
   `O_Y`-modules.
4. Invariants are global sections. Let `F` be quasi-coherent on `Y` and
   `M = Γ(U, φ^*F)`. The sheaf condition for the étale covering
   `{φ : U → Y}`, with `U ×_Y U = R`, identifies `Γ(Y, F)` with the
   equalizer of the two maps from `M` to the sections over `R` of the
   pullback of `F` along `φ ∘ t = φ ∘ s`. As `R` is affine, these sections are
   `C ⊗_{t,B} M` and `C ⊗_{s,B} M` before and after the identification `α`.
   The two maps become `m ↦ α (1 ⊗ m) = θ m` and `m ↦ 1 ⊗ m`. So `Γ(Y, F)` is
   the subgroup `θ.invariants`, compatibly with morphisms.
5. The long exact cohomology sequence of step 3 contains
   `Γ(Y, F_G) → Γ(Y, F_Q) → H^1(Y, F_M)`, and `H^1(Y, F_M) = 0` by step 1.
   So `Γ(Y, F_G) → Γ(Y, F_Q)` is surjective, which by step 4 says that every
   invariant element of `Q` lifts to an invariant element of `G`. This is
   `IsAcyclic`.

So the statement is a consequence of Lemma 69.17.3.

The restriction to modules in `Type u` needs no extra step here.
`E.ComodulesAcyclic` only asks about modules `M`, `G` and `Q` whose
underlying types lie in `Type u`, the universe of `B` and `C`. Steps 2 to 5
use no size condition on the modules: they apply to modules on the groupoid
of any size, and the modules in `Type u` are a special case. So the
restriction only weakens the conclusion and is never used. (The Serre
criterion statement uses `E.ComodulesAcyclic` as a hypothesis and must
handle the restriction; its Markdown explains how.)

## Scope and role

This statement belongs to the planned proof of
`NoetherianEtaleEquivalenceRelationAffineDescentStatement` (Lemma 69.17.3
for presentations). That statement follows from three statements:
`EtaleEquivalenceRelationAffineRelationStatement` gives `IsAffine E.R` and
the closed immersion `j`, this statement gives `E.ComodulesAcyclic`, and
`EtaleEquivalenceRelationSerreCriterionStatement` gives `E.HasAffineQuotient`.
The correspondence above derives this statement from Lemma 69.17.3 itself,
so it is not a proof route for that lemma. The planned proof works on the
ring form instead and follows the dévissage over coherent modules in the
proof of Lemma 69.17.3, using the Noetherian hypothesis. The statement
without that hypothesis is also true, by Lemma 70.15.1 (Tag 07VS) in place of
Lemma 69.17.3, but it is not needed. The proof is a separate unit.
