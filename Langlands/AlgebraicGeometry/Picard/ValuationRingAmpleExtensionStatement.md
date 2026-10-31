# Ample line bundles on the generic fibre of an abelian scheme over a valuation ring

`Langlands.AbelianScheme.ValuationRingAmpleExtensionStatement.{u}` is a
universe-polymorphic definition of type `Prop`. Let `R` be a valuation domain
with fraction field `K`, and let `A` be an abelian scheme over `Spec R`. If the
generic fibre of `A` has an ample line bundle, then some line bundle on the
total space of `A` restricts to an ample line bundle on the generic fibre. This
module only defines the proposition. It does not prove it, and it adds no
axiom.

Worker 712 implemented this pair. Worker 1031 specified the exact Lean
statement, the source and the specializations in the task contract of task
`469d3df1-468d-41cc-bbec-02aa3e4fab79`.

## Exact statement

The checked declaration, in namespace `Langlands.AbelianScheme` with
`CategoryTheory`, `CategoryTheory.Limits`, `AlgebraicGeometry` and
`Langlands.AlgebraicGeometry.Picard` open, is

```lean
def ValuationRingAmpleExtensionStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (A : AbelianScheme (Spec (CommRingCat.of R))),
    (∃ L : LineBundle (pullback A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
        L.IsAmple) →
      ∃ M : LineBundle A.X.left,
        ((LineBundle.pullback
          (pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj M).IsAmple
```

This is the body displayed in the task objective, unchanged. Only the
docstring and the module documentation were added. `lean_check` in
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` reports no errors or
warnings and confirms that the declaration returns `Prop`, with the single
universe parameter `u`.

Below, `Spec R` abbreviates `Spec (CommRingCat.of R)`, and `ι` abbreviates
`Spec.map (CommRingCat.ofHom (algebraMap R K)) : Spec K ⟶ Spec R`.

The proposition quantifies over:

- a commutative ring `R : Type u` with `[IsDomain R]` and Mathlib's
  `[ValuationRing R]`;
- a field `K : Type u` with `[Algebra R K]` and `[IsFractionRing R K]`, so
  `K` is a fraction field of `R`;
- an abelian scheme `A : AbelianScheme (Spec R)` in the Library sense.

`A.X : Over (Spec R)` is the underlying object of the group object, so
`A.X.left` is the total scheme and `A.X.hom : A.X.left ⟶ Spec R` is the
structure morphism. `pullback A.X.hom ι` is Mathlib's pullback in
`Scheme.{u}`. It is the generic fibre `A_K = A ×_{Spec R} Spec K`, and
`pullback.fst A.X.hom ι : A_K ⟶ A.X.left` is the base-change projection.

- **Hypothesis.** Some line bundle `L : LineBundle A_K` satisfies
  `L.IsAmple`.
- **Conclusion.** Some line bundle `M : LineBundle A.X.left` has
  `((LineBundle.pullback (pullback.fst A.X.hom ι)).obj M).IsAmple`.

The conclusion does not require that `M` extends the given `L`, or that its
restriction is related to `L` at all. It asserts nothing about the closed
fibre or any other fibre, and it does not assert that `M` is ample relative
to `Spec R`.

### Library definitions used

- `Langlands.AbelianScheme` (module `Langlands.AbelianScheme.Basic`) is a
  commutative group scheme over the base, `CommGroupScheme S`, with the
  instances `Smooth X.hom`, `IsProper X.hom` and
  `GeometricallyConnected X.hom`. The group law is the actual group object
  in `Over S`, and commutativity is explicit. The published module
  `Langlands/AbelianScheme/SourceDefinition.md` explains the relation to the
  source definition of an abelian scheme (Lan, Definition 1.3.1.1, with
  commutativity from Lan, Corollary 1.3.1.7). This statement only uses the
  bundle.
- `LineBundle X` (module `Langlands.AlgebraicGeometry.Picard.LineBundle`)
  is the Library's full subcategory of actual `X.Modules` that are locally
  isomorphic to the structure sheaf.
- `LineBundle.pullback f` (module
  `Langlands.AlgebraicGeometry.Picard.LineBundlePullback`) is the Library's
  lift of `Scheme.Modules.pullback f` to line bundles.
- `LineBundle.IsAmple` (module `Langlands.AlgebraicGeometry.Picard.Ample`)
  is an absolute ampleness predicate on the scheme carrying the bundle. For
  `N : LineBundle Y`, `N.IsAmple` is

  ```text
  CompactSpace Y ∧ ∀ y : Y, ∃ n : ℕ, 1 ≤ n ∧ ∃ s : N.powSections n,
    y ∈ N.sectionOpen s ∧ IsAffineOpen (N.sectionOpen s).
  ```

  Here `N.powSections n` is the type of global sections of the actual
  tensor power `tensorPow N.obj n`, and `N.sectionOpen s` is the whole open
  on which `s` generates. That whole open must be affine. This is Stacks
  Definition 28.27.1 and EGA II 4.5.3; see
  `Langlands/AlgebraicGeometry/Picard/Ample.md`. Both the hypothesis and
  the conclusion apply it on the scheme `A_K`. `A_K` is a scheme over the
  field `K`, and for schemes over a field (an affine base) absolute
  ampleness is the same as ampleness relative to the base (Stacks Lemma
  29.38.5, tag 01VK). So on `A_K` the Library predicate agrees with
  the source's ampleness on the generic fibre.
- Mathlib's `ValuationRing R` for a domain `R` says that for all `a b : R`
  some `c` has `a * c = b` or `b * c = a`. By
  `ValuationRing.iff_isInteger_or_isInteger`, this holds exactly when every
  `x : K` has `x ∈ R` or `x⁻¹ ∈ R`. That is the characterization of
  valuation rings in Stacks Lemmas 10.50.4 and 10.50.5 (tag 00I8), so
  Mathlib's notion agrees with Stacks Definition 10.50.1 for domains.

## Scope

The statement covers every universe `u`. The valuation domain `R` has
arbitrary rank. There is no noetherian, discrete-valuation, finite-rank,
completeness, henselian, residue-characteristic or algebraic-closedness
premise on `R` or `K`. A field `R` is allowed, since Mathlib's
`ValuationRing.of_field` makes every field a valuation ring. Then `Spec R` is
a point and `A_K` is isomorphic to `A`. Every fraction field `K` of `R` is
allowed, not only a chosen one.

There is no hypothesis on `A` beyond the `AbelianScheme` bundle: no relative
dimension, polarization, projectivity, symmetry or rigidification premise.
Ampleness is assumed only on the generic fibre.

## Original source

Michel Raynaud, *Faisceaux amples sur les schémas en groupes et les espaces
homogènes*, Lecture Notes in Mathematics 119, Springer (1970). The project
copy is the second corrected printing of 1986 (PDF p.3), registered as
`provided-5d5546c6572c2556d06cb8181d9d78944bca00a4138a3ab39df0a5810f0fd485`,
SHA256 `29bce9a9be67396fd1bd8f0396e57d5ff08325eed53819e240eb14155711f38d`.
The working Library has no errata note for this source.

Théorème XI 1.4 (Grothendieck), printed p.161 (PDF p.165), read from the
rendered page image:

> Soient S un schéma intègre de point générique η, géométriquement
> unibranche (EGA IV 6.15.1), G un S-schéma abélien, L_η un faisceau
> inversible sur G_η. Alors il existe un faisceau inversible symétrique M
> sur G, tel que M_η soit algébriquement équivalent à L_η^{⊗2}. Si L_η est
> ample, M est S-ample. En particulier, G est projectif sur S.

The proof, printed pp.161–163 (PDF pp.165–167), runs as follows.

- It first derives the last assertions: "Si L_η est ample, il en est de même
  de L_η^{⊗2}, donc de M_η, qui lui est algébriquement équivalent, mais
  alors M est S-ample (VIII 7.)". So the source itself obtains ampleness of
  `M_η` on the way to `S`-ampleness of `M`.
- Lemme XI 1.5 says that under the hypotheses of XI 1.4 the map from the
  sections over `S` of the scheme `C_{G/S}` representing `Corr_S(G,G)` to
  the rational points of its generic fibre is bijective. Its proof (printed
  p.162) says the assertion is local on `S`. It then reduces "par passage à
  la limite" to `S` noetherian, writing the ring `A` of an affine `S` as the
  filtered union of the integral closures `A'_i` of its finitely generated
  `ℤ`-subalgebras `A_i` in `A ∩ K_i`, where `K_i` is the fraction field of
  `A_i`. These `A'_i` are of finite type over `ℤ` (EGA IV 7) and
  geometrically unibranch. The noetherian case follows from EGA IV
  18.10.20. So no noetherian hypothesis appears in the theorem.
- Lemme XI 1.6 (printed pp.162–163) gives a monomorphism
  `u : NS(G/S) → Corr(G ×_S G / S) ≅ Pic^{(e,e)}(G ×_S G)`. For
  `w = δ^* ∘ u`, with `δ` the diagonal, the image of `w` consists of
  symmetric sheaves and the composite `NS(G/S) → Pic^{(e)}(G) → NS(G/S)` is
  multiplication by 2. The proof of XI 1.4 (printed p.163) takes the
  rational point `a_η` of the generic fibre of `NS_{G/S}` defined by `L_η`,
  applies XI 1.6 over `Spec k(η)` to get `b_η = u(a_η)`, extends it to `b`
  over `S` by XI 1.5, and sets `M = δ^* b`. Then `M_η` is symmetric and
  algebraically equivalent to `L_η^{⊗2}`, and `M` is symmetric because
  `Pic_{G/S}` is separated.

## Derived formulation

This is a specialization and weakening of Théorème XI 1.4, not a verbatim
source statement.

### The base: `S = Spec R` for a valuation domain `R`

`S = Spec R` is integral because `R` is a domain. Its generic point `η` is
the zero ideal, with residue field the fraction field of `R`. The base
change along `ι : Spec K ⟶ Spec R` is therefore the generic fibre `G_η` up
to the canonical isomorphism of `K` with `κ(η)` over `R`. The Lean statement
uses the given fraction field `K` directly.

`S` is geometrically unibranch, as Raynaud requires:

1. The local rings of `Spec R` are the localizations `R_p`. Each is a
   valuation ring by Stacks Lemma 10.50.9 (tag 00I8), and hence a normal
   domain by Stacks Lemma 10.50.3.
2. So `Spec R` is a normal scheme in the sense of Stacks Definition 28.7.1
   (tag 033I): every local ring is a normal domain.
3. A normal scheme is geometrically unibranch by Stacks Lemma 28.16.2
   (tag 0BQ3), whose proof uses Definition 15.108.1 (tag 0BPZ): a local
   normal domain is its own integral closure, so the residue-field condition
   holds trivially. Geometric unibranchness of a scheme is Stacks Definition
   28.16.1 (tag 0BQ2), which cites EGA IV 6.15.1, the reference given by
   Raynaud.

### The abelian scheme

Raynaud's `G` is an `S`-schéma abélien. The Lean `A` is a Library
`AbelianScheme (Spec R)`: a smooth, proper, commutative group scheme with
geometrically connected fibres. The source correspondence of this bundle is
documented in `Langlands/AbelianScheme/SourceDefinition.md`. The explicit
commutativity can only restrict the objects quantified over, so it does not
strengthen the statement relative to the source.

### Hypothesis: only the ample case

Raynaud's theorem holds for every invertible sheaf `L_η` on `G_η`. The Lean
statement keeps only the ample case, as the hypothesis that some actual
line bundle on `A_K` is ample in the Library sense. This weakens the
hypothesis side of the source to a special case.

### Conclusion: ampleness of the generic restriction

Raynaud concludes that `M` is `S`-ample. The Lean conclusion asks only that
the pullback of `M` to `A_K` along `pullback.fst A.X.hom ι` is ample. This
follows from the source in two ways.

- **Through relative ampleness.** By Stacks Lemma 29.38.9 (tag 0893), the
  pullback of an `f`-ample sheaf to a base change `X' → S'` of `f : X → S`
  is ample relative to `S'`. Apply it with `S' = Spec K` and `X' = A_K`.
  Since `Spec K` is affine, Stacks Lemma 29.38.5 (tag 01VK) turns
  ampleness relative to `Spec K` into absolute ampleness on `A_K`.
- **Directly from the proof.** Raynaud's proof shows that `M_η` is ample
  because it is algebraically equivalent to the ample `L_η^{⊗2}`.

Raynaud's `M_η` is the restriction of `M` to the generic fibre, which the
Library renders as `LineBundle.pullback` along the base-change projection.

### Dropped parts

The following parts of the source are dropped from the conclusion:

- the symmetry of `M`;
- the algebraic equivalence of `M_η` with `L_η^{⊗2}`, and with it any
  relation between `M` and the given `L`;
- the `S`-ampleness of `M` itself;
- the projectivity of `G` over `S`.

The Lean statement also does not ask for `M` to extend `L`. The consumer
described below needs only some ample line bundle on the generic fibre that
extends over `A`.

## Role in the project

Worker 1031 published this statement as a prerequisite of the exact-target
proof task `322a2874-8b1c-4e61-b7cc-e0d154742640`, which proves
`Langlands.AbelianScheme.PicardZeroValuativeExtensionStatement`. That task
in turn serves Worker 302's task `54d4a7cc-7607-4c5a-82e7-25bafba9e3e9`. On
Worker 1031's route, the line bundle `M` supplied here, passed to a
valuation ring dominating `R` in an algebraic closure of `K`, feeds the
Mumford-bundle construction. Any ample line bundle on the generic fibre
suffices, because the translation-difference lifting is applied afterwards
to the restriction of `M`.

## Reading record

- Raynaud, LNM 119, rendered page images of PDF pp.164–167 (printed
  pp.160–163): Remarque XI 1.3, Théorème XI 1.4, its proof, Lemmes XI 1.5
  and XI 1.6. The text extraction of these pages is noisy, so the quotations
  above come from the images.
- Registered source `stacks-valuation-normal-unibranch-2026-10-30`,
  directory SHA256
  `40f8c93a80878a062eb4bf6387a8f76f9843c43cadcb38ec84d6bac9c5ea3f8c`, at
  `literature/Stacks Project - Valuation rings, normal schemes and geometric unibranchness (HTML snapshot 2026-10-30)`.
  Worker 712 read `00I8.html` (Section 10.50, Definition 10.50.1 and
  Lemmas 10.50.3, 10.50.4, 10.50.5 and 10.50.9 with proofs), `06DT.html`
  (Section 15.108), `0BPZ.html` (Definition 15.108.1), `0BQ1.html`
  (Section 28.16), `0BQ2.html` (Definition 28.16.1) and `0BQ3.html`
  (Lemma 28.16.2 and its proof). The five comments on Section 10.50 concern
  typesetting and the arrangement of Lemmas 10.50.4 and 10.50.5. The two
  comments on Section 15.108 concern étale neighbourhoods with
  geometrically unibranch components. Section 28.16 and the individual
  tags have no comments. None affects the results used here. The
  registration's citation string labels tag `0BPZ` as "Lemma 15.108.5";
  the retained page is Definition 15.108.1, as cited here.
- Registered source `stacks-normal-scheme-domain-stalk-definitions-2026-10-25`,
  directory SHA256
  `4b962e26e7516ff782a6f7b146df1c0c9972c10ecdbf685912db247b39209e79`,
  file `033I.html` (Definition 28.7.1).
- Registered source `stacks-field-base-change-ampleness-2026-10-26`,
  directory SHA256
  `42e3c9b9a073a223fab83518d24f49215baffa88c4eb11c2f72a0a95cec4ac17`,
  files `01VK.html` (Lemma 29.38.5) and `0893.html` (Lemma 29.38.9). These
  were read in full with their comments for the published
  `Langlands/AlgebraicGeometry/Picard/FieldBaseChangeAmpleStatement.md`.

## Proof obligations for the future exact-target proof

A proof must work with the Library definitions above and add no outer
hypothesis. The source gives no Lean construction of the following, among
others:

1. The limit reduction to a noetherian geometrically unibranch base, or a
   substitute, including spreading out `A` and the given bundle over a
   finite-type model of `R`.
2. The scheme `C_{G/S}` of divisorial correspondences, Lemme XI 1.5
   (extension of rational points over a geometrically unibranch base via
   EGA IV 18.10.20), and Lemme XI 1.6 on the Néron–Severi map.
3. The passage from the source's `M_η`, or from `S`-ampleness, to the
   Library predicate `LineBundle.IsAmple` on the Mathlib pullback `A_K`.
   This includes a comparison of actual tensor powers with pullbacks and of
   the whole generation open, as in the obligations listed in
   `Langlands/AlgebraicGeometry/Picard/FieldBaseChangeAmpleStatement.md`.

This module discharges none of these obligations.
