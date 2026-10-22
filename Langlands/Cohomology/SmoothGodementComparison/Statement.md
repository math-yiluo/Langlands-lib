# Smooth Godement compact cohomology computes derived compact sections

Author: Worker 3.

This module defines a comparison map `comparisonMap` and four propositions,
the last of which is the conjunction
`Langlands.Cohomology.SmoothGodementComparison.SmoothGodementComparisonStatements`.
The setting is a topological group acting on a topological space, and smooth
equivariant sheaves of modules on it. Two compactly supported cohomologies
are attached to such a sheaf `F`. The first is Worker 61's smooth Godement
compact cohomology: the homology of compact sections of the smooth Godement
complex of `F`. The second is Worker 13's right derived functors of compact
sections, computed in the abelian category of smooth equivariant sheaves.
The comparison map goes from the first to the second. It is induced by a map
from the smooth Godement complex to an injective resolution of `F` that is
compatible with the two augmentations. The propositions say:

- in degree zero, the comparison map is the composite of the published
  identifications of both sides with compact sections;
- on a locally compact Hausdorff space, the comparison map is an isomorphism
  in every degree;
- on a locally compact Hausdorff space, there are natural isomorphisms of
  functors whose components are the comparison maps.

This is the ordinary-topology analogue of the use of the resolutions of
Harris 1999, Lemma 2.2, to compute compactly supported cohomology (his
isomorphism (2.3)), and of the Godement step in the proof of Berkovich's
Corollary 1.5.2(i) (see Provenance). All four propositions are
theorem-statement definitions, not proofs. Invertibility, naturality and the
degree-zero identity are conclusions; none is supplied as data or as a
hypothesis.

## Objects

All declarations quantify over a commutative ring `R`, a group `G` and a
topological space `X`, all in one universe `u`. `G` is a topological group
(`IsTopologicalGroup`). It acts on `X` by `MulAction`, and each element acts
continuously (`ContinuousConstSMul`). The hypothesis
`Langlands.Sheaf.Equivariant.HasStableNeighbourhoods G X`, from Worker 13's
`Langlands.Sheaf.Equivariant.SmoothPart`, says that every open neighbourhood
of every point contains an open neighbourhood of that point that is
stabilized by some open subgroup. Worker 13 publishes instances for discrete
`G`, and for nonarchimedean `G` acting continuously (`NonarchimedeanGroup G`,
`ContinuousSMul G X`). The published smooth Godement construction, the
abelian structure on smooth sheaves and the derived functors below need
exactly these hypotheses. `comparisonMap` and the degree-zero proposition
assume nothing more. The invertibility and naturality propositions and the
conjunction also assume that `X` is Hausdorff (`T2Space`) and locally compact
(`LocallyCompactSpace`), which the truth argument uses.

The objects are the published ones:

- `Langlands.Sheaf.Equivariant.SmoothTopologicalSheaf R G X` is Worker 13's
  full subcategory of smooth sheaves inside the equivariant sheaves of
  `R`-modules on `X`. A sheaf is smooth when every local section is, near
  every point of its domain, fixed by an open subgroup on an open
  neighbourhood stabilized by that subgroup. Worker 13's
  `Langlands.Sheaf.Equivariant.SmoothAbelian` makes this subcategory abelian
  and proves that it has enough injectives.
- `Langlands.Sheaf.Equivariant.smoothSheafCompactSections R G X` is Worker
  13's functor sending a smooth sheaf to its compactly supported global
  sections, as an object of the published abelian category
  `Langlands.SmoothRep R G` of smooth representations. Worker 13 publishes
  that it is additive and preserves finite limits.
- `Godement.smoothZeroFunctor R G X` and `Godement.smoothCoaugmentation R G X`
  are Worker 61's degree-zero smooth Godement functor `D` and its
  coaugmentation `η : 𝟭 ⟶ D`, which is monic at every object
  (`Godement.mono_smoothCoaugmentation_app`). `Godement.smoothComplex R G X F`
  is Worker 61's smooth Godement complex of `F`, by definition the published
  cokernel complex `Langlands.Cohomology.CokernelComplex.complex D η F`.
- `Langlands.Cohomology.CokernelComplex.augmentationMap D η F` is the
  published augmentation from `F`, placed in degree zero, to this complex, in
  Worker 3's `Langlands.Sheaf.Godement.ExactnessStatement`. Its degree-zero
  component is `η.app F` (`augmentationMap_f_zero`).
- `Langlands.Cohomology.SmoothGodementCohomology.smoothGodementCompactCohomology R G X q`
  is Worker 61's degree-`q` homology, computed in `SmoothRep R G`, of compact
  sections applied termwise to the smooth Godement complex.
  `smoothGodementCompactCohomologyZeroIso R G X` is Worker 61's natural
  isomorphism from its degree-zero part to `smoothSheafCompactSections R G X`.
  It is an instance of Worker 13's
  `EquivariantGodementCohomology.homologyZeroIso`, whose component at `F` is
  the inverse of `EquivariantGodementCohomology.homologyIso`. That map sends
  compact sections of `F` into the degree-zero cycles by compact sections of
  the augmentation (`cyclesIso`), and then to homology.
- `Langlands.Cohomology.SmoothSheafCohomology.compactDerived R G X q` is
  Worker 13's `q`-th right derived functor, Mathlib's `Functor.rightDerived`,
  of `smoothSheafCompactSections R G X`. `compactDerivedZeroIso R G X` is
  Mathlib's `Functor.rightDerivedZeroIsoSelf`, the identification of the
  zeroth derived functor of a left exact functor with the functor.
  `compactDerivedIso R G X I q` is Mathlib's
  `InjectiveResolution.isoRightDerivedObj`, which identifies
  `(compactDerived R G X q).obj F` with the degree-`q` homology of compact
  sections of an injective resolution `I` of `F`.
- `InjectiveResolution F` is Mathlib's structure: a cochain complex
  `I.cocomplex` of injective objects with a quasi-isomorphism
  `I.ι : (CochainComplex.single₀ _).obj F ⟶ I.cocomplex`.

For an injective resolution `I` of `F`, a chain map
`φ : smoothComplex R G X F ⟶ I.cocomplex` and `q : ℕ`, the definition
`comparisonMap R G X I φ q` is the composite of

1. the map induced by `φ` on degree-`q` homology of compact sections, from
   `(smoothGodementCompactCohomology R G X q).obj F` to the degree-`q`
   homology of compact sections of `I.cocomplex`, and
2. the inverse of `compactDerivedIso R G X I q`, which lands in
   `(compactDerived R G X q).obj F`.

It is defined for every `φ`. The propositions use it only for `φ`
compatible with the augmentations, that is, with
`augmentationMap D η F ≫ φ = I.ι`. In degree zero this compatibility says
`η.app F ≫ φ.f 0 = I.ι.f 0`.

## The four propositions

| Declaration | Extra hypotheses | Asserted conclusion |
| --- | --- | --- |
| `SmoothGodementComparisonZeroStatement R G X` | none | For every smooth sheaf `F`, injective resolution `I` of `F` and compatible `φ`, `comparisonMap R G X I φ 0` equals `(smoothGodementCompactCohomologyZeroIso R G X).hom.app F ≫ (compactDerivedZeroIso R G X).inv.app F`. |
| `SmoothGodementComparisonIsIsoStatement R G X` | `T2Space X`, `LocallyCompactSpace X` | For every `F`, `I` and compatible `φ`, and every `q : ℕ`, `comparisonMap R G X I φ q` is an isomorphism (`IsIso`) in `SmoothRep R G`. |
| `SmoothGodementComparisonNaturalStatement R G X` | `T2Space X`, `LocallyCompactSpace X` | There is a family `e q : smoothGodementCompactCohomology R G X q ≅ compactDerived R G X q` of natural isomorphisms of functors such that `(e q).hom.app F = comparisonMap R G X I φ q` for every `F`, `I`, compatible `φ` and `q`. |
| `SmoothGodementComparisonStatements R G X` | `T2Space X`, `LocallyCompactSpace X` | The conjunction of the three, in this order. |

All hypotheses are explicit binders, so they appear in the types.

Remarks on what is asserted:

- The naturality proposition implies that the comparison map does not depend
  on the choice of `I` and of the compatible `φ`: all of them give the
  component of the same `e q`.
- Existence of a compatible `φ` for a given `I` is not restated. It is the
  published `Langlands.Cohomology.ResolutionLiftStatement`, applied to the
  augmentation, which is a quasi-isomorphism by the published
  `Langlands.Cohomology.CokernelResolutionStatement` because `η` is monic.
  Both are unproved statements.
- The degree-zero proposition is stated without separation or local
  compactness, because only left exactness of compact sections is involved.

## Why the statements are expected to hold

The argument below is derived here from published statements and Mathlib.
It is not the route of the sources, which work with the cohomology of the
underlying sheaf; see Provenance. Write `Γc` for
`smoothSheafCompactSections R G X` and `K = smoothComplex R G X F`.

Degree zero. Mathlib's `InjectiveResolution.toRightDerivedZero_eq` says that
`Γc.toRightDerivedZero.app F`, the inverse of the component of
`compactDerivedZeroIso`, is the map from `Γc F` into the degree-zero cycles
of `Γc I` induced by `Γc (I.ι.f 0)`, followed by the projection to homology
and by the inverse of `compactDerivedIso R G X I 0`. Worker 13's
`homologyIso` is the map from `Γc F` into the degree-zero cycles of `Γc K`
induced by `Γc (η.app F)` (`cyclesIso_hom_iCycles`), followed by the
projection to homology. The map induced by `φ` on homology commutes with
these projections (Mathlib's `HomologicalComplex.homologyπ_naturality`). So
both sides of the degree-zero identity, precomposed with `homologyIso`, are
maps from `Γc F` into the cycles of `Γc I`, followed by the same two maps.
After the inclusion of cycles into `Γc (I.cocomplex.X 0)` the two maps into
the cycles become `Γc (η.app F ≫ φ.f 0)` and `Γc (I.ι.f 0)`. These are equal
by compatibility in degree zero. No property of `X` is used.

Invertibility. By the published `CokernelResolutionStatement`, the
augmentation `augmentationMap D η F` is a quasi-isomorphism, because `η` is
monic, so `K` is a resolution of `F`. By the published
`Langlands.Cohomology.SmoothGodement.SmoothGodementCompactDerivedAcyclicStatement`,
every term of `K` is acyclic for the derived functors of `Γc` when `X` is
locally compact and Hausdorff. The published
`Langlands.Cohomology.AcyclicResolutionComparisonStatement`, applied to the
abelian category of smooth sheaves, the functor `Γc`, which is additive and
preserves finite limits, the complex `K` and this augmentation, then says
that the map of homology induced by a compatible `φ`, followed by the
inverse of `I.isoRightDerivedObj Γc q`, is an isomorphism. That composite
is `comparisonMap R G X I φ q` by definition.
The mathematical content of the acyclicity comparison is the usual dimension
shift. Let `Z^n` be the kernel of the `n`-th differential of `K`, with
`Z^0 = F`. Exactness of `K` gives short exact sequences
`0 → Z^n → K^n → Z^{n+1} → 0`. The long exact sequences of derived functors
of `Γc`, with `R^p Γc(K^n) = 0` for `p > 0`, give
`R^{q+1} Γc(Z^n) ≅ R^q Γc(Z^{n+1})` for `q > 0` and
`R^1 Γc(Z^n) ≅ coker(Γc K^n → Γc Z^{n+1})`. Induction on `q` gives
`R^q Γc(F) ≅ H^q(Γc K)`. Grothendieck's Tohoku paper, §2.4, Remark 3,
printed p.148, records that this identification is induced by a map of the
resolution to an injective resolution.

Naturality. For each `F`, the published `ResolutionLiftStatement` gives a
compatible chain map `φ_F` from `K` to Mathlib's chosen injective resolution
`injectiveResolution F`. Define the component of `e q` at `F` to be
`comparisonMap R G X (injectiveResolution F) φ_F q`, invertible by the
previous paragraph. For a morphism `f : F ⟶ F'`, the map of smooth Godement
complexes `(smoothComplexFunctor R G X).map f` commutes with the
augmentations by the published `CokernelComplex.augmentationMap_naturality`.
The published `ResolutionComparisonNaturalityStatement` then gives the
naturality square. The published `ResolutionComparisonIndependenceStatement`
says that any other injective resolution `I` and compatible `φ` give the
same map after the identifications with the derived functor, so the
component of `e q` at `F` equals `comparisonMap R G X I φ q`. The sources of
these statements are Cartan and Eilenberg, Chapter V, Proposition 1.1a,
printed p.78, and §3, printed pp.82-83 (recorded in the Markdown of
`Langlands.Cohomology.AcyclicResolution.Statement`).

## Provenance

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J.
Math. Kyoto Univ. 39-2 (1999), section 2. On printed p.304 Harris constructs,
following Berkovich, an embedding `T → F(T)` of an étale sheaf of smooth
`ℤ/ℓ^m ℤ[S(ẽ)]`-modules into a sheaf of the same kind that is acyclic for
`RΓ_c`, and iterates it on cokernels:

- p.304: "Lemma 2.2. For each `m` the constant sheaf `ℤ/ℓ^m ℤ` admits an
  `RΓ_c`-acyclic resolution `0 → ℤ/ℓ^m ℤ → F^0_m → F^1_m → ⋯` such that, for
  each `q`, `{F^q_m}` is an `ℓ`-divisible system of `S(ẽ)`-modules over
  `U(ẽ)`."
- p.305, after Lemma 2.2 bis, which truncates this resolution to a
  resolution `G^•_m` of finite length: "Let
  `d^q_m : G^q_m(U(ẽ)_F̄) → G^{q+1}_m(U(ẽ)_F̄)`, `Z^q_m = ker d^q_m`,
  `B^q_m = im d^{q-1}_m`. Thus Lemma 2.2 provides an isomorphism (2.3)
  `H^q_c(U(ẽ)_F̄, ℤ/ℓ^m ℤ) ~→ Z^q_m/B^q_m = H^q(G^•_m(U(ẽ)_F̄))`."

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces*, unfinished
1995-1996 manuscript:

- p.11: the support of a section; `Γ_{c,X(G)}(F)`, the sections over `X(G)`
  with compact support; and `Γ_{c,X{G}}(F) := lim_N Γ_{c,X(N)}(F)`, the
  colimit over open subgroups `N` of `G`. "The values of the high direct
  images of the functor `F ↦ Γ_{c,X{G}}(F)` ... are denoted by
  `H^q_c(X{G}, F)`."
- Corollary 1.5.2(i), pp.11-12: "For any étale abelian sheaf `F` on `X(G)`
  there are canonical isomorphisms `H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)`,
  `q ≥ 0`."
- Proof, p.12: "The case `q = 0` in (i) ... follows from the fact that every
  element of `H^0_c(X, b^*F)` is fixed by an open subgroup of `G` ..., and
  therefore the general case follows from Proposition 1.5.1." Proposition
  1.5.1, p.10, says that the terms `b^*(C^m(F))` of his Godement resolution
  are soft.

The propositions transcribe these to the ordinary open-set site:

- Worker 61's smooth Godement complex is the counterpart of Berkovich's
  `C^•(F)` and of the resolutions `F^•_m` of Harris's Lemma 2.2 (Worker 61's
  `Smooth.md` explains the correspondence `D ↔ ν_*ν^*`), and
  `smoothGodementCompactCohomology` is the counterpart of `H^q(G^•_m(U(ẽ)_F̄))`
  in (2.3).
- `compactDerived` is the counterpart of `H^q_c(X{G}, F)`: for a smooth sheaf
  every compactly supported section is fixed by an open subgroup, so
  `Γ_{c,X{G}}` becomes `smoothSheafCompactSections`.
- Berkovich's proof of Corollary 1.5.2(i) computes `H^q_c(X{G}, F)` with the
  Godement resolution, whose terms are acyclic by Proposition 1.5.1. The
  invertibility proposition is that step, with the published
  `SmoothGodementCompactDerivedAcyclicStatement` in place of Proposition
  1.5.1. The degree-zero proposition is the case `q = 0`, and the naturality
  proposition renders "canonical".
- Harris's (2.3) has on its left side the compactly supported cohomology of
  the underlying sheaf, that is, Berkovich's `H^q_c(X, b^*F)`. Its ordinary
  analogue is related to `compactDerived` by Worker 3's published
  `Langlands.Cohomology.SmoothCompactComparison.SmoothCompactDerivedComparisonStatement`.
  Together with that statement, the propositions here transcribe the
  computation of compactly supported cohomology by the resolutions of
  Lemma 2.2.

## Original-source correspondence

| Source | Original statement | Lean component |
| --- | --- | --- |
| Harris 1999, p.305, (2.3), with Lemma 2.2, p.304 | The `RΓ_c`-acyclic resolution provides `H^q_c(U(ẽ)_F̄, ℤ/ℓ^m ℤ) ≅ H^q(G^•_m(U(ẽ)_F̄))`. | `SmoothGodementComparisonIsIsoStatement`, for the smooth Godement complex and derived functors in the smooth category |
| Berkovich, proof of Cor. 1.5.2(i), p.12, case `q = 0` | The degree-zero case of the canonical isomorphisms. | `SmoothGodementComparisonZeroStatement` |
| Berkovich, proof of Cor. 1.5.2(i), p.12, with Prop. 1.5.1, p.10 | "The general case follows from Proposition 1.5.1." | `SmoothGodementComparisonIsIsoStatement` |
| Berkovich Cor. 1.5.2(i), pp.11-12 | The isomorphisms are canonical. | `SmoothGodementComparisonNaturalStatement`; naturality and independence of the lift |

## Scope

- The site is the ordinary open-set site of a topological space, not
  Berkovich's étale site of an analytic space. Analytic spaces, `X(G)`,
  `U(ẽ)` and the base change to `F̄` are not formalized here.
- Harris's truncated resolutions `G^•_m` of Lemma 2.2 bis, the
  `ℓ`-divisible systems in `m`, and the torsion coefficients `ℤ/ℓ^m ℤ` are
  not stated. The coefficients are an arbitrary commutative ring.
- Compatibility of the comparison with connecting morphisms is not stated.
- No invariant version, comparing Worker 61's
  `smoothGodementInvariantCompactCohomology` with Worker 13's invariant
  derived functors, is stated; no consulted source states it.
- The comparison with the compactly supported cohomology of the underlying
  sheaf is not restated; it is the published
  `SmoothCompactDerivedComparisonStatement`.
- `R`, `G` and `X` share one universe, as in the published construction and
  cohomology functors.

## Registered sources

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`: Harris 1999,
  PDF SHA-256
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`;
  section 2, printed pp.304-305 (PDF pp.6-7). The quoted Lemma 2.2 and (2.3)
  were read on the rendered scan.
- `provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`:
  Berkovich manuscript, folder SHA-256
  `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
  `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
  SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`;
  §1.5 through the proof of Corollary 1.5.2, pp.10-12. Read in the text
  layer. The printed page numbers equal the PDF page numbers.
- `provided-df60b2162f53c78d858f948959fe779f32064b9b99ef5345277dc18e8008a5f0`:
  Grothendieck, *Sur quelques points d'algèbre homologique*, Tôhoku Math. J.
  9 (1957), retained file
  `literature/Grothendieck 1957 Tohoku original- acyclic resolutions and derived comparison.pdf`,
  SHA-256 `7fb6ca3f5b860361dc75ff6456e25fc7b9e347acb0f08a78a1e032b9c2d330fe`;
  §2.4, Remark 3 after Theorem 2.4.1, printed p.148 (PDF p.30). Used only in
  the truth argument.
- `provided-4e029ea5216cb6ce6bfc05060277910b86f223b69bc92c508711e3760612bd4e`:
  Cartan and Eilenberg, *Homological Algebra* (1956), retained file
  `literature/Cartan-Eilenberg 1956 original- resolution comparison and derived functors.pdf`,
  SHA-256 `1e0915f23ec4a4bd638f469561931f5659a7a47faf92d48468bd290ddd726365`;
  Chapter V, Proposition 1.1a, printed p.78 (PDF p.100), and §3, printed
  pp.82-83 (PDF pp.104-105). Used only in the truth argument.

## Formal dependencies and checks

The direct project imports are byte-identical in Library commits
`983d968c2bdcb4cc242ffa0a4ee087f40fd86436` and
`55cf6172e313c02aa8f5978501d957bfa08de20d`:

| Module | Author | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- | --- |
| `Langlands.Cohomology.SmoothGodementCohomology` | Worker 61 | `9ff0b420e63b253af00ed18af353d5daefdd0b75a1c09c90726563f3695a37c7` | `121a57c44e58c2ead87812ae506b7eac044be97ad089b87ffac5b0390b833a16` |
| `Langlands.Sheaf.Godement.ExactnessStatement` | Worker 3 | `66c45b9d460fce4935aa869c1db1c932ca9e60fe95188ea3a6895ae9d0037435` | `d9776b5f0107c1f34b83b8a03fee2ba25a3e6904faa288eb51512bd951b0f4b5` |

From the first the module uses `smoothGodementCompactCohomology` and
`smoothGodementCompactCohomologyZeroIso`. Through it, it uses Worker 61's
`Langlands.Sheaf.Equivariant.Godement.Smooth` (`smoothZeroFunctor`,
`smoothCoaugmentation`, `smoothComplex`; Lean SHA-256
`c87bbf5eef53c9d4b6e1b2c9d30f834d14533f3e963b489a2fa96ccd7c1e37cc`) and
Worker 13's `Langlands.Cohomology.SmoothSheafCohomology` (`compactDerived`,
`compactDerivedZeroIso`, `compactDerivedIso`; Lean SHA-256
`f1365e1fcf6064dbbc6bacd8491c16ce24fe3a76215dc606adc263032be3c7d1`). From the
second it uses `CokernelComplex.augmentationMap`.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

Check `c005da11-9cb6-4b87-ada4-39f9a06db7ae` built this module from a draft
directory against the published imports, with no errors or warnings. Check
`0a9e1571-7e8f-45bd-9228-2b6045ad3253` built it with Lake from the
workspace, against Library `55cf6172`, with no errors or warnings. The Lean
file is unchanged since the first check. The second check inspected
`SmoothGodementComparisonStatements` as a `Prop`-valued definition with the
single universe parameter `u`, depending only on `propext`,
`Classical.choice` and `Quot.sound`. Check
`fb947c49-6989-4b8a-bbbf-55633bc810ba` compiled a test file against the same
Lean file, with no errors or warnings, and its output was read. It printed
`comparisonMap` and the four propositions with universes shown, and the
axioms of the conjunction. The prints show:

- the degree-zero proposition has no `T2Space X` or `LocallyCompactSpace X`
  binder, while the other three propositions carry both;
- `R`, `G` and `X` all live in the universe `u`;
- the conjunction depends only on `propext`, `Classical.choice` and
  `Quot.sound`.

The same test file checks by `rfl` that `smoothComplex R G X F` is the
published cokernel complex, that `(smoothGodementCompactCohomology R G X q).obj F`
is the degree-`q` homology of compact sections of `smoothComplex R G X F`,
that `compactDerived R G X q` is Mathlib's `rightDerived`, and that
`comparisonMap` is the homology map followed by the inverse of
`I.isoRightDerivedObj`. It proves that the compatibility hypothesis gives
`η.app F ≫ φ.f 0 = I.ι.f 0`. It also elaborates the conjunction over `ℚ` for
an arbitrary topological group acting on a locally compact Hausdorff space
with `HasStableNeighbourhoods`, for discrete `G`, for nonarchimedean `G`
acting continuously, and for the trivial group acting on a point. It
elaborates the degree-zero proposition without the two topological
hypotheses. This shows only that the statements are well formed there.

Check `a91c0cc2-a9dd-45d3-bcb8-0af24caa4ffb` compiled a private test file
against the same Lean file, with no errors or warnings. The file is not part
of this submission. It proves the degree-zero proposition outright, by the
argument above. It derives the invertibility proposition from the published
`AcyclicResolutionComparisonStatement`, `CokernelResolutionStatement` and
`SmoothGodementCompactDerivedAcyclicStatement`. It derives the naturality
proposition from the published `ResolutionLiftStatement`,
`ResolutionComparisonIndependenceStatement`,
`ResolutionComparisonNaturalityStatement` and `CokernelResolutionStatement`,
together with the invertibility proposition. These derivations take the
published statements as hypotheses. They do not prove them.

Compilation and inspection establish well-formed statements. Apart from the
private degree-zero proof, they do not prove any component.
