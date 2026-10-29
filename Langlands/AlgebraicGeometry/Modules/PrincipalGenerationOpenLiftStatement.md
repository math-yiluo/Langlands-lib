# Lifting principal opens of a generation open to sections of tensor powers

This module states one proposition and proves nothing:

```lean
def Langlands.SchemeModule.PrincipalGenerationOpenLiftStatement : Prop :=
  ∀ (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Langlands.AlgebraicGeometry.Picard.LineBundle X)
    (s : Langlands.SchemeModule.GlobalSections M.obj)
    (r : Γ(X, Langlands.SchemeModule.trivializationOpen M.obj s)),
    ∃ n : ℕ, 1 ≤ n ∧
      ∃ t : Langlands.SchemeModule.GlobalSections
        (Langlands.Scheme.Modules.tensorPow M.obj n),
        Langlands.SchemeModule.trivializationOpen
          (Langlands.Scheme.Modules.tensorPow M.obj n) t = X.basicOpen r
```

It has one universe parameter `u`. The file opens only `AlgebraicGeometry`, for
`Scheme` and the notation `Γ(X, U)`. All Library names are written in full and
refer to the published declarations.

## Meaning

Let `X` be a scheme in `Scheme.{u}` whose underlying space is quasi-compact
(`CompactSpace X`) and quasi-separated (`QuasiSeparatedSpace X`). These are the
only hypotheses on `X`. There is no affine, separated, noetherian, ample or
base-field assumption.

- `M` is a line bundle in the Library sense: a module sheaf `M.obj` on `X` that
  is isomorphic, on some open neighbourhood of every point, to the structure
  sheaf of that open.
- `s` is an arbitrary global section of `M.obj`. It may be zero.
- `trivializationOpen M.obj s` is the supremum in `X.Opens` of all opens `U` on
  which `TrivializesOn M.obj s U` holds. That predicate says that the
  restriction to `U` of the morphism from the structure module sending `1` to
  `s` is an isomorphism. So this is the whole maximal open on which `s`
  generates `M.obj`, not a chosen neighbourhood or an affine subopen. It plays
  the role of the source's `X_s`.
- `r : Γ(X, trivializationOpen M.obj s)` is an arbitrary regular function on
  that whole open, that is, an element of the ring of sections of the
  structure sheaf of `X` over it. It may be zero.
- `X.basicOpen r` is Mathlib's `AlgebraicGeometry.Scheme.basicOpen`: the open
  of `X` consisting of the points `x` of `trivializationOpen M.obj s` at which
  the germ of `r` is a unit. Mathlib's `AlgebraicGeometry.Scheme.basicOpen_le`
  shows that it lies inside `trivializationOpen M.obj s`.
  It is an open of the ambient `X`, not of the open subscheme.

The proposition says that there exist an exponent `n ≥ 1` and a global section
`t` of the actual tensor power `tensorPow M.obj n` with

```text
trivializationOpen (tensorPow M.obj n) t = X.basicOpen r
```

as an equality in `X.Opens`. In words, on such a scheme every principal open
of a regular function on the generation open `X_s` is itself the whole
generation open of a global section of some positive tensor power of `M`. The section `t` is
arbitrary; it need not be a power of `s` or have any prescribed form.

The exponent must be positive. The cases `r = 0`, `s = 0` and an empty
`X.basicOpen r` are not excluded. Neither is the empty scheme.

### The right-associated convention

`Langlands.Scheme.Modules.tensorPow M.obj n` is the actual right-associated
tensor power in `Langlands.AlgebraicGeometry.Modules.Tensor`. Its zeroth power is
the structure sheaf, and its power `n + 1` is the sheafified tensor product
`tensorObj M.obj (tensorPow M.obj n)`. For `n ≥ 1`,

```text
tensorPow M.obj n = M ⊗ (M ⊗ (⋯ ⊗ (M ⊗ 𝒪_X)))      (n copies of M)
```

In particular the first power is `tensorObj M.obj (structureSheaf X)`, not
`M.obj` itself. The statement does not identify `tensorPow M.obj n` with any
flattened or left-associated tensor product.

## Source correspondence

The original source is The Stacks Project, *Properties of Schemes*, Lemma
28.18.2, tag [01PW](https://stacks.math.columbia.edu/tag/01PW). The registered
PDF is `stacks-properties-chapter-2026-10-28`, file
`Stacks Project — Properties of Schemes chapter (PDF compiled July 14, 2026).pdf`,
SHA256
`2f5b9ba41e07dd3a888da40496e07afae6caedd550597d96313ab16db4380316`. There the
result is Lemma 18.2 on pages 22–23. The current HTML page with its comments is
retained in the registered snapshot
`stacks-section-open-prerequisites-2026-10-29`, directory SHA256
`290fd705ee87e9b334a225352ff3b4d9118789a923dac35712126f59581269cf`, as the file
`01PW.html` with SHA256
`60bc1435a16d7d9ad4d4ef9cc426dbe4a992c7cb421f14fb5e5989fbfe06475c`.

The lemma concerns a scheme `X`, an invertible sheaf `𝓛`, a section
`s ∈ Γ(X, 𝓛)` and a quasi-coherent module `𝓕`, and the canonical map
`Γ_*(X, 𝓛, 𝓕)_(s) → Γ(X_s, 𝓕|_{X_s})`. Part (1) says the map is injective
if `X` is quasi-compact. Part (2) says it is an isomorphism if `X` is
quasi-compact and quasi-separated. The lemma concludes:

> In particular, the canonical map
> `Γ_*(X, 𝓛)_(s) → Γ(X_s, 𝒪_X)`, `a/s^n ↦ a ⊗ s^{-n}`,
> is an isomorphism if `X` is quasi-compact and quasi-separated.

### Derived formulation

The present proposition is this project's derived consequence of that
conclusion. It is not a verbatim source statement. The source identifies the
ring of the open `X_s` with a degree-zero localization. The proposition instead
asserts an exact identity of whole generation opens. It is the form needed by
Worker 689 for the basis proof in task `95bb4422-61fb-457d-82b7-162bc9807a6b`,
whose target pair is in
`Langlands.AlgebraicGeometry.Picard.AmpleSectionOpenStatements`. The exact Lean
form, with the explicit quasi-compactness and quasi-separatedness hypotheses,
was fixed by the contract of task `7aebc706-2b14-43af-8bb2-921eeeac9ba4`,
published by Worker 689. The parent task establishes these two hypotheses from
ampleness.

The expected mathematical route is as follows. It is recorded only to explain
why the proposition holds and why its exponent is positive. This module does
not prove it.

1. By the surjectivity in the conclusion above, `r = a/s^m` for some `m ≥ 0`
   and some `a ∈ Γ(X, 𝓛^{⊗m})`. That is, `a|_{X_s} = r · s^m|_{X_s}`. This
   clears a power of `s` from `r`.
2. Put `t = a ⊗ s ∈ Γ(X, 𝓛^{⊗(m+1)})`. Its generation open is
   `X_t = X_a ∩ X_s`. On `X_s` the section `s^m` generates `𝓛^{⊗m}`, so
   `X_a ∩ X_s` is the principal open of `r` in `X_s`. Hence `X_t` equals that
   principal open, with exponent `n = m + 1 ≥ 1`.

The final multiplication by `s` is needed. The cleared section `a` alone may
generate at points outside `X_s`. For example, when `m = 0`, `a` is a
regular function on `X` that may be a unit outside `X_s`. Multiplying by `s`
makes the lifted section stop generating outside the original generation open.

### Translations

- The source's invertible sheaves are represented by the Library's locally
  free rank-one sheaves (`LineBundle`). Stacks Lemma 17.25.4 identifies the
  two notions when the structure sheaf has local stalks, as schemes do; the
  `LineBundle` Markdown records this. Lemmas 17.25.4 and 17.25.10 are in the
  registered source `stacks-local-freeness-invertibility-sections-2026-10-21`,
  retained file `01CR.html`.
- The source's `X_s` is "the open over which `s` has an inverse" (Stacks,
  Modules, Lemma 17.25.10), that is, `{x | s ∉ 𝔪_x 𝓛_x}`. It is represented by
  the whole maximal trivialization open `trivializationOpen M.obj s`. Lemma
  17.25.10 also states that `s : 𝒪_{X_s} → 𝓛|_{X_s}` is an isomorphism, so
  `X_s` lies in the trivialization open. Conversely, at a point of an open
  where this map is an isomorphism, the stalk of `s` generates `𝓛_x`. In the
  Library this agreement for line bundles is the published theorem
  `Langlands.SchemeModule.lineBundleResidueOpenComparison` (module
  `Langlands.AlgebraicGeometry.Modules.SectionResidueComparison`). That
  comparison is neither imported nor assumed here. The open
  `trivializationOpen (tensorPow M.obj n) t` is likewise used directly as the
  generation open of `t`.
- The source's `Γ(X_s, 𝒪_X)` is the ring `Γ(X, trivializationOpen M.obj s)` of
  sections of the structure sheaf of `X` over that open.
- The principal open of `r` in `X_s`, the open where `r` is invertible (Stacks,
  Schemes, Lemma 26.6.2), is `X.basicOpen r`.
- The source's `𝓛^{⊗n}` is represented by `tensorPow M.obj n` with the right
  association and trailing structure-sheaf factor described above.
- The source's quasi-compact scheme is `CompactSpace X`. The source's
  quasi-separated scheme is `QuasiSeparatedSpace X`. Mathlib's class says that
  the intersection of two quasi-compact opens is quasi-compact. Mathlib's
  `AlgebraicGeometry.quasiSeparatedSpace_iff_quasiSeparated` identifies it with
  quasi-separatedness of the morphism `terminal.from X` to the terminal scheme,
  which is `Spec ℤ` up to isomorphism; that is the source's definition.
  Mathlib's `AlgebraicGeometry.quasiSeparatedSpace_iff_forall_affineOpens`
  gives the affine-intersection criterion of Stacks, Schemes, Lemma 26.21.6,
  which the source's proof uses.
- The source fixes a quasi-coherent module `𝓕`. Only `𝓕 = 𝒪_X`, the case of
  the concluding sentence, is used. So no quasi-coherence hypothesis appears.

### Errata and current comments

Current errata were checked before reliance. On 2026-10-29 the current page at
`https://stacks.math.columbia.edu/tag/01PW` was fetched. It is byte-identical
to the retained `01PW.html`, with the same SHA256 above. It has seven comments.

- Comment #4719 by Manuel Hoff (November 25, 2019) reports a mistake in the
  proof of part (2). As then defined, the local sections `t_j` restrict to
  `f_j^{e_j} t'|_{D(f_j)}`, which are the wrong elements and need not glue.
  The comment proposes `t_j = f_j^{e - e_j} t'_j ⊗ q_j^e`, where `q_j` is the
  trivializing section of `𝓛|_{U_j}`. It also notes that the exponents `e_j`
  may all be chosen equal.
- Comment #4809 by Johan (December 10, 2019) accepts this and records the fix.

The current HTML and the registered PDF (page 22) both define
`t_j = f_j^{e - e_j} t'_j ⊗ q_j^e`, so the current source implements that
correction of the clearing exponents. The correction concerns the proof of
part (2), the surjectivity used in the route above, not the statement of the
lemma.

The other comments do not change the lemma. Comments #2595 and #2623 (2017)
discuss a suggested slogan. Comments #11098, #11100 and #11235 (January 2026)
point to Görtz–Wedhorn, *Algebraic Geometry I*, Theorem 7.22, and to the
Springer edition of EGA I, Section 6.8; the latter reference was added as
`[GD71, Section 6.8]`, which the registered PDF shows. The enclosing Section
28.18, tag [0B5K](https://stacks.math.columbia.edu/tag/0B5K), has two
comments. Its current page was fetched on 2026-10-29, SHA256
`9ede9a0eeada48bef8f9f3689587100cb2ce0c311c86c0e43a49657d7b6e69fb`. Comment
#11097 gives an alternative description of the map (28.18.1.1). Comment #11234
answers "Leaving as is." Neither corrects Lemma 28.18.2. No errata note for this
passage was found among the public notes.

## Provenance and scope

The provenance is derived, as explained above. The module imports
`Langlands.AlgebraicGeometry.Modules.SectionLocus`,
`Langlands.AlgebraicGeometry.Modules.Tensor`,
`Langlands.AlgebraicGeometry.Picard.LineBundle` and
`Mathlib.Topology.QuasiSeparated`. It defines no new tensor power, section,
line-bundle structure, locus or localization.

It proves no part of the proposition. It also does not state or prove the
localization isomorphism of Lemma 28.18.2, any tensor-section locus identity,
any rank-one property of tensor powers, any tensor-power isomorphism, or any
ampleness result. The proof of the proposition is the separate obligation of a
`lean.proof@1` successor task.

The pinned environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0
and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
