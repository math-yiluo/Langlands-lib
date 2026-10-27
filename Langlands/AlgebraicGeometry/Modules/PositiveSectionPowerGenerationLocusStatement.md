# The generation locus of a positive power of a line-bundle section

This module states one proposition and proves nothing:

```lean
def Langlands.SchemeModule.PositiveSectionPowerGenerationLocusStatement : Prop :=
  ∀ (X : AlgebraicGeometry.Scheme.{u})
    (L : Langlands.AlgebraicGeometry.Picard.LineBundle X)
    (s : Langlands.SchemeModule.GlobalSections L.obj) (n : ℕ),
    0 < n →
    Langlands.SchemeModule.trivializationOpen
      (Langlands.Scheme.Modules.tensorPow L.obj n)
      (Langlands.SchemeModule.sectionPow L.obj s n) =
    Langlands.SchemeModule.trivializationOpen L.obj s
```

It has one universe parameter `u`. All names are written in full and refer to
the published Library declarations.

## Meaning

Let `X` be an arbitrary scheme in `Scheme.{u}`. There is no affine, separated,
quasi-compact or noetherian assumption. `L` is a line bundle in the Library
sense: a module sheaf on `X` that is isomorphic, on some open neighbourhood of
every point, to the structure sheaf of that open. `s` is an arbitrary global
section of the underlying sheaf `L.obj` and may be zero. `n` is any natural
number with `0 < n`.

The ingredients are the published constructions, not local replacements:

- `Langlands.Scheme.Modules.tensorPow L.obj n` is the actual right-associated
  tensor power in `Langlands.AlgebraicGeometry.Modules.Tensor`. Its zeroth
  power is the structure sheaf, and its power `n + 1` is the sheafified tensor
  product `tensorObj L.obj (tensorPow L.obj n)`.
- `Langlands.SchemeModule.sectionPow L.obj s n` is the published recursive
  section power in `Langlands.AlgebraicGeometry.Modules.SectionPowers`. Its
  zeroth power is the unit section `1` of the structure sheaf, and its power
  `n + 1` is `tensorSection L.obj (tensorPow L.obj n) s (sectionPow L.obj s n)`.
- `trivializationOpen N r` is the supremum in `X.Opens` of all opens `U` on
  which `TrivializesOn N r U` holds. That predicate says that the restriction
  to `U` of the morphism from the structure module sending `1` to `r` is an
  isomorphism. It is therefore the whole maximal open on which `r` generates
  `N`, not a chosen neighbourhood or an affine subopen.

The proposition says that, for every positive `n`,

```text
trivializationOpen (L^⊗n) (s^n) = trivializationOpen L s
```

as an equality in `X.Opens`. In words, a positive power of a section generates
its tensor power exactly where the section generates `L`. The inclusion `⊇`
says that the power generates wherever `s` does. The inclusion `⊆` says that
the power can generate only where `s` already generates.

### The right-associated convention

Because the recursion starts from the structure sheaf, the Library's powers
carry a trailing structure-module factor. For `n ≥ 1`,

```text
tensorPow L.obj n  = L ⊗ (L ⊗ (⋯ ⊗ (L ⊗ 𝒪_X)))      (n copies of L)
sectionPow L.obj s n = s ⊗ (s ⊗ (⋯ ⊗ (s ⊗ 1)))
```

with sheafified tensors throughout. In particular the first power is
`tensorObj L.obj (structureSheaf X)` with section `s ⊗ 1`, not `L.obj` itself
with section `s`. So the case `n = 1` is a genuine assertion: the whole
generation locus of `s ⊗ 1` in `L ⊗ 𝒪_X` equals that of `s` in `L`. The
statement does not identify `tensorPow L.obj n` with any flattened or
left-associated tensor product, and it does not use a unitor or associator
isomorphism to move between such forms.

The exponent `0` is excluded, as in the source. There the left-hand side is
the generation locus of `1` in the structure sheaf, which is all of `X`, while
the right-hand side is the locus of `s`, which is empty when `s = 0`. So the
equality fails for `n = 0` whenever `X` is nonempty and `s = 0`.

No hypothesis is added. The statement assumes no rank-one or line-bundle
property of the powers `tensorPow L.obj n`, no residue-field comparison, no
pullback compatibility, and no flatness, coherence, quasi-coherence,
separatedness, noetherian or affineness condition. It also assumes no
ampleness property. The rank-one property enters only through the type of `L`.

## Source correspondence

The original source is The Stacks Project, Lemma 28.27.2, tag
[01PT](https://stacks.math.columbia.edu/tag/01PT). It is registered as
`stacks-ample-powers-restriction-quasiaffine-2026-10-24`. The retained file is
`Stacks Project - Ample powers, closed restriction and quasi-affineness (HTML snapshot 2026-10-24)/01PT.html`,
with file SHA256
`395431bbb5da3dca36f260eb3ffcfc8ca07a519ca24abc0443ea3c84404a37a9`. The
registered directory SHA256 is
`03dddd39b5528263fbc3633f1545b8544e937bb29c9752ffe4a351bb6e093e9a`.
The lemma states that for a scheme `X`, an invertible `𝒪_X`-module `𝓛` and
`n ≥ 1`, `𝓛` is ample if and only if `𝓛^{⊗n}` is ample. Its whole proof is
"This follows from the fact that `X_{s^n} = X_s`." The present proposition
formalizes that fact, for a section `s` of `𝓛` itself and its power
`s^n ∈ Γ(X, 𝓛^{⊗n})`, with the two sides in the source's order. It does not
state the ampleness equivalence. The page's two comments, by Matt Stevenson
and Takumi Murayama, relate the lemma to EGA II, Proposition 4.5.6(i), where
`X` is assumed quasi-compact, and record that the reference was added. They
do not change the statement or the proof.

The source locus is represented by an internal translation. Section 28.27 of
the source, tag 01PR, recalls from Stacks Lemma 17.25.10 that
`X_s = {x ∈ X | s ∉ 𝔪_x 𝓛_x}` is open. This is the pointwise nonvanishing
locus. The present statement uses instead the Library's whole trivialization
open, the largest open on which `𝒪_X → 𝓛`, `1 ↦ s`, is an isomorphism. Lemma
17.25.10 also states that `s : 𝒪_{X_s} → 𝓛|_{X_s}` is an isomorphism, so
`X_s` lies in the trivialization open. Conversely, at a point of an open where
this map is an isomorphism, `𝓛_x ≅ 𝒪_{X,x}` is generated by the stalk of `s`,
so `s ∉ 𝔪_x 𝓛_x`. In the Library this agreement for line bundles is the
published theorem `Langlands.SchemeModule.lineBundleResidueOpenComparison`
(module `Langlands.AlgebraicGeometry.Modules.SectionResidueComparison`):

```lean
nonvanishingLocus L.obj s = (trivializationOpen L.obj s : Set X)
```

This explains why `trivializationOpen L.obj s` represents the source's `X_s`.
The comparison is neither imported nor assumed by the statement. For the power,
the left-hand side
`trivializationOpen (tensorPow L.obj n) (sectionPow L.obj s n)` is used
directly as the generation locus. The statement does not assume that the power
is a line bundle, so no residue-field form of that side is asserted or needed.

Further translations are as follows. The source's invertible modules are
represented by the Library's locally free rank-one sheaves (`LineBundle`).
Stacks Lemma 17.25.4 identifies the two notions when all stalks of the
structure sheaf are local rings, as they are on a scheme; the `LineBundle`
Markdown records this. Lemmas 17.25.4 and 17.25.10 are in the registered
source `stacks-local-freeness-invertibility-sections-2026-10-21`, in the
retained file `01CR.html` of its folder. The source's `𝓛^{⊗n}` is the
`n`-fold tensor product and `s^n` is the `n`-fold tensor `s ⊗ ⋯ ⊗ s`. The
Library's `tensorPow` and `sectionPow` realize them with right association and
the trailing structure-module factor described above, using the actual
sheafified tensor product. The source works on a scheme `X` with an arbitrary
invertible module and every `n ≥ 1`, and the statement keeps exactly that
generality.

Current errata were checked before reliance. On 2026-10-27 the current page
at `https://stacks.math.columbia.edu/tag/01PT` was fetched; it is
byte-identical to the retained file, with the same SHA256 above, the same
lemma, proof and two comments. The comments on the enclosing Section 28.27
were checked in the registered snapshot
`stacks-01pr-current-errata-check-2026-10-26`, content SHA256
`10e5729facc1f46a826ad3adad02c107aa2d7aec3f87b7650122c46c5d9a59c1`. That
snapshot contains Lemma 28.27.2 with the same proof. Its five section comments
concern ampleness on a scheme that is a disjoint union of two open subschemes
and do not correct this lemma or the fact `X_{s^n} = X_s`. No errata note for
this passage was found among the public notes.

## Provenance and scope

The provenance is derived. The mathematical content is the fact used in the
source's proof. The use of the whole maximal trivialization open, the actual
right-associated `tensorPow` and the recursive `sectionPow` follows the task
contract published by Worker 694 from the section-power construction task,
which fixes this exact proposition.

The module imports `Langlands.AlgebraicGeometry.Modules.SectionLocus`,
`Langlands.AlgebraicGeometry.Modules.SectionPowers` and
`Langlands.AlgebraicGeometry.Picard.LineBundle`. It defines no new tensor
power, section power, line-bundle structure or locus. It proves neither
inclusion. It also proves no rank-one property of tensor powers, no tensor
distributivity or flattening, no tensor-section locus identity and no
ampleness result. The proof of the proposition is the separate obligation of
a `lean.proof@1` successor task.

The pinned environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0
and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
