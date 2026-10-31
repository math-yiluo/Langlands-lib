# Clearing a scalar section on a line-bundle generation open

`Langlands.SchemeModule.LineBundleSectionClearingStatement.{u}` is a
Prop-valued definition with one arbitrary universe parameter `u`. It states
the following unconditional scalar section-clearing assertion:

```lean
def LineBundleSectionClearingStatement : Prop :=
  ∀ (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (L : LineBundle X) (s : GlobalSections L.obj)
    (r : Γ(X, trivializationOpen L.obj s)),
    ∃ (m : ℕ) (a : GlobalSections (tensorPow L.obj m)),
      (tensorPow L.obj m).presheaf.map
        (homOfLE (show trivializationOpen L.obj s ≤ ⊤ from le_top)).op a =
        r • (tensorPow L.obj m).presheaf.map
          (homOfLE (show trivializationOpen L.obj s ≤ ⊤ from le_top)).op
          (sectionPow L.obj s m)
```

Here the namespaces `CategoryTheory`, `AlgebraicGeometry`,
`TopologicalSpace`, `Langlands.Scheme.Modules` and
`Langlands.AlgebraicGeometry.Picard` are open, and the declaration is in
`Langlands.SchemeModule`.

## Meaning and exact scope

Let `X : Scheme.{u}` be quasi-compact and quasi-separated. These conditions
are `CompactSpace X` and `QuasiSeparatedSpace X`, respectively. Let `L` be
any actual Library line bundle, so `L.obj : X.Modules` is locally free of
rank one, and let `s` be any global section of that module sheaf. Put
`U = trivializationOpen L.obj s`.

The open `U` is the whole maximal open on which the structure-module
morphism sending one to `s` is an isomorphism. The Library defines it as
the supremum of all opens with that property. For a line bundle it is the
nonvanishing locus `X_s` of the source. The published theorem
`Langlands.SchemeModule.lineBundleResidueOpenComparison`, in
`Langlands.AlgebraicGeometry.Modules.SectionResidueComparison`, identifies
its underlying set with the entire residue nonvanishing locus. This
comparison explains the source correspondence; it is not an extra premise
of the proposition.

For every regular function `r : Γ(X, U)` there exist `m : ℕ` and a global
section `a` of the actual module sheaf `tensorPow L.obj m` such that

```text
a restricted to U = r · (sectionPow L.obj s m restricted to U).
```

Both sides are sections of that same module sheaf over `U`.
The displayed presheaf maps are exactly restriction along `U ≤ ⊤`;
`r •` is its usual module action by the structure-sheaf ring `Γ(X, U)`.
The equality concerns this entire open, without a choice of smaller opens.

The exponent may be zero. There is no positivity condition and no
nonzero or nonempty condition: zero sections, zero functions, the empty
open and the empty scheme are all included. There are no affineness,
separatedness, noetherian, base-field or ampleness assumptions. No
localization, quasi-coherence, section-extension, comparison or
principal-lifting assertion is assumed as a premise.

## Actual tensor powers and sections

The objects are the existing right-associated tensor powers in
`Langlands.Scheme.Modules`:

```text
tensorPow L.obj 0       = structureSheaf X
tensorPow L.obj (m + 1) = tensorObj L.obj (tensorPow L.obj m).
```

Thus a positive power has a trailing structure-module factor, and the
first power is `tensorObj L.obj (structureSheaf X)`. The formal statement
uses these objects themselves, without identifying them definitionally
with flattened powers.

The section is the existing `Langlands.SchemeModule.sectionPow`, imported
from `Langlands.AlgebraicGeometry.Modules.SectionPowers`. Its zeroth value
is the unit section `(1 : Γ(X, ⊤))`; its successor is the actual tensor
section of `s` with its preceding power. It follows the same right
association and trailing-unit convention. The chosen categorical
realization of powers and their sections is part of the selected Library
interface, rather than additional notation imposed by the source.

## Source and provenance

The mathematical source is The Stacks Project Authors, *Properties of
Schemes*, Lemma 28.18.2, tag
[01PW](https://stacks.math.columbia.edu/tag/01PW), part (2), specifically
the section-extension assertion in its surjectivity proof and the
concluding specialization to the structure sheaf. The retained source is
registered as `stacks-section-open-prerequisites-2026-10-29`, *Stacks
Project — Section-open lifting and finite avoidance (HTML snapshot
2026-10-29)*, directory SHA256
`290fd705ee87e9b334a225352ff3b4d9118789a923dac35712126f59581269cf`.
Its file `01PW.html` has SHA256
`60bc1435a16d7d9ad4d4ef9cc426dbe4a992c7cb421f14fb5e5989fbfe06475c`.
The full lemma, proof and all seven retained comments were read. No
applicable source-specific errata note was found in the project's public
notes or errata locations.

The source starts with an invertible sheaf `𝓛`, a section `s` and a
quasi-coherent module `𝓕`. Part (2) identifies the degree-zero localization
of the graded section module with the sections of `𝓕` over `X_s`, when
`X` is quasi-compact and quasi-separated. In its proof, a section `t'`
over `X_s` extends after multiplication by a nonnegative power of `s` to
a global section of `𝓕 ⊗ 𝓛^m`.

Specialize to `𝓕 = 𝒪_X` and `t' = r`. The structure sheaf is
quasi-coherent, so no quasi-coherence hypothesis remains in this
specialization. Under the canonical unit and tensor-association
identifications, the resulting global section is `a` and the restriction
equality is `a|_{X_s} = r · s^m|_{X_s}`. The Library's locally free
rank-one `LineBundle`, whole maximal trivialization open, `tensorPow` and
`sectionPow` give the precise realization used in Lean.

This is a derived specialization and selected interface of that source
theorem. It does not state the source's full localization isomorphism or
its injectivity assertion. Worker 5 supplied the exact clearing interface
for the conditional principal-lift reduction; Worker 311 contributed the
generic locus assembly motivating the prerequisite. Their conditional
assemblies do not supply a proof of the proposition stated here.

## Corrected source proof

The retained comments record the correction used by the current text.
In comment [#4719](https://stacks.math.columbia.edu/tag/01PW#comment-4719)
(November 25, 2019), Manuel Hoff observes that the former local sections
have incompatible clearing exponents and need not glue. With local
denominator exponents `e_j`, their maximum `e`, and a local frame `q_j`,
the corrected local section is

```text
t_j = f_j^(e - e_j) t'_j ⊗ q_j^e.
```

Comment [#4809](https://stacks.math.columbia.edu/tag/01PW#comment-4809)
(December 10, 2019) records Johan's acceptance and fix. The retained
current proof of part (2) contains precisely this corrected formula,
before clearing the finitely many overlap differences by a further
common power. The correction changes the proof's local exponents, not
the statement or its scalar specialization.

The two 2017 comments discuss a suggested slogan. The three January 2026
comments discuss references to Görtz–Wedhorn and the Springer edition of
EGA I, Section 6.8; they introduce no further mathematical correction.

## Formal status

This module states the proposition and supplies no proof. It imports
only `SectionPowers`, `Picard.LineBundle` and
`Mathlib.Topology.QuasiSeparated`, using the existing definitions
unchanged. Its unconditional proof and the consuming principal-lift and
ample-basis proofs are separate obligations.

The pinned environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
