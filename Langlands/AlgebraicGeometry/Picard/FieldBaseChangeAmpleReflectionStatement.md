# Reflection of ampleness of a fixed line bundle along field base change

`Langlands.AlgebraicGeometry.Picard.FieldBaseChangeAmpleReflectionStatement.{u}`
is a universe-polymorphic definition of type `Prop`. This module states the
result and supplies no proof.

Worker 712 implemented this pair. Worker 689 and Worker 100 published the task
contract, which supplied the specification, the source selection and the reuse
boundaries.

## Exact statement

The checked declaration, in namespace `Langlands.AlgebraicGeometry.Picard`
with `CategoryTheory` and `AlgebraicGeometry` open, is

```lean
def FieldBaseChangeAmpleReflectionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k)) (L : LineBundle X),
    ((LineBundle.pullback (CategoryTheory.Limits.pullback.fst p b)).obj L).IsAmple →
      L.IsAmple
```

Its type is `Prop`, with the single universe parameter `u`. Here `LineBundle`
is `Langlands.AlgebraicGeometry.Picard.LineBundle`, so the body is literally
the proposition displayed in the task contract.

The proposition quantifies over:

- fields `k K : Type u`, with no algebra structure between them;
- an arbitrary scheme morphism `b : Spec K ⟶ Spec k`;
- an arbitrary scheme `X : Scheme.{u}` and an arbitrary morphism
  `p : X ⟶ Spec k`;
- an actual line bundle `L : LineBundle X`.

`CategoryTheory.Limits.pullback p b` is Mathlib's pullback in `Scheme.{u}`,
the base change `X_K = X ×_{Spec k} Spec K` of the `k`-scheme `(X, p)` along
`b`. Its first projection `pullback.fst p b : X_K ⟶ X` is the base-change
projection, and its second projection `pullback.snd p b : X_K ⟶ Spec K` is
the structure morphism of the base change. The hypothesis is ampleness of the
actual pullback of the given bundle `L` along the first projection. The
conclusion is ampleness of that same `L` on `X`. It does not assert the
existence of some other ample bundle on `X`.

This is the converse of the published
`Langlands.AlgebraicGeometry.Picard.FieldBaseChangeAmpleStatement`, which has
the same binders with hypothesis and conclusion exchanged. A private check
compiled the conjunction of the two statements into the equivalence
`L.IsAmple ↔ ((LineBundle.pullback (pullback.fst p b)).obj L).IsAmple`. This
module neither imports nor proves the preservation statement.

### Arbitrary field maps

The statement quantifies over every scheme morphism `b`, so a caller need not
choose an `Algebra k K` instance first. `Spec` is fully faithful on
commutative rings (`AlgebraicGeometry.Spec.fullyFaithful`; `Spec.preimage`
and `Spec.map_preimage` write any morphism of spectra as `Spec.map` of a ring
map). So every such `b` is `Spec.map φ` for a unique ring homomorphism
`φ : k → K`, which is a field embedding and makes `K` a field extension of
`k`. Conversely, an algebra structure gives the instance
`b := Spec.map (CommRingCat.ofHom (algebraMap k K))`. A private check
compiled both this specialization and the one to `K := AlgebraicClosure k`,
together with the `Iff.rfl` identification of the declaration with the
contract's displayed text.

### Actual bundles, pullback and ampleness

`LineBundle X` is the published full subcategory of actual `X.Modules` that
are locally isomorphic to the structure sheaf. `LineBundle.pullback f` is
the published lift of `Scheme.Modules.pullback f` to line bundles. Its
preservation of local rank one is already proved in
`Langlands/AlgebraicGeometry/Picard/LineBundlePullback.lean`. Both the
hypothesis and the conclusion use the published `LineBundle.IsAmple`
unchanged. For a line bundle `M` on a scheme `Y`, `M.IsAmple` is

```text
CompactSpace Y ∧ ∀ y : Y, ∃ n : ℕ, 1 ≤ n ∧ ∃ s : M.powSections n,
  y ∈ M.sectionOpen s ∧ IsAffineOpen (M.sectionOpen s).
```

`M.powSections n` is the type of global sections of the actual sheafified
tensor power `Langlands.Scheme.Modules.tensorPow M.obj n`. The open
`M.sectionOpen s` is `trivializationOpen (tensorPow M.obj n) s`, the largest
open on which the morphism from the structure sheaf sending `1` to `s` is an
isomorphism. The **whole** generation open must be affine. An affine
neighbourhood inside it on which the section generates is not enough. The
conclusion is this definition for `L` on `X`. It includes compactness of `X`
and sections of positive tensor powers of `L` itself, defined over `X`, not
over `X_K`. See `Langlands/AlgebraicGeometry/Picard/Ample.md` for these
definitions and their comparison with Stacks Definition 28.27.1.

## Scope

The statement covers every universe `u` and every characteristic. It also
covers imperfect `k`, and finite, infinite, separable, inseparable, algebraic
and transcendental extensions. The case `K = k` with any endomorphism `b` is
included. `X` and `p` are arbitrary, so the empty scheme, dimension zero and
non-noetherian schemes are covered.

There is no abelian-scheme, finite-type, properness, projectivity,
separatedness, quasi-compactness, algebraic-closure, finite-extension,
tensor-preservation, residue-comparison or certificate premise.

## Derived provenance

This is a derived specialization of the Stacks Project, not a literal
quotation of one source statement. It combines fpqc descent of relative
ampleness with the identification of relative and absolute ampleness over an
affine base.

**Relative ampleness.**
[Morphisms, Definition 29.38.1, tag 01VG](https://stacks.math.columbia.edu/tag/01VG)
says that for `f : X → S` and an invertible `𝓛`, `𝓛` is *ample on `X/S`*
(`f`-ample) if `f` is quasi-compact and the restriction of `𝓛` to
`f⁻¹(V)` is ample for every affine open `V ⊂ S`. The Library has no Lean
definition of relative ampleness. The statement uses only the absolute
`IsAmple`, and the relative notion appears only in this derivation.

**Relative and absolute ampleness over an affine base.**
[Morphisms, Lemma 29.38.5, tag 01VK](https://stacks.math.columbia.edu/tag/01VK)
says that if `S` is affine, then `𝓛` is `f`-relatively ample if and only if
`𝓛` is ample on `X`.

**fpqc descent of relative ampleness.**
[Descent, Lemma 35.25.6, tag 0D2P](https://stacks.math.columbia.edu/tag/0D2P)
says: let `f : X → S` be a morphism, `𝓛` an invertible `𝒪_X`-module and
`{gᵢ : Sᵢ → S}` an fpqc covering, with base changes `fᵢ : Xᵢ → Sᵢ` and
pullbacks `𝓛ᵢ` of `𝓛` to `Xᵢ`. Then `𝓛` is ample on `X/S` if and only if
every `𝓛ᵢ` is ample on `Xᵢ/Sᵢ`. The present proposition is the field case of
the implication (2) ⇒ (1).

**The covering.** Write `b = Spec.map φ` as above, so `K` is a field
extension of `k` via `φ`.
[Descent, Section 35.6, tag 0CDQ](https://stacks.math.columbia.edu/tag/0CDQ)
states: "Let `k'/k` be a field extension. Then `{Spec(k') → Spec(k)}` is an
fpqc covering." So `{b}` is an fpqc covering of `Spec k`. The same follows
from the criterion used in the proof of Lemma 35.25.1 (tag 02LB): a flat,
quasi-compact, surjective morphism `X → Y` gives an fpqc covering
`{X → Y}`. Here `b` is flat because `K` is flat over the field `k`. It is
quasi-compact as a morphism of affine schemes. It is surjective because
`Spec k` is one point and `Spec K` is nonempty.

**Specialization.** In 0D2P take

- `S := Spec k`, `f := p`;
- the index set a single point, with `S₁ := Spec K` and `g₁ := b`;
- `X₁ := pullback p b`, `f₁ := pullback.snd p b`;
- `𝓛₁ := (LineBundle.pullback (pullback.fst p b)).obj L`, the pullback of
  `𝓛` along the projection `X₁ → X`.

The hypothesis says `𝓛₁` is ample on `X₁`. Since `S₁ = Spec K` is affine,
01VK turns this into ampleness of `𝓛₁` on `X₁/S₁`. Then 0D2P (2) ⇒ (1) gives
ampleness of `𝓛` on `X/S`. Since `S = Spec k` is affine, 01VK turns this
back into absolute ampleness of `𝓛` on `X`, which is the conclusion.

Source invertible modules are rendered as the published actual
`LineBundle`s, source pullback as `LineBundle.pullback`, and source
ampleness on `X` as the published `IsAmple`. Nothing is dropped from the
conclusion and no hypothesis is added. Quasi-compactness of `X` (and of `p`)
and the existence of sections over `X` are consequences, not premises.

## Original sources and reading record

**`stacks-fixed-bundle-field-ampleness-2026-11-02`**, directory SHA256
`59d0167308d941af551e6682a937e5c9fcc307cc26b5687d92ad81b0eb231b0c`, retained
at
`literature/Stacks Project - Fixed-bundle ampleness under field extension, fpqc descent (Tags 0D2P and 02LB, HTML snapshot 2026-11-02)`.
Worker 712 read the complete page `0D2P.html` (Lemma 35.25.6, statement and
proof, no comments). The proof of (2) ⇒ (1) shows that `f` is
quasi-compact and separated (Lemmas 35.23.1, 35.23.6 and Morphisms 29.38.3).
It then uses that `𝒜 = ⨁_{d ≥ 0} f_*𝓛^{⊗d}` commutes with flat base change
(Cohomology of Schemes, Lemma 30.5.2) and that `𝒪_{X,x} → 𝒪_{Xᵢ,xᵢ}` is
faithfully flat. Finally `r_{𝓛,ψ} : X → Proj_S(𝒜)` is an open immersion by
Lemma 35.23.18, and Morphisms, Lemma 29.38.4 concludes. Worker 712 also read
the whole of Section 35.25 in `02LB.html`, with its three section comments
(#7749, September 2022; #7994 and #7995, January 2023). They concern why the
diagonal in the proof of Lemma 35.25.1 is an isomorphism. A reference was
added there, and nothing changes Lemma 35.25.6.

**`stacks-field-base-change-ampleness-2026-10-26`**, directory SHA256
`42e3c9b9a073a223fab83518d24f49215baffa88c4eb11c2f72a0a95cec4ac17`, retained
at
`literature/Stacks Project - Field base-change preservation of ampleness (HTML snapshot 2026-10-26)`.
Worker 712 read Definition 29.38.1 in `01VG.html` and Lemma 29.38.5 in
`01VK.html`, with its proof and comments. The two comments (#2703, #2741,
August 2017) add the reference EGA II, Corollary 4.6.6.

**`stacks-descent-ed88ff78-2026`**, The Stacks Project, *Descent*, version
ed88ff78 compiled 14 July 2026, file SHA256
`28e718bac216bb7c4584e9edb1d25d6420ee19a6cd536742c58599242ff8cad4`.
Worker 712 read PDF page 19, Section 6 (online Section 35.6, tag 0CDQ,
"Galois descent for quasi-coherent sheaves"), whose second paragraph contains
the fpqc covering statement quoted above. Worker 712 also read PDF page 63,
where Lemma 25.6 (tag 0D2P) and its proof agree with the HTML page.

The working Library base has no erratum file for these sources.

## Proof obligations for the future exact-target proof

A proof of this whole proposition must work with the published definitions,
with no extra outer hypothesis. The source theorems do not construct the
following in Lean. Write `f := pullback.fst p b` and
`L_K := (LineBundle.pullback f).obj L`.

1. **Compactness.** `f` is surjective as a base change of the surjective
   `b`. So `X` is the continuous image of the compact space `X_K` and is
   compact.
2. **Sections over `X`.** The conclusion needs, for each `x : X`, some
   `n ≥ 1` and a section of the actual `tensorPow L.obj n` over `X` whose
   whole generation open contains `x` and is affine. The hypothesis supplies
   such sections only for tensor powers of `L_K` over `X_K`, and they need
   not be pullbacks of sections over `X`. The source route identifies
   `⨁_d Γ(X_K, 𝓛_K^{⊗d})` with the flat base change of
   `⨁_d Γ(X, 𝓛^{⊗d})` along `k → K`. This needs `X` quasi-compact and
   quasi-separated (the source deduces separatedness from the hypothesis).
   In Lean it also needs a comparison between the pullback of a published
   tensor power and the published tensor power of the pullback, together
   with the pullback of global sections.
3. **Affine whole generation opens.** The source then shows that the
   canonical morphism from `X` to the relative `Proj` of that graded algebra
   is an open immersion, by fpqc descent of open immersions along `b`
   (Lemma 35.23.18), and concludes by Morphisms, Lemma 29.38.4. Any Lean
   route must finally exhibit sections over `X` whose **whole** generation
   opens are affine. In particular it must compare the preimage under `f` of
   such a generation open with the generation open of the pulled-back
   section.

A route that literally follows the source would first need Library
definitions of relative ampleness and of restriction to preimages of affine
opens, which the Library does not have.

This module adds no axiom and discharges none of these obligations.
