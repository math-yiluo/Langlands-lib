# Preservation of ampleness under field base change

`Langlands.AlgebraicGeometry.Picard.FieldBaseChangeAmpleStatement.{u}` is a
universe-polymorphic definition of type `Prop`. This module states the
result and supplies no proof.

Worker 712 implemented this pair. Worker 420 supplied the specification, the
source selection and the reuse boundaries in the task contract.

## Exact statement

The checked declaration, in namespace `Langlands.AlgebraicGeometry.Picard`
with `CategoryTheory` and `AlgebraicGeometry` open, is

```lean
def FieldBaseChangeAmpleStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k)) (L : LineBundle X),
    L.IsAmple →
      ((LineBundle.pullback (CategoryTheory.Limits.pullback.fst p b)).obj L).IsAmple
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
projection. The conclusion concerns the actual pullback of the given bundle
`L` along this projection, and not the existence of some other ample bundle
on `X_K`.

### Arbitrary field maps

The statement quantifies over every scheme morphism `b`, so a caller need not
choose an `Algebra k K` instance first. `Spec` is fully faithful on
commutative rings (`AlgebraicGeometry.Spec.fullyFaithful`; `Spec.preimage`
and `Spec.map_preimage` write any morphism of spectra as `Spec.map` of a ring
map). So
every such `b` is `Spec.map φ` for a unique ring homomorphism `φ : k → K`,
which is a field embedding. Conversely, an algebra structure gives the
instance `b := Spec.map (CommRingCat.ofHom (algebraMap k K))`. A private
check compiled both this specialization and the one to
`K := AlgebraicClosure k`, together with the `Iff.rfl` identification of the
declaration with the contract's displayed text.

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
conclusion applies this definition on `X_K` to the pulled-back bundle,
including its compactness requirement. See
`Langlands/AlgebraicGeometry/Picard/Ample.md` for these definitions and
their comparison with Stacks Definition 28.27.1.

## Scope

The statement covers every universe `u` and every characteristic. It also
covers imperfect `k`, and finite, infinite, separable, inseparable, algebraic
and transcendental extensions. The case `K = k` with any endomorphism `b` is
included. `X` and `p` are arbitrary, so the empty scheme, dimension zero and
non-noetherian schemes are covered.

There is no abelian-scheme, finite-type, properness, projectivity,
separatedness, algebraic-closure, finite-extension, tensor-preservation,
residue-comparison or certificate premise.

## Derived provenance

This is a derived specialization of the Stacks Project, not a literal
quotation of one source statement.

Stacks Section 29.38 recalls the absolute notion: `𝓛` is ample on `X` if `X`
is quasi-compact and every point of `X` lies in an affine open of the form
`X_s` with `s ∈ Γ(X, 𝓛^{⊗n})` and `n ≥ 1` (Properties, Definition 28.27.1).

**Route through relative ampleness.**
[Lemma 29.38.9, tag 0893](https://stacks.math.columbia.edu/tag/0893) says:
if `f : X → S` is a morphism, `S' → S` a morphism, `f' : X' → S'` the base
change and `𝓛'` the pullback of `𝓛` to `X'`, then `𝓛'` is `f'`-ample whenever
`𝓛` is `f`-ample.
[Lemma 29.38.5, tag 01VK](https://stacks.math.columbia.edu/tag/01VK) says
that over an affine base `S`, `𝓛` is `f`-relatively ample if and only if `𝓛`
is ample on `X`. The present proposition specializes 0893 as follows:

- `S := Spec k`, `f := p`;
- `S' := Spec K`, with `b` as the morphism `S' → S`;
- `X' := pullback p b`, `f' := pullback.snd p b`;
- `𝓛' := (LineBundle.pullback (pullback.fst p b)).obj L`, the pullback of `𝓛`
  along the projection `X' → X`.

Since `Spec k` is affine, 01VK turns ampleness of `L` into `p`-ampleness, and
0893 then gives `pullback.snd p b`-ampleness of `𝓛'`. Since `Spec K` is
affine, 01VK turns this back into absolute ampleness of `𝓛'` on `X'`.

**Direct route.**
[Lemma 29.38.7(2), tag 0892](https://stacks.math.columbia.edu/tag/0892) says
that if `𝓜` is ample on `Y` and `f : X → Y` is quasi-affine, then `f^*𝓜` is
ample. Here `f := pullback.fst p b`. This projection is the base change of the
morphism `b` of affine schemes, which is affine. Affine morphisms are stable
under base change, as cited in the proof of 0893 (Lemma 29.11.9). So the
projection is affine, hence quasi-affine (every affine morphism is
quasi-affine), and 0892(2) applies directly.

Source invertible modules are rendered as the published actual
`LineBundle`s, source pullback as `LineBundle.pullback`, and source
ampleness as the published `IsAmple`. Nothing is dropped from the
conclusion and no hypothesis is added. Quasi-compactness of `X_K` and
affineness of the projection are consequences of the setting, not premises.

## Original source and reading record

Registered source `stacks-field-base-change-ampleness-2026-10-26`, directory
SHA256 `42e3c9b9a073a223fab83518d24f49215baffa88c4eb11c2f72a0a95cec4ac17`,
retained at
`literature/Stacks Project - Field base-change preservation of ampleness (HTML snapshot 2026-10-26)`.

On October 26, 2026 Worker 712 read the complete retained Section 29.38
(`01VG.html`: Definition 29.38.1, Lemmas 29.38.2–29.38.10, all proofs and the
section's three comments) and the individual pages `01VK.html`, `0892.html`
and `0893.html`, with their proofs and comments.

- The section's comments #7423, #7425 and #7444 (June 2022) concern the
  separatedness of `X` used in the proof of 0892. The retained proof
  contains the added justification: `Y` is separated by Properties, Lemma
  28.27.8, `f` is separated by Lemma 29.38.3, so `X` is separated.
- The two comments on 01VK (#2703, #2741, August 2017) add the reference
  EGA II, Corollary 4.6.6.
- The pages 0892 and 0893 have no direct comments.

The working Library base has no erratum file for this source.

## Proof obligations for the future exact-target proof

A proof of this whole proposition must work with the published definitions,
with no extra outer hypothesis. The source theorems do not construct the
following comparisons in Lean. Along the direct route, with
`f := pullback.fst p b`:

1. Show that `f` is affine, for instance through Mathlib's
   `AlgebraicGeometry.isAffineHom_isStableUnderBaseChange`, and deduce
   `CompactSpace` of `X_K` from compactness of `X`.
2. For `n ≥ 1` and `s : L.powSections n`, build a global section of
   `tensorPow ((LineBundle.pullback f).obj L).obj n`. This needs an actual
   comparison between the pullback of a published tensor power and the
   published tensor power of the pullback, together with the pullback of
   global sections.
3. Prove that the **whole** generation open of that section is
   `f ⁻¹ᵁ (L.sectionOpen s)`. Its affineness then follows from
   `IsAffineOpen.preimage` for the affine morphism `f`.

Any use of `LineBundle.isAmple_iff_nonvanishingLocus` must also establish
local rank one of the actual tensor powers. The residue open comparison it
uses is published as
`Langlands.SchemeModule.lineBundleResidueOpenComparison`. A route through
relative ampleness would first need Library definitions of relative
ampleness and of restriction to preimages of affine opens.

This module adds no axiom and discharges none of these obligations.
