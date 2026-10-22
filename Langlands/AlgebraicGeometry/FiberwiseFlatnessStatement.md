# The finite-presentation fibrewise flatness criterion

`Langlands.AlgebraicGeometry.FiberwiseFlatnessStatement` is a
proposition-valued definition in
`Langlands.AlgebraicGeometry.FiberwiseFlatnessStatement`. It states the first
assertion of Stacks Project tag
[039E](https://stacks.math.columbia.edu/tag/039E), Lemma 37.16.4, the
*critère de platitude par fibres* in its finitely presented form.

## Statement

For every scheme `S : Scheme.{u}`, objects `X Y : Over S`, and morphism
`f : X ⟶ Y` of `S`-schemes, assume:

1. the structure morphism `X.hom : X.left ⟶ S` is `Flat`;
2. `X.hom` is `LocallyOfFinitePresentation`;
3. the structure morphism `Y.hom : Y.left ⟶ S` is `LocallyOfFiniteType`;
4. for every point `s : S`, the fibre morphism
   `((Over.pullback (S.fromSpecResidueField s)).map f).left` is `Flat`.

Then the underlying scheme morphism `f.left : X.left ⟶ Y.left` is `Flat`.

All four predicates are Mathlib's scheme-morphism classes
`AlgebraicGeometry.Flat`, `AlgebraicGeometry.LocallyOfFinitePresentation` and
`AlgebraicGeometry.LocallyOfFiniteType`, used here as ordinary hypotheses.

## The fibre morphism

`S.fromSpecResidueField s : Spec κ(s) ⟶ S` is Mathlib's canonical morphism
from the spectrum of the residue field at `s`. The functor
`Over.pullback (S.fromSpecResidueField s) : Over S ⥤ Over (Spec κ(s))` is the
actual categorical base change. It sends `X` to the scheme-theoretic fibre
product `X_s = X ×_S Spec κ(s)` with its second projection, and sends `f` to the
induced morphism `f_s : X_s ⟶ Y_s` of `κ(s)`-schemes, given by
`pullback.lift (pullback.fst _ _ ≫ f.left) (pullback.snd _ _) _`
(Mathlib's simp lemma `Over.pullback_map_left`). Its `.left` is therefore the
morphism written `f_s : X_s → Y_s` in Stacks Section 37.16. The hypothesis
concerns these scheme morphisms; it is not a condition on points, on rational
points, or on an abstract indexed family. The quantifier ranges over all
points `s : S`, not only closed points.

## Comparison with the original source

The registered source is the retained Stacks HTML file `039E.html`
(Lemma 37.16.4), with its proof referring to Theorem 37.16.2 in `039A.html`.
Lemma 37.16.4 reads: let `S` be a scheme and `f : X → Y` a morphism of schemes
over `S`; assume `X` is locally of finite presentation over `S`, `X` is flat
over `S`, for every `s ∈ S` the morphism `f_s : X_s → Y_s` is flat, and `Y` is
locally of finite type over `S`. Then `f` is flat.

The Lean hypotheses correspond one-to-one to these:

| Stacks Lemma 37.16.4 | Lean |
| --- | --- |
| `S` a scheme; `f : X → Y` a morphism over `S` | `S : Scheme.{u}`, `X Y : Over S`, `f : X ⟶ Y` |
| `X` locally of finite presentation over `S` | `LocallyOfFinitePresentation X.hom` |
| `X` flat over `S` | `Flat X.hom` |
| `f_s : X_s → Y_s` flat for every `s ∈ S` | `∀ s : S, Flat ((Over.pullback (S.fromSpecResidueField s)).map f).left` |
| `Y` locally of finite type over `S` | `LocallyOfFiniteType Y.hom` |
| conclusion: `f` is flat | `Flat f.left` |

The base `S` is arbitrary. The statement adds no noetherian, quasicompact,
quasi-separated, field, group, properness, connectedness, or surjectivity
hypothesis, and does not assume that `Y → S` is flat or of finite
presentation. The universe is a single parameter `u`, the universe of
`Scheme.{u}`.

**Omitted second assertion.** Lemma 37.16.4 also asserts that if `f` is
surjective then `Y` is flat over `S`. That assertion is deliberately not part
of this proposition. Its Lean conclusion would differ (flatness of `Y.hom`
under the extra hypothesis that `f.left` is surjective), and it is not needed
by the intended application below.

The proof in Stacks deduces the lemma from Theorem 37.16.2, the
finite-presentation pointwise criterion for a finitely presented
quasi-coherent module, applied to `𝓕 = 𝒪_X`. That theorem works with the
local ring maps `𝒪_{S,s} → 𝒪_{Y,y} → 𝒪_{X,x}` and does not need noetherian
hypotheses. The present statement is the global form for the structure sheaf;
the module version and the openness assertion of Theorem 37.16.2 are not
stated here.

## Why the finite-presentation version, not SGA 1

The same criterion is often quoted from SGA 1, Exposé IV, Corollary 5.9
(registered source `sga1-arxiv-math-0206203v2`, recomposed edition, printed
page 81, PDF page 97, original pagination 99–100 in the margin). That
corollary is a statement about local homomorphisms `A → B → C` of
**noetherian local rings** and a finite `C`-module `M`; it also assumes `B`
flat over `A`. Applied at stalks `𝒪_{S,s} → 𝒪_{Y,y} → 𝒪_{X,x}`, it therefore
only covers schemes whose local rings are noetherian (and, as stated, `Y` flat
over `S`). It cannot by itself supply the arbitrary-base scope stated here,
where `S`, `X` and `Y` need not be locally noetherian. The locally noetherian
global variant in Stacks is the separate Lemma 37.16.3, which is not the
statement formalized here. The finite-presentation hypotheses on `X → S` and
the finite type hypothesis on `Y → S` are exactly what Theorem 37.16.2 uses in
place of noetherian hypotheses, and this is the version formalized here.

## Intended application

The published statement
`Langlands.GroupScheme.FiberwiseIsogenyStatement` (module
`Langlands.AbelianScheme.FiberwiseIsogenyStatement`) needs the flatness
component of a fibrewise isogeny criterion for smooth proper group schemes.
Smoothness of the source structure map gives `Flat` and
`LocallyOfFinitePresentation`, smoothness of the target structure map gives
`LocallyOfFiniteType`, and the flatness component of the fibre isogeny
hypothesis is literally the fibre hypothesis above, for `X = G.X`, `Y = H.X`
and the morphism `f.hom.hom`, since `Functor.mapGrp` acts on underlying
morphisms by the functor itself. A private development check confirmed that
this application typechecks; it is not part of this artifact.

## Status

This file states the criterion only. No proof is supplied, and the criterion
is not installed as an axiom, an instance, or a field of a structure. Proving
`FiberwiseFlatnessStatement` is a separate exact-target task. A search of the
pinned Mathlib (`AlgebraicGeometry/Morphisms`, `RingTheory/Flat`,
`RingTheory/LocalRing/Module.lean`, `RingTheory/Smooth/Fiber.lean`) found no
theorem stating this criterion or Stacks Theorem 37.16.2.

## Sources

- `stacks-fiberwise-isogeny-2026-10-22`, folder SHA256
  `db82f1556e926672cc2278329e279f7fcaceb540c23e323a7c266a6a6b1f0dca`:
  `039E.html`, Lemma 37.16.4 (the statement), and `039A.html`, Section 37.16,
  Theorem 37.16.2 (the finitely presented criterion used in its proof) and
  Lemma 37.16.3 (the locally noetherian variant).
- `sga1-arxiv-math-0206203v2`, SHA256
  `8e64218d356456c534eebf996940f0f957e43b54f1a080241debe12cbaf60d3c`:
  Exposé IV, Corollary 5.9, printed page 81, PDF page 97; cited only to delimit
  its noetherian local scope.
