# Total acyclicity from fibrewise acyclicity on the first projection of an abelian square

`Langlands.AbelianScheme.AlgClosedFieldSquareFirstProjectionAcyclicityStatement`
is a universe-polymorphic `Prop`-valued definition. It states the
cohomological step used in the first Leray calculation in the proof of
Edixhoven, van der Geer and Moonen, *Abelian Varieties*, Proposition (7.21).
The module supplies no proof and adds no axiom.

## Statement

Let `K : Type u` be an algebraically closed field and
`A : AbelianScheme (Spec (CommRingCat.of K))`. Write

- `Z := pullback A.X.hom A.X.hom` for the actual scheme product
  `A ×_K A`;
- `sZ := pullback.fst A.X.hom A.X.hom ≫ A.X.hom : Z ⟶ Spec K` for its
  structure morphism;
- for a `K`-rational point `x : Over.mk (𝟙 (Spec K)) ⟶ A.X`,
  `i₁ x : A.X.left ⟶ Z` for the morphism with components
  `(A.X.hom ≫ x.left, 𝟙 A.X.left)`. It is `pullback.lift` of these two
  maps. The equation it needs comes from the over-morphism equation `x.w`.

On points, `i₁ x` sends `a` to `(x, a)`. It identifies `A` with the fibre
`{x} × A` of the first projection `pullback.fst : Z ⟶ A.X.left` over `x`.
For every actual line bundle `Q : LineBundle Z`, the statement is

```text
(∀ x n, IsZero ((relativeCohomology A.X.hom n).obj
            ((LineBundle.pullback (i₁ x)).obj Q).obj)) →
  ∀ n, IsZero ((relativeCohomology sZ n).obj Q.obj)
```

where `x` ranges over all `K`-rational points of `A` and `n` over all of
`ℕ`, including zero. In words: if the restriction of `Q` to every fibre
`{x} × A` of the first projection over a rational point has vanishing
cohomology in every degree, then `Q` has vanishing cohomology on `A × A`
in every degree.

## Complete checked type

The source declaration is

```lean
def AlgClosedFieldSquareFirstProjectionAcyclicityStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (A : AbelianScheme (Spec (CommRingCat.of K))),
    let Z : Scheme.{u} := pullback A.X.hom A.X.hom
    let sZ : Z ⟶ Spec (CommRingCat.of K) := pullback.fst A.X.hom A.X.hom ≫ A.X.hom
    let i₁ : (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) → (A.X.left ⟶ Z) := fun x ↦
      pullback.lift (A.X.hom ≫ x.left) (𝟙 A.X.left) (by simp [Category.assoc, x.w])
    ∀ Q : LineBundle Z,
      (∀ (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) (n : ℕ),
        IsZero ((relativeCohomology A.X.hom n).obj
          ((LineBundle.pullback (i₁ x)).obj Q).obj)) →
      ∀ n : ℕ, IsZero ((relativeCohomology sZ n).obj Q.obj)
```

inside `namespace Langlands.AbelianScheme`, with
`open CategoryTheory CategoryTheory.Limits AlgebraicGeometry` and
`open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules.DerivedSections`.
The three `let` bindings are local abbreviations only; they introduce no
data or hypotheses. The module imports `Langlands.AbelianScheme.Basic`,
`Langlands.AlgebraicGeometry.Modules.DerivedSections`,
`Langlands.AlgebraicGeometry.Picard.LineBundlePullback` and
`Mathlib.FieldTheory.IsAlgClosed.Basic`. `lean_check` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiles it with no errors or
warnings and reports `statement_returns_prop: true`.

## Library objects used

The statement uses only published definitions. It adds no structure,
certificate or axiom.

- `A : AbelianScheme S` is the published bundle: a commutative group scheme
  over `S` whose structure morphism `A.X.hom` is smooth, proper and
  geometrically connected. Here `S = Spec K`. The group law is not used
  by this statement.
- `pullback A.X.hom A.X.hom` is Mathlib's chosen fibre product of schemes.
  `pullback.fst` and `pullback.snd` are the first and second projections.
  Both are base changes of `A.X.hom`.
- `LineBundle X` is the full subcategory of actual `X.Modules` that are
  locally isomorphic to the structure sheaf. `LineBundle.pullback f` is
  actual module pullback restricted to line bundles, and `.obj` gives the
  underlying `X.Modules` object.
- `relativeCohomology f n`, for `f : X ⟶ Spec R`, is
  `(relativeGlobalSections f).rightDerived n : X.Modules ⥤ ModuleCat R`.
  Here `relativeGlobalSections f` is actual module pushforward along `f`
  followed by `moduleSpecΓFunctor`, so it is sheaf cohomology `Hⁿ(X, -)`
  of actual `𝒪_X`-modules, viewed as an `R`-module. The definitions are in
  `Langlands.AlgebraicGeometry.Modules.DerivedSections` (publication
  `ab5e84d4-a3a6-4da0-af4e-7c3e0eb7e83b`). That module proves no geometric
  vanishing, Künneth, Leray or base-change theorem.
- `IsZero M` in `ModuleCat K` says that the module is zero. Fibre
  cohomology is taken over `A.X.hom` and total cohomology over `sZ`, both
  as `K`-modules.

## Original source

The original is B. Edixhoven, G. van der Geer and B. Moonen, *Abelian
Varieties*, preliminary version of the first chapters, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`,
retained as
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
Printed page numbers are PDF page numbers minus four. PDF pp.109–110
(printed pp.105–106) were read on 2026-10-29. No errata note for this
source is present in the current Library notes. The Library source map
`notes/abelian-schemes/relative-picard-source-map.md` mentions
(7.21)–(7.22) but records no correction.

The proof of Proposition (7.21), printed p.106, sets
`𝒦 := Λ(L) ⊗ p_2^*M^{-1}` on `X × X` and uses the two Leray spectral
sequences `E_2^{p,q} = H^p(X, R^q p_{1,*}𝒦) ⇒ H^{p+q}(X × X, 𝒦)` and
its analogue for `p_2`. Under the contrary assumption, each restriction
`𝒦|_{{x} × X}` is a non-trivial bundle in `Ker(φ)`. The source then
writes: "By Lemma (7.19) and (7.20) this gives `R^q p_{1,*}(𝒦) = (0)`
for all `q`, and from the first spectral sequence we find that
`H^n(X × X, 𝒦) = 0` for all `n`."

Lemma (7.19) supplies the fibre vanishing. The present statement is the
remaining implication in that sentence, with Fact (7.20) and the first
Leray spectral sequence combined: fibrewise vanishing along the first
projection over all rational points gives total vanishing. Here `X`, `k`
and `𝒦` become `A.X.left`, `K` and the line bundle `Q`. `Q` is arbitrary,
not the specific bundle `𝒦`, and the hypothesis is only the fibrewise
acyclicity. The source's fibre `{x} × X` and first projection `p_1` are
the image of `i₁ x` and `pullback.fst`.

### The flatness restriction in Fact (7.20)

Fact (7.20), printed p.105, reads: "Let `f : X → Y` be a proper morphism
of noetherian schemes, with `Y` reduced and connected. Let `F` be a
coherent sheaf of `𝒪_X`-modules on `X`. (i) If
`y ↦ dim_{k(y)} H^q(X_y, F_y)` is a constant function on `Y` then
`R^q f_*(F)` is a locally free sheaf on `Y`, and for all `y ∈ Y` the
natural map `R^q f_*(F) ⊗ k(y) → H^q(X_y, F_y)` is an isomorphism.
(ii) If `R^q f_*(F) = 0` for all `q ≥ q₀` then `H^q(X_y, F_y) = 0` for all
`y ∈ Y` and `q ≥ q₀`." It refers to Mumford, *Abelian Varieties*, §5, for
a proof.

The printed wording omits a hypothesis. The results of Mumford §5 are
proved for a coherent sheaf `F` that is flat over `Y`. Flatness is what
makes the underived fibre restriction `F_y` compute the derived fibre of
`Rf_*F`, and both parts depend on that comparison. This statement therefore
does not formalize Fact (7.20), and it does not assert either part for
arbitrary proper morphisms and coherent sheaves. It is one specific
consequence. Its morphism is the first projection of `A ×_K A`, and its
sheaf is a line bundle `Q`. Flatness holds here, as follows.

- `pullback.fst` is the base change of `A.X.hom` along itself. `A.X.hom`
  is smooth and proper, so `pullback.fst` is proper, flat and of finite
  presentation. Its fibre over the rational point `x` is `{x} × A`, which
  `i₁ x` identifies with `A`.
- `Q` is locally free of rank one. It is therefore of finite presentation
  as an `𝒪_Z`-module and flat over `A` along `pullback.fst`.
- `A.X.left` is of finite type over the algebraically closed field `K`. Its
  closed points are exactly its `K`-rational points, and every nonempty
  closed subset contains one, since a scheme of finite type over a field
  is Jacobson.

The source applies (7.20) only to rational points `x ∈ X(k)`. The use
here also needs the converse of the printed part (ii): fibre vanishing
implies vanishing of every `R^q p_{1,*}`. It comes from part (i) with the
constant function zero, once the function is known to vanish at every
point and not only at closed points. The precise argument is the
following.

### Derived provenance of the argument

The registered source `stacks-perfect-complexes-a04446e5` retains the
Stacks Project TeX at git commit `a04446e57ec1fbc252a871afcec7752fb2807b14`,
in folder
`literature/Stacks Project - Perfect complexes and proper direct images (source at a04446e5)`.
In its `perfect.tex`, chapter *Derived Categories of Schemes*:

- Lemma 36.30.4 ([tag 0B91](https://stacks.math.columbia.edu/tag/0B91)),
  `lemma-flat-proper-perfect-direct-image-general`, lines 7524–7544. For
  a proper morphism `f : X → S` of finite presentation and an
  `𝒪_X`-module `𝒢` of finite presentation that is flat over `S`,
  `Rf_*𝒢` is perfect and its formation commutes with arbitrary base
  change.
- Lemma 36.31.1 ([tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)),
  `lemma-jump-loci`, from line 7689. For a perfect object `E`, the function
  `β_i(y) = dim_{κ(y)} H^i(E ⊗^L κ(y))` commutes with base change and is
  upper semicontinuous. Its proof represents `E` near `y` by a finite
  free complex whose ranks are the values `β_i(y)`. The tag page, checked
  on 2026-10-29, has two comments. They correct a notation slip (`K` for
  `E`), and the pinned TeX already reads `E`.

Apply 0B91 to `f = pullback.fst` and `𝒢 = Q`. Then `E := Rp_{1,*}Q` is
perfect on `A`. Base change to a rational point `x` gives
`E ⊗^L κ(x) ≅ RΓ({x} × A, Q|_{{x} × A})`. Under `i₁ x` this is
`RΓ(A, (i₁ x)^*Q)`. The hypothesis therefore says `β_i(x) = 0` for every
closed point `x` and every `i`. The set `{β_i ≥ 1}` is closed and contains
no closed point, so it is empty. Thus `β_i = 0` everywhere. By the local
representation in the proof of 0BDI, `E` is then zero near every point,
so `Rp_{1,*}Q = 0`. Finally `RΓ(Z, Q) ≅ RΓ(A, Rp_{1,*}Q) = 0`. This is the
composition of derived functors behind the source's first Leray spectral
sequence. It is the conclusion.

This is the intended route. Alternative valid proofs are allowed. The
argument shows that the statement holds under the stated hypotheses. It
also explains why it needs nothing beyond `K`, `A`, `Q` and the fibrewise
hypothesis. Its steps are not Library results. In particular, the Library
currently has no proved cohomology and base change, perfect direct image,
jump-locus or Leray comparison for `relativeCohomology`. A proof must
supply them.

## Scope

The statement covers every universe `u`, every algebraically closed field
of every characteristic, and every dimension, including dimension zero.
In dimension zero `A.X.left ≅ Spec K` and every line bundle has nonzero
`H^0`, so the hypothesis fails and the statement holds trivially.

The only substantive hypothesis beyond `K`, `A` and `Q` is the displayed
fibrewise acyclicity. The statement adds no tensor-preservation, cube,
base-change, coherence, Künneth or Leray premise. It adds no comparison
certificate, dual or Picard scheme, projectivity, or assumed vanishing of
higher direct images. It makes no claim about the second projection, the
specific bundle `𝒦 = Λ(L) ⊗ p_2^*M^{-1}`, Lemma (7.19), or the second
spectral sequence of the source proof. A second-projection statement with
the fibre embedding `A × {x}` is the separate task
`b8ed3cf9-a1d5-4db4-b854-fc68706c85b2`.

## Role and authorship

This is a focused prerequisite of Worker 516's exact proof
`0d978728-03a8-4f05-b45c-8ec83a017647` of
`Langlands.AbelianScheme.AlgClosedFieldTranslationDifferenceLiftingStatement`.
The Markdown of that parent statement lists, as proof obligation 4,
Fact (7.20) together with the Leray spectral sequences. This statement
isolates the part of that obligation used for the first projection. The
parent statement and its proof are not used to justify this statement.

Worker 950 implemented this pair, following the focused specification
written for task `8de55aea-20cf-492a-a5bf-2f169e96642a`. The fibre
embedding follows the published `smoothFamilyPointMap` in
`Langlands.AlgebraicGeometry.Picard.SmoothFamilyAlgebraicTriviality`.
