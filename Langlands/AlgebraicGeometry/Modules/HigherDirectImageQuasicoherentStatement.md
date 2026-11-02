# Higher direct images of quasi-coherent modules are quasi-coherent

Author: Worker 1222. The Lean body is the one fixed by the task specification, whose
formulation Worker 360 supplied; Worker 1222 checked the source and prepared this pair.

`Langlands.AlgebraicGeometry.Modules.HigherDirectImageQuasicoherentStatement.{u}` is a
`Prop`-valued definition. It states that, for every quasi-compact separated morphism of schemes
`f : X ⟶ Y`, every quasi-coherent `𝒪_X`-module `M` and every degree `n : ℕ`, the higher direct
image `Rⁿ f_* M` is a quasi-coherent `𝒪_Y`-module. This module only states the proposition; it
contains no proof. A separate exact-target proof is still required.

## Exact interface

The only external parameter is the universe `u`. Every scheme, module and index type in the
statement lives in this one universe. The proposition quantifies over the following data, in
this order.

- Schemes `X Y : Scheme.{u}` and a morphism of schemes `f : X ⟶ Y`.
- A hypothesis `QuasiCompact f`. This is Mathlib's class
  `AlgebraicGeometry.QuasiCompact`: the preimage under `f` of every compact open subset of `Y`
  is compact.
- A hypothesis `IsSeparated f`. This is Mathlib's class `AlgebraicGeometry.IsSeparated`: the
  diagonal `pullback.diagonal f : X ⟶ X ×_Y X` is a closed immersion. Mathlib derives
  `QuasiSeparated f` from it by an instance.
- A sheaf of modules `M : X.Modules` over the structure sheaf of `X`, that is, an object of
  Mathlib's category `SheafOfModules X.ringCatSheaf`.
- A hypothesis `M.IsQuasicoherent`. This is Mathlib's class `SheafOfModules.IsQuasicoherent`.
  It holds when there are a family of opens of `X` covering `X` and, for each member `U`, a
  presentation of the restriction `M.over U`: an epimorphism from a free module
  `⨁_{i ∈ I} 𝒪_U ⟶ M|_U` together with a family of generating sections of its kernel. So
  `M|_U` is the cokernel of a morphism `⨁_{j ∈ J} 𝒪_U ⟶ ⨁_{i ∈ I} 𝒪_U`. The index types `I`
  and `J` lie in `Type u`.
- A degree `n : ℕ`. Every degree is included, also `n = 0`.

The conclusion is `((DerivedSections.higherDirectImage f n).obj M).IsQuasicoherent`, with the
same Mathlib predicate, now on `Y.Modules` and again with index types in `Type u`. Here
`DerivedSections.higherDirectImage f n` is the Library's higher direct image `Rⁿ f_*` of actual
`𝒪_X`-modules, from module `Langlands.AlgebraicGeometry.Modules.DerivedSections`. It is
Mathlib's right-derived functor `(Scheme.Modules.pushforward f).rightDerived n : X.Modules ⥤
Y.Modules`, computed from chosen injective resolutions in `X.Modules`. The Library's
`DerivedSections.higherDirectImageZeroIso` identifies degree `0` with the pushforward
`Scheme.Modules.pushforward f`.

The statement assumes no data: it contains no resolution, no Čech complex, no open cover and no
comparison map. It places no condition on `Y`.

## Original source

The Stacks Project Authors, *The Stacks Project*, Cohomology of Schemes, Lemma 30.4.5, tag
01XJ, label `lemma-quasi-coherence-higher-direct-images`, part (1). The source is file
`coherent.tex` (SHA-256 `702ca51850d0f9a615888dc0ced8100e104c98961e05a48b32c3ddf6eda61604`) at
Stacks commit `a04446e57ec1fbc252a871afcec7752fb2807b14`, in the registered folder
`stacks-flasque-affine-vanishing-kunneth-a04446e5` (folder SHA-256
`af02e6f0aff875e216f1e0fde58f6baad3eedeb6b82799a8d6c91ff68cccaa3a`). The folder's `tags.txt`
maps 01XJ to `coherent-lemma-quasi-coherence-higher-direct-images`. The lemma is at lines
741-758 of `coherent.tex`, in Section 30.4 (tag 01XH, line 545); the proof of part (1) is at
lines 760-802. Part (1) reads:

> Let f : X → S be a morphism of schemes. Assume that f is quasi-separated and quasi-compact.
> (1) For any quasi-coherent O_X-module F the higher direct images R^p f_* F are
> quasi-coherent on S.

The definitions used by the source match the Lean objects as follows.

- The source's `S`, `F` and `p ≥ 0` are Lean's `Y`, `M` and `n : ℕ`.
- Higher direct images of modules: Cohomology of Sheaves, Section 20.2 (tag 01DZ),
  `cohomology.tex` in the same folder, lines 76-86, equation
  `equation-higher-direct-image-modules`. For a morphism of ringed spaces, `R^i f_* F` is
  `H^i(f_* I^•)` for an injective resolution `F[0] → I^•` in `Mod(O_X)`. The Lean functor is
  the same construction: Mathlib's `rightDerived` of `Scheme.Modules.pushforward f` uses
  injective resolutions in `X.Modules`, the category of sheaves of `𝒪_X`-modules.
- Quasi-coherent modules: Sheaves of Modules, Definition `definition-quasi-coherent` (tag
  01BE), `modules.tex`, label at line 1021, in the registered folder
  `stacks-closed-immersion-exactness-a04446e5` (folder SHA-256
  `a35bfda718ee774de875160239072d121d9d0acd5c43fbc792f2b03a77f64691`). A sheaf of
  `𝒪_X`-modules is quasi-coherent if every point has an open neighbourhood `U` on which it is
  the cokernel of a map `⨁_{j ∈ J} 𝒪_U → ⨁_{i ∈ I} 𝒪_U`. Mathlib asks for the same local
  presentations on the members of an open cover, and a cover by such neighbourhoods exists if
  and only if every point has one. Stacks allows arbitrary index sets. The Lean index types lie
  in `Type u`, which loses nothing: a sheaf of modules on a `u`-small scheme can be presented
  using `u`-small index sets, for instance its sections over the members of the cover and the
  relations among them.
- Quasi-compact morphisms: the inverse image of every quasi-compact open is quasi-compact. This
  is Mathlib's `QuasiCompact`.
- Separated morphisms: the diagonal is a closed immersion. This is Mathlib's `IsSeparated`.

The Lean statement is therefore part (1) of 01XJ with one extra hypothesis, as explained next.
It claims nothing beyond part (1).

## The separatedness restriction

The source assumes `f` quasi-compact and quasi-separated. The Lean statement assumes `f`
quasi-compact and separated. Every separated morphism is quasi-separated, so the Lean
proposition is a special case of the source: the source implies it, and it is strictly narrower
whenever some quasi-compact, quasi-separated, non-separated morphism occurs.

The task specification fixes this restriction, for two reasons given there and in the consumer.

- The consumer is the Library statement
  `Langlands.AlgebraicGeometry.Modules.FlatHigherDirectImageBaseChangeStatement`, flat base
  change for higher direct images, which also assumes `QuasiCompact f` and `IsSeparated f`. Its
  proof needs this quasi-coherence only for such morphisms.
- The Library's Čech tools are proved for separated morphisms. Over an affine base, a
  separated `X` has affine pairwise intersections of affine opens, so a finite affine cover
  computes `Rⁿ f_*` by a Čech complex of quasi-coherent modules (compare Lemma 30.7.1, label
  `lemma-separated-case-relative-cech`, tag 01XL, `coherent.tex` line 1200).

## Parts not stated

Parts (2) and (3) of 01XJ are not stated. Part (2) asserts, for quasi-compact `S`, a single
bound `n(X, S, f)` beyond which `R^p f_* F` vanishes for every quasi-coherent `F`; part (3)
asserts such a bound uniformly over all base changes `S' → S`. The Lean proposition contains no
vanishing assertion of any kind.

## Errata

The tag page https://stacks.math.columbia.edu/tag/01XJ was read on 2026-11-02; it is not a
registered source. It has five comments. Comment 7145 notes an alternative proof of part (1)
through Čech-to-sheaf cohomology (tag 0A3Z); comment 7192 reports a typo in the proof of part
(3); comment 7725 proposes proving part (1) with the induction principle (Lemma 30.4.1, tag
08DR), and the maintainers made that change in January 2023. The proof at commit `a04446e5`
already uses the induction principle. No comment changes the statement of part (1) or its
hypotheses.

## Intended use

Worker 360 published this statement task as a missing prerequisite for the exact proof of flat
higher-direct-image base change, task `5b778a75-e74b-4ae4-9232-6735e3eefa47`, revision 1.
That proof needs to identify the actual higher direct image over an affine base with the
quasi-coherent sheaf associated to cohomology (compare Lemma 30.4.6, tag 01XK, `coherent.tex`
line 844). A separate exact-target proof task will prove this proposition; it must not use
flat base change, which depends on it.

## Proof pointers

These are pointers for the future proof, not a claim that a proof is available. The Stacks
proof of part (1) reduces to an affine base, because higher direct images commute with
restriction to opens (Cohomology, Lemma `lemma-localize-higher-direct-images`, tag 01E5) and
quasi-coherence is local. Over an affine base it uses the induction principle (tag 08DR,
`coherent.tex` line 557): affine opens have vanishing higher direct images (tag 01XC) and
quasi-coherent pushforward (tag 01LC), and the relative Mayer-Vietoris sequence (tag 01EC)
passes the property to unions. The Library supplies `higherDirectImageRestrictIso` (module
`Langlands.AlgebraicGeometry.Modules.HigherDirectImageOpenRestriction`), the Čech comparison
modules under `Langlands.AlgebraicGeometry.Modules.CechResolution`, and positive-degree
vanishing along affine morphisms
(`Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentHigherDirectImageVanishingProof`).

## Imports

The module imports Mathlib's `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` and
`Mathlib.AlgebraicGeometry.Morphisms.Separated`, and the Library's
`Langlands.AlgebraicGeometry.Modules.DerivedSections`. It imports no flat base change statement
or proof.
