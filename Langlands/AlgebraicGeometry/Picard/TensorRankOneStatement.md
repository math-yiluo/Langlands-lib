# Local rank one of actual tensor powers of line bundles

`TensorPowLocallyFreeRankOneStatement` is a precise proposition. It is not
assumed, installed as an axiom, or used as a premise by any imported
construction. A separate module proves it:
`Langlands.AlgebraicGeometry.Picard.tensorPow_isLocallyFreeRankOne :
TensorPowLocallyFreeRankOneStatement.{u}` in
`Langlands.AlgebraicGeometry.Picard.TensorRankOneProof`, by induction on `n`
from `IsLocallyFreeRankOne.tensor` and the published theorem
`Langlands.Scheme.Modules.pullbackTensorComparisonIsIso`.

## Statement

For every scheme `X : Scheme.{u}`, every `L : LineBundle X` and every
natural number `n`, the module sheaf `tensorPow L.obj n` satisfies
`IsLocallyFreeRankOne`. The scheme, the line bundle and the exponent are
all quantified inside the proposition. The universe `u` is arbitrary, and no
affine, noetherian, quasi-compact, separated or quasi-coherence hypothesis is
imposed on `X`.

The ingredients are the published ones:

- `IsLocallyFreeRankOne M` (from `Langlands.AlgebraicGeometry.Picard.LineBundle`)
  says that every point `x` has an open neighborhood `U` with an isomorphism
  `M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf`, that is, a
  trivialization of `M` on `U`. `LineBundle X` is the full subcategory of
  `X.Modules` cut out by this property, and `L.obj` is the underlying sheaf.
- `tensorPow M n` (from `Langlands.AlgebraicGeometry.Modules.Tensor`) is defined
  by recursion: `tensorPow M 0 = structureSheaf X`, which is
  `SheafOfModules.unit X.ringCatSheaf`, and
  `tensorPow M (n + 1) = tensorObj M (tensorPow M n)`. Here `tensorObj` is the
  actual sheaf tensor product, the sheafification of the sectionwise presheaf
  tensor product of modules. No abstract `MonoidalCategory` instance is used.

So for `n = 0` the statement says that the structure sheaf is locally free
of rank one. For `n ≥ 1` it is about the right-associated product
`L ⊗ (L ⊗ (⋯ ⊗ (L ⊗ 𝒪_X)))` with `n` copies of `L` and one trailing factor
`𝒪_X`. For example, `tensorPow L.obj 1` is `tensorObj L.obj (structureSheaf X)`,
a sheafified tensor product, rather than `L.obj` itself.

## Correspondence with the sources

The source is the Stacks Project, registered as
`stacks-local-freeness-invertibility-sections-2026-10-21`, content SHA-256
`6d1641a9deb284be889ee6e2630a2be6e57cc5985c80af2c9da7d17543ed0785`.
Section 17.25 (tag 01CR) is in file `01CR.html`, and Section 17.14 (tag 01C5) is
in file `01C5.html`.

- Definition 17.14.1 (tag 01C6) defines locally free modules of finite rank by
  local trivializations. The published `IsLocallyFreeRankOne` is its rank-one
  case for the module sheaves of a scheme.
- Definition 17.25.6 (tag 01CU) defines `𝓛^{⊗n}` for an invertible `𝓛` as the
  image of `𝒪_X` under applying `𝓕 ↦ 𝓕 ⊗ 𝓛` exactly `n` times. Explicitly
  `𝓛^{⊗0} = 𝒪_X` and, for `n > 0`, `𝓛^{⊗n} = 𝓛 ⊗ ⋯ ⊗ 𝓛`. The Lean `tensorPow`
  covers only `n ≥ 0`. It tensors on the left instead of the right and keeps the
  unit factor `𝒪_X` instead of discarding it. Both versions are built by
  repeatedly tensoring `𝒪_X` with `𝓛`, so they are isomorphic through the
  unitors, associators and symmetry of the tensor product (Stacks Section 17.16).
  `IsLocallyFreeRankOne.of_iso` shows that the property in this statement does
  not change under isomorphism, so these differences in bracketing do not affect
  what the statement means. The Lean statement also does not require `L` to be
  invertible in the sense of Definition 17.25.1. Its hypothesis is local rank
  one, which is what `LineBundle` records.
- In Stacks, the matching fact goes through invertibility: by Lemma 17.25.4
  (tag 0B8M), a locally free module of rank one is invertible. By Lemma 17.25.5
  (tag 01CT), part (1), a tensor product of invertible modules is invertible.
  Then the converse in Lemma 17.25.4, which holds when all stalks `𝒪_{X,x}` are
  local rings (true for schemes), returns local freeness of rank one. Induction
  on `n` then gives local rank one of every `𝓛^{⊗n}`, `n ≥ 0`.

The Lean target is the direct local form of this consequence. It states local
rank one of the actual iterated sheaf tensor product and does not mention
invertibility. It does not formalize or depend on the comparison between
invertibility and local rank one, which is a separate result. The formulation is a
derived scheme specialization of the Stacks statements, written for the
published constructions.

## Scope and relation to other results

Only the tensor-power form is stated. The optional binary form, local rank one
of `tensorObj M N` for locally free rank-one `M` and `N`, is not stated here.
A version of that binary closure that depends on an extra premise is already
published as `IsLocallyFreeRankOne.tensor` in
`Langlands.AlgebraicGeometry.Picard.LineBundleTensor`. It takes the explicit premise
`Langlands.Scheme.Modules.pullbackTensorComparisonIsIsoStatement`, which the
published theorem `Langlands.Scheme.Modules.pullbackTensorComparisonIsIso`
proves. This module does not import either and does not depend on that
premise.

The downstream ampleness interface `Langlands.AlgebraicGeometry.Picard.Ample`
takes the hypothesis `∀ n : ℕ, IsLocallyFreeRankOne (tensorPow L.obj n)` in
`LineBundle.isAmple_iff_nonvanishingLocus`. For a proof `h` of this statement,
the hypothesis is exactly `h X L`.

The statement says nothing about negative tensor powers, tensor inverses,
Picard groups, or a monoidal structure on `LineBundle X`.
