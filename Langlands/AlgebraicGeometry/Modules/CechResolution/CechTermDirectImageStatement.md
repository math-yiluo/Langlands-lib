# Direct images of sheafified Čech terms over an affine base

Authors: Worker 1159 and Worker 1098.

Module:
`Langlands.AlgebraicGeometry.Modules.CechResolution.CechTermDirectImageStatement`.
Declaration:
`Langlands.AlgebraicGeometry.Modules.CechResolution.CechTermDirectImageStatement`.

This module defines a proposition at arbitrary universe `u`. It states that for
every scheme `X : Scheme.{u}`, commutative ring object `R : CommRingCat.{u}`,
separated morphism `π : X ⟶ Spec R`, ordered affine cover `𝒰` of `X`,
quasi-coherent `𝒪_X`-module `M`, and Čech degree `q : ℕ`,

1. `π_* (cechTerm 𝒰 M q)` is a quasi-coherent `𝒪_(Spec R)`-module;
2. `R^(n + 1) π_* (cechTerm 𝒰 M q)` is a zero object for every `n : ℕ`.

All objects and hypotheses are quantified inside the `Prop`-valued definition;
there are no outer parameters or hypotheses. No Noetherian, finite type,
flatness, or finite generation hypothesis is imposed. The ordered affine cover
is finite by its definition, so its existence implies that `X` is
quasi-compact: it is a finite union of affine, hence quasi-compact, opens.
The assumption `IsSeparated π` concerns the morphism to `Spec R`; since the
affine base is separated, `X` is also separated.

The Čech degree `q` is independent of the derived degree. The first conjunct
concerns the ordinary direct image, or derived degree zero, for every Čech
degree. The second conjunct ranges over exactly the positive derived degrees
using `n + 1`. This module defines the statement and supplies no proof of it.

## Objects used in Lean

The imported Library interfaces are used unchanged:

- `Scheme.OrderedAffineCover` has a finite linearly ordered index type `𝒰.ι`,
  affine opens `𝒰.U i`, and the covering condition `⨆ i, 𝒰.U i = ⊤`.
- In `CechResolution.Complex`, `cechTerm 𝒰 M q` is the finite biproduct
  `⨁ fun s : 𝒰.Idx q => sheafOn M (𝒰.inter s)`. Here
  `𝒰.Idx q = {s : Fin (q + 1) → 𝒰.ι // StrictMono s}` and
  `𝒰.inter s = ⨅ j, 𝒰.U (s.1 j)`. Thus the Library's alternating complex
  uses strictly increasing tuples.
- In `CechResolution.Basic`, `sheafOn M W` is
  `(Scheme.Modules.pushforward W.ι).obj
    ((Scheme.Modules.restrictFunctor W.ι).obj M)`,
  the pushforward of the restriction of `M` along the open immersion
  `W.ι : W ⟶ X`.
- `Scheme.Modules.pushforward π` is Mathlib's functor on sheaves of modules.
  `M.IsQuasicoherent` and `IsSeparated π` are Mathlib's actual predicates.
- In `DerivedSections`,
  `higherDirectImage π k := (Scheme.Modules.pushforward π).rightDerived k`.
  Its values are sheaves of modules on `Spec R`, and `IsZero` is the
  categorical zero-object predicate. The degree-zero comparison
  `DerivedSections.higherDirectImageZeroIso π` identifies this right-derived
  functor in degree zero with ordinary pushforward.

## Provenance and scope

The source is The Stacks Project Authors, *Cohomology of Schemes*, at commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`, registered as
`stacks-flasque-affine-vanishing-kunneth-a04446e5`:

- [Lemma 30.7.1, tag 01XL](https://stacks.math.columbia.edu/tag/01XL),
  `coherent.tex`, Lemma `lemma-separated-case-relative-cech`,
  lines 1199–1268, especially the quasi-coherence assertion in
  lines 1225–1244 and termwise acyclicity argument in lines 1245–1261;
- [Lemma 30.2.3, tag 01XC](https://stacks.math.columbia.edu/tag/01XC),
  `coherent.tex`, Lemma `lemma-relative-affine-vanishing`,
  lines 180–200, asserting positive higher-direct-image vanishing for
  quasi-coherent modules along affine morphisms.

The retained `coherent.tex` has SHA-256
`702ca51850d0f9a615888dc0ced8100e104c98961e05a48b32c3ddf6eda61604`;
`tags.txt` lines 2513 and 2522 identify tags 01XC and 01XL respectively.

This is a derived formulation of the two termwise facts in the proof of
01XL, specialized to an affine base and separated `X`. That proof uses
affineness of the intersection inclusions and their composites with the base
morphism, together with 01XC and the relative Leray argument, to obtain
acyclicity of the summands; the terms are finite sums. The Lean proposition
packages those two facts for the published strictly increasing tuple terms.
It is not a verbatim source statement: 01XL writes the Čech construction
using all index tuples, whereas this Library uses the ordered version.
The same termwise facts apply to its selected tuples and finite biproducts.

The identification of the Čech complex with `Rπ_* M`, its augmentation,
and any base-change comparison are outside this statement. In particular,
the existing vanishing theorem for `DerivedSections.relativeCohomology`
of Čech terms concerns ring-valued relative global sections and is different
from the sheaf-valued higher-direct-image assertion here.

Worker 1098 supplied the formulation reproduced in the task. Worker 1159
checked the Library interfaces and original source locations and prepared
this statement and documentation.
