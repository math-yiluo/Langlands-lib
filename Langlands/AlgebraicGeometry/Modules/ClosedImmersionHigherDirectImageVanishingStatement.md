# Higher direct images along a closed immersion vanish

Author: Worker 727.

`Langlands.AlgebraicGeometry.Modules.ClosedImmersionHigherDirectImageVanishingStatement.{u}`
is a `Prop`-valued definition. This module only states the vanishing; it contains no
proof. A separate exact-target proof of this proposition is still required.

## Exact interface

The only external parameter is the universe `u`. The proposition quantifies over the
following data, in this order.

- Schemes `X Y : Scheme.{u}` and a morphism of schemes `i : X ⟶ Y` with
  `IsClosedImmersion i`. This is Mathlib's class
  `AlgebraicGeometry.IsClosedImmersion`: the underlying continuous map is a closed
  embedding, and `i^# : 𝒪_Y ⟶ i_* 𝒪_X` is surjective on stalks. No other hypothesis is
  placed on `X`, `Y` or `i`: no quasi-compactness, quasi-separatedness or
  noetherianity, and no condition on the base.
- An arbitrary sheaf of modules `M : X.Modules` over the structure sheaf of `X`, that is,
  an object of Mathlib's category `SheafOfModules X.ringCatSheaf`. `M` need not be
  quasi-coherent.
- A degree `q : ℕ`. The statement concerns degree `q + 1 ≥ 1`.

The conclusion is
`IsZero ((DerivedSections.higherDirectImage i (q + 1)).obj M)`.
Here `DerivedSections.higherDirectImage i m` is the Library's higher direct image
`Rᵐ i_*` of actual `𝒪_X`-modules (module
`Langlands.AlgebraicGeometry.Modules.DerivedSections`). It is Mathlib's right-derived
functor `(Scheme.Modules.pushforward i).rightDerived m : X.Modules ⥤ Y.Modules`, computed
from chosen injective resolutions in `X.Modules`. `Scheme.Modules.pushforward i` is
Mathlib's pushforward of sheaves of modules. Its sections over an open `V ⊆ Y` are the
sections of `M` over `i ⁻¹ᵁ V`, viewed as a `Γ(Y, V)`-module through `i^#`.

So `R^{q+1} i_* M` is the zero object of `Y.Modules` for every `q`. Nothing is assumed
as data: the statement contains no resolution, no exactness hypothesis and no
comparison map.

## Intended use

The Library's `DerivedSections.pushforwardComparison h g M hM n` (module
`Langlands.AlgebraicGeometry.Modules.PushforwardComparison`) needs the hypothesis
`hM : ∀ q : ℕ, IsZero ((higherDirectImage h (q + 1)).obj M)`. For a closed immersion `h`
this proposition supplies `hM` for every module `M`. Together with
`isIso_pushforwardComparison` and the Library's
`PushforwardInjectiveAcyclicStatement`, it identifies `Hⁿ(Y, i_* M)` with `Hⁿ(X, M)`
along a closed immersion. This is Stacks tag 02UV for scheme modules. The proof of Stacks
tag 0BF3 (relative theorem of the cube, task `eab37f2b-d9cf-40e4-86ad-492608a9c630`)
uses this identification for the section axes, which are closed immersions.

## Original source

The Stacks Project at git commit `a04446e57ec1fbc252a871afcec7752fb2807b14`. Two
registered sources hold it:

- `stacks-closed-immersion-exactness-a04446e5`, the folder "Stacks Project - Exactness
  of closed-immersion pushforward and vanishing of its higher direct images (source at
  a04446e5)" (folder SHA-256
  `a35bfda718ee774de875160239072d121d9d0acd5c43fbc792f2b03a77f64691`). It holds
  `modules.tex` and `derived.tex`.
- `stacks-flasque-affine-vanishing-kunneth-a04446e5` (folder SHA-256
  `af02e6f0aff875e216f1e0fde58f6baad3eedeb6b82799a8d6c91ff68cccaa3a`). It holds
  `cohomology.tex`.

The cited results are:

- Cohomology of Sheaves, Lemma `lemma-cohomology-and-closed-immersions` (tag 02UV,
  `cohomology.tex`, label at line 3447, proof lines 3453-3459). For a closed immersion of
  topological spaces `i : Z → X` and an abelian sheaf `F` on `Z`,
  `H^p(Z, F) = H^p(X, i_* F)`. The proof states: "`i_*` is exact (see Modules, Lemma
  01AX), and hence `R^p i_* = 0` as a functor (Derived Categories, Lemma 015F)". The
  vanishing `R^p i_* = 0` for `p > 0` in that proof is the content of the present
  proposition.
- Sheaves of Modules, Lemma `lemma-i-star-exact` (tag 01AX, `modules.tex`, label at line
  557). For the inclusion `i : Z → X` of a closed subset, `i_* : Ab(Z) → Ab(X)` is
  exact. The proof uses the stalk formula of Sheaves, Lemma 6.32.1 (tag 00AE):
  `(i_* F)_x = F_x` for `x ∈ Z`, and the stalk is trivial for `x ∉ Z`. It also uses
  Lemma `lemma-abelian` (tag 01AG, `modules.tex`, label at line 149): `Mod(𝒪_X)` is
  abelian, and a complex of `𝒪_X`-modules is exact if and only if it is exact on
  stalks.
- Derived Categories, Lemma `lemma-right-derived-exact-functor` (tag 015F, `derived.tex`,
  label at line 5884). For an exact functor `F` of abelian categories, `R^iF = 0` for
  `i ≠ 0`.

### Relation to the Lean statement

Stacks 01AX is stated for abelian sheaves. The Lean statement concerns modules. The
functor `Scheme.Modules.pushforward i` on modules is exact for the same reason. Lemma 01AG
detects exactness of a complex of `𝒪`-modules on stalks, that is, on the underlying
abelian sheaves. The underlying abelian sheaf of `i_* M` is the abelian pushforward of
the underlying abelian sheaf of `M`, which is exact by 01AX. Lemma 015F applied to the
exact functor `Scheme.Modules.pushforward i` between the abelian categories `X.Modules`
and `Y.Modules` then gives `R^{q+1} i_* = 0`. Mathlib's `rightDerived` is the
injective-resolution right-derived functor, matching the Stacks `R^iF` on the bounded
below derived category (015F, part (5)).

The Lean hypothesis `IsClosedImmersion i` is stronger than the topological hypothesis
the source uses. Only the closed-embedding part of it is needed for exactness. The
proposition therefore claims no more than the source supports.

Errata: on 2026-10-29 the tag pages of 00AE, 01AG, 01AX, 02UV and 01XC had no comments
of their own. Tag 015F had three: #4282 reports a typo in part (2) (D(A) for D^+(A)),
#4446 says it is fixed, and #4855 thanks. Tag 02UV links two comments on Section 20.20,
and tag 00AE links one comment on Section 6.32. No comment changes a statement used here.
No project errata file exists for these sources.
