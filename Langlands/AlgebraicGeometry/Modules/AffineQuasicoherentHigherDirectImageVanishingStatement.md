# Higher direct images of quasi-coherent modules along an affine morphism vanish

Author: Worker 727.

`Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentHigherDirectImageVanishingStatement.{u}`
is a `Prop`-valued definition. This module only states the vanishing; it contains no proof. A
separate exact-target proof of this proposition is still required.

## Exact interface

The only external parameter is the universe `u`. The proposition quantifies over the
following data, in this order.

- Schemes `X S : Scheme.{u}` and a morphism of schemes `f : X ⟶ S` with `IsAffineHom f`.
  This is Mathlib's class `AlgebraicGeometry.IsAffineHom`: for every open `U ⊆ S` with
  `IsAffineOpen U`, the preimage `f ⁻¹ᵁ U` is an affine open of `X`. No other hypothesis is
  placed on `X`, `S` or `f`: no finiteness, noetherianity or separatedness condition on the
  schemes, and no condition on the base.
- A sheaf of modules `M : X.Modules` over the structure sheaf of `X`, that is, an object of
  Mathlib's category `SheafOfModules X.ringCatSheaf`, with `M.IsQuasicoherent`. This is
  Mathlib's class `SheafOfModules.IsQuasicoherent`. It holds when there are a family of opens
  of `X` covering `X` (a family covering the terminal object of the site of opens) and, for
  each member `U`, a presentation of the restriction `M.over U`. Such a presentation is a
  family of generating sections, that is an epimorphism from a free module
  `⨁_{i ∈ I} 𝒪_U ⟶ M|_U`, together with a family of generating sections of its kernel. So
  `M|_U` is the cokernel of a morphism `⨁_{j ∈ J} 𝒪_U ⟶ ⨁_{i ∈ I} 𝒪_U`. The index types
  `I` and `J` lie in `Type u`.
- A degree `q : ℕ`. The statement concerns degree `q + 1 ≥ 1`.

The conclusion is `IsZero ((DerivedSections.higherDirectImage f (q + 1)).obj M)`. Here
`DerivedSections.higherDirectImage f m` is the Library's higher direct image `Rᵐ f_*` of
actual `𝒪_X`-modules (module `Langlands.AlgebraicGeometry.Modules.DerivedSections`). It is
Mathlib's right-derived functor `(Scheme.Modules.pushforward f).rightDerived m :
X.Modules ⥤ S.Modules`, computed from chosen injective resolutions in `X.Modules`.

So `R^{q+1} f_* M` is the zero object of `S.Modules` for every `q`. The statement assumes no
data: it contains no resolution, no Čech complex and no comparison map.

## Intended use

The Library's `DerivedSections.pushforwardComparison h g M hM n` (module
`Langlands.AlgebraicGeometry.Modules.PushforwardComparison`) needs the hypothesis
`hM : ∀ q : ℕ, IsZero ((higherDirectImage h (q + 1)).obj M)`. For an affine morphism `h`
and a quasi-coherent `M`, this proposition supplies `hM`. Together with
`isIso_pushforwardComparison` and the Library's `PushforwardInjectiveAcyclicStatement`, it
identifies `Hⁿ(S, f_* M)` with `Hⁿ(X, M)`. This is Stacks Lemma
`lemma-relative-affine-cohomology` (tag 089W, `coherent.tex`, right after 01XC) for scheme
modules. The first executor of task `eab37f2b-d9cf-40e4-86ad-492608a9c630` (proof of the
relative theorem of the cube, Stacks tag 0BF3), Worker 606, requested this vanishing for the
base-change step of that proof.

## Original source

All sources are from the Stacks Project at git commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`. Three registered sources hold the files.

- `stacks-flasque-affine-vanishing-kunneth-a04446e5` (folder SHA-256
  `af02e6f0aff875e216f1e0fde58f6baad3eedeb6b82799a8d6c91ff68cccaa3a`) holds `coherent.tex` and
  `cohomology.tex`.
- `stacks-closed-immersion-exactness-a04446e5` (folder SHA-256
  `a35bfda718ee774de875160239072d121d9d0acd5c43fbc792f2b03a77f64691`) holds `modules.tex`.
- `stacks-affine-morphisms-relative-vanishing-a04446e5` (folder SHA-256
  `52a274f2aafc218e99eb2433780f5a9df33a34acd513b47a714044e2e2903d91`) holds `morphisms.tex`
  and the tag pages with their comment threads.

The cited results are:

- Cohomology of Schemes, Lemma `lemma-relative-affine-vanishing` (tag 01XC, `coherent.tex`,
  label at line 181, statement lines 180-185, proof lines 187-199): "Let f : X → S be a
  morphism of schemes. Let F be a quasi-coherent O_X-module. If f is affine then
  R^i f_* F = 0 for all i > 0." The Lean proposition is this statement with `i = q + 1`.
- Morphisms of Schemes, Definition `definition-affine` (Definition 29.11.1, tag 01S6,
  `morphisms.tex`, label at line 1714): "A morphism of schemes f : X → S is called affine if
  the inverse image of every affine open of S is an affine open of X." Mathlib's
  `IsAffineHom` is literally this condition.
- Sheaves of Modules, Definition `definition-quasi-coherent` (tag 01BE, `modules.tex`, label
  at line 1021). A sheaf of `𝒪_X`-modules `F` is quasi-coherent if every point has an open
  neighbourhood `U` such that `F|_U` is isomorphic to the cokernel of a map
  `⨁_{j ∈ J} 𝒪_U → ⨁_{i ∈ I} 𝒪_U`. Mathlib's `IsQuasicoherent` asks for the same local
  presentations on the members of an open cover. A cover by such neighbourhoods exists if and
  only if every point has one, so the two conditions agree. Stacks allows arbitrary index
  sets. The Lean index types lie in `Type u`, which loses nothing: a sheaf of modules on a
  `u`-small scheme can be presented using `u`-small index sets, for instance its sections over
  the members of the cover and the relations among them.

The Stacks proof of 01XC combines three facts. By Cohomology, Lemma
`lemma-describe-higher-direct-images` (tag 01E4, `cohomology.tex`, label at line 592),
`R^i f_* F` is the sheafification of `V ↦ H^i(f⁻¹ V, F)`. By the definition of an affine
morphism, `f⁻¹ V` is affine when `V` is affine. By Lemma
`lemma-quasi-coherent-affine-cohomology-zero` (tag 01XB, `coherent.tex`, label at line 146),
`H^i(f⁻¹ V, F) = 0` for `i > 0` on such opens. Affine opens form a basis of `S`. Neither 01E4
nor 01XB is in the Library at the time of writing. A proof of this proposition must supply
them or equivalent facts.

Errata: the tag pages were checked on 2026-10-29. Tags 01S6, 01BE and 01XC have no comments
of their own. Tag 01XB has one comment, a suggested slogan. Tag 01E4 has four comments about
a step in the proof that uses exactness of sheafification. Section 01S5 has five comments: a
typo in a different lemma, and a discussion of the notation in Lemma 01SD. Section 01BD has
two comments suggesting an additional lemma. No comment changes a definition or a statement
used here, and no project errata file exists for these sources.
