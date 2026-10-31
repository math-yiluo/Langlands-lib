# Higher cohomology of quasi-coherent modules on affine schemes vanishes

Author: Worker 958.

`Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentCohomologyVanishingStatement.{u}` is a
`Prop`-valued definition. This module only states the vanishing; it contains no proof. A
separate exact-target proof of this proposition is still required.

## Exact interface

The only external parameter is the universe `u`. The proposition quantifies over the
following data, in this order.

- A scheme `X : Scheme.{u}` with `IsAffine X`. This is Mathlib's class
  `AlgebraicGeometry.IsAffine`: the canonical morphism `X ⟶ Spec Γ(X, ⊤)` is an isomorphism.
  No finiteness, noetherianity or other condition is placed on `X`.
- A sheaf of modules `M : X.Modules` over the structure sheaf of `X`, that is, an object of
  Mathlib's category `SheafOfModules X.ringCatSheaf`, with `M.IsQuasicoherent`. This is
  Mathlib's class `SheafOfModules.IsQuasicoherent`: there are a family of opens covering `X`
  and, on each member `U`, a presentation of `M|_U` as the cokernel of a morphism
  `⨁_{j ∈ J} 𝒪_U ⟶ ⨁_{i ∈ I} 𝒪_U` of free modules, with index types in `Type u`.
- A degree `n : ℕ`. The statement concerns degree `n + 1 ≥ 1`.

The conclusion is a conjunction of two parts.

1. `IsZero ((DerivedSections.cohomology X (n + 1)).obj M)`. Here
   `DerivedSections.cohomology X m` is the Library's sheaf cohomology `Hᵐ(X, -)` of actual
   `𝒪_X`-modules (module `Langlands.AlgebraicGeometry.Modules.DerivedSections`): Mathlib's
   right-derived functor `(DerivedSections.globalSections X).rightDerived m` of the global
   sections functor `X.Modules ⥤ ModuleCat Γ(X, ⊤)`, computed from chosen injective
   resolutions in `X.Modules`. So `Hⁿ⁺¹(X, M)` is the zero `Γ(X, ⊤)`-module.
2. For every `R : CommRingCat.{u}` and every morphism of schemes `g : X ⟶ Spec R`,
   `IsZero ((DerivedSections.relativeCohomology g (n + 1)).obj M)`. Here
   `DerivedSections.relativeCohomology g m` is the right-derived functor of the Library's
   `DerivedSections.relativeGlobalSections g = Scheme.Modules.pushforward g ⋙ moduleSpecΓFunctor`,
   the global sections of `M` as an `R`-module. So `Hⁿ⁺¹(X, M)` is also the zero `R`-module.

The statement assumes no data: it contains no resolution, no Čech complex and no cover.

## Intended use

Part 2 says that `relativeGlobalSections g` has vanishing higher right-derived functors on
quasi-coherent modules of an affine scheme. It is the acyclicity input for the comparison of
the alternating Čech complex of a finite affine open cover of a separated scheme `Y ⟶ Spec R`
with the actual derived sections `DerivedPlus.derivedComplex (relativeGlobalSections _)`
(Stacks Lemma 01XD), which the executor needs for the proof of
`Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsStatement` (task
`5056e5fc-5861-489e-adae-be84a23164c5`). There each finite intersection `U_s` of cover members
is affine, and the Čech terms are pushforwards of quasi-coherent modules on `U_s`.

## Original source

The sources are from the Stacks Project at git commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`, in two registered folders.

- `stacks-flasque-affine-vanishing-kunneth-a04446e5` (folder SHA-256
  `af02e6f0aff875e216f1e0fde58f6baad3eedeb6b82799a8d6c91ff68cccaa3a`) holds `coherent.tex`.
- `stacks-affine-morphisms-relative-vanishing-a04446e5` (folder SHA-256
  `52a274f2aafc218e99eb2433780f5a9df33a34acd513b47a714044e2e2903d91`) holds the tag page
  `tag-01XB.html` with its comment thread.

The cited result is Cohomology of Schemes, Lemma 30.2.2,
`lemma-quasi-coherent-affine-cohomology-zero` (tag 01XB, `coherent.tex`, label at line 146,
statement lines 145–155, proof lines 157–174): "Let X be a scheme. Let F be a quasi-coherent
O_X-module. For any affine open U ⊂ X we have H^p(U, F) = 0 for all p > 0."

Part 1 is this lemma for the affine open `U = X` of an affine scheme `X`, with `p = n + 1`.
The Library has no cohomology functor of the restriction of a module to an open subscheme,
so the Lean proposition takes the whole affine scheme; the case of an affine open `U` of an
arbitrary scheme is the same statement for the scheme `U` and the restriction `F|_U`, which
is quasi-coherent. Part 2 is the same vanishing read as `R`-modules: the Library's
`DerivedSections.relativeCohomologyRestrictScalarsIso g m` identifies
`relativeCohomology g m` with `cohomology X m` followed by restriction of scalars along the
ring map `R ⟶ Γ(X, ⊤)` induced by `g`, so it is not an additional mathematical claim; it is
stated because the derived `R`-module sections are what the intended use consumes.

The Stacks proof checks the conditions of Cohomology, Lemma 20.11.9
(`cohomology-lemma-cech-vanish-basis`) for the basis of affine opens with the standard open
coverings, using Lemma 30.2.1 (`lemma-cech-cohomology-quasi-coherent-trivial`, label at
line 45): Čech cohomology of a quasi-coherent module for a standard open covering of an
affine scheme vanishes in positive degrees. The Library already contains the Lean form of
Lemma 30.2.1 as `AffineVanishing.exactAt_cover` (module
`Langlands.AlgebraicGeometry.Modules.AffineVanishing.QuasicoherentCech`).

Errata: the tag page of 01XB, fetched 2026-10-29, has one comment (#3020, a suggested
slogan), which does not change the statement. No project errata file exists for this source.
