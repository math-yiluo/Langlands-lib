# Pushforwards of injective scheme modules are acyclic for global sections

Author: Worker 727.

`Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicStatement.{u}`
is a `Prop`-valued definition. This module states the vanishing and supplies no
proof. A separate exact-target proof of this proposition is still required.

## Exact interface

The only external parameter is the universe `u`. Inside the proposition the
following data are quantified, in this order.

- Schemes `X Y : Scheme.{u}` and an arbitrary morphism of schemes `h : X ⟶ Y`.
  No hypothesis is placed on `X`, `Y` or `h`: no quasi-compactness,
  separatedness, finiteness, affineness or closed-immersion condition.
- A sheaf of modules `J : X.Modules` over the structure sheaf of `X`, that is an
  object of Mathlib's category `SheafOfModules X.ringCatSheaf`, with
  `Injective J`. This is Mathlib's categorical injectivity in `X.Modules`:
  every morphism into `J` extends along every monomorphism of `X.Modules`.
- A degree `n : ℕ`; the statement concerns the degree `n + 1 ≥ 1`.

Write `h_* J = (Scheme.Modules.pushforward h).obj J : Y.Modules` for Mathlib's
pushforward of sheaves of modules, whose sections over an open `V ⊆ Y` are the
sections of `J` over `h ⁻¹ᵁ V`.

The conclusion is the conjunction of two vanishing statements.

1. `IsZero ((DerivedSections.cohomology Y (n + 1)).obj (h_* J))`. Here
   `DerivedSections.cohomology Y m` is the Library's sheaf cohomology
   `Hᵐ(Y, -)` of actual `𝒪_Y`-modules: Mathlib's right-derived functor
   `(globalSections Y).rightDerived m` of the global-sections functor
   `Y.Modules ⥤ ModuleCat Γ(Y, ⊤)`, computed from chosen injective resolutions
   in `Y.Modules` (module `Langlands.AlgebraicGeometry.Modules.DerivedSections`).
2. For every `R : CommRingCat.{u}` and every morphism `g : Y ⟶ Spec R`,
   `IsZero ((DerivedSections.relativeCohomology g (n + 1)).obj (h_* J))`. Here
   `relativeCohomology g m` is the right-derived functor of the `R`-module
   global sections `Scheme.Modules.pushforward g ⋙ moduleSpecΓFunctor`.

So `h_* J` has no cohomology on `Y` in any positive degree, whether cohomology
is taken as `Γ(Y, ⊤)`-modules or as `R`-modules over an affine base. The second
part is a consequence of the first: the Library's
`DerivedSections.relativeCohomologyRestrictScalarsIso g m` identifies
`relativeCohomology g m` with `cohomology Y m` followed by restriction of
scalars along `structureRingHom g`, which sends zero modules to zero modules. It
is stated separately because the intended consumers work with the `R`-module
version over an affine base.

Nothing is assumed as data: no resolution, no flasqueness predicate and no
comparison map appears in the statement.

## Intended use

Together with exactness of the pushforward along a closed immersion and the
Library's acyclic-resolution comparison
(`Langlands.Cohomology.AcyclicResolution`), this vanishing identifies
`Hⁿ(Y, i_* M)` with `Hⁿ(X, M)` for a closed immersion `i : X ⟶ Y`. In the
proof of Stacks tag 0BF3 (relative theorem of the cube, task
`eab37f2b-d9cf-40e4-86ad-492608a9c630`) this identifies the cohomology of the
pushforward along a section axis with the cohomology of the axis itself.

## Original source

The Stacks Project, Cohomology of Sheaves, Section "Flasque sheaves" (tag 09SV),
in the retained file `cohomology.tex`, lines 1880-2000. Registered source
`stacks-flasque-affine-vanishing-kunneth-a04446e5` (git commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`, folder SHA-256
`af02e6f0aff875e216f1e0fde58f6baad3eedeb6b82799a8d6c91ff68cccaa3a`).

- Definition `definition-flasque` (lines 1887-1893): a sheaf is flasque if every
  restriction map `F(V) → F(U)` for opens `U ⊆ V` is surjective.
- Lemma `lemma-injective-flasque` (tag 09SX, Lemma 20.12.2, lines 1902-1906, proof 1908-1910):
  on a ringed space, any injective `𝒪_X`-module is flasque. Its proof refers to
  Lemma `lemma-injective-restriction-surjective` (tag 01EA, lines 714-725).
- Lemma `lemma-flasque-acyclic` (tag 09SY, Lemma 20.12.3, lines 1912-1917, proof
  1919-1958): on a ringed space, any flasque `𝒪_X`-module is acyclic for
  `RΓ(X, -)`.
- The pushforward of a flasque sheaf is flasque, because the restriction maps of
  `h_* F` are restriction maps of `F` between the opens `h ⁻¹ V`. The source
  uses this fact without a separate lemma, in the proof of Lemma
  `lemma-godement-resolution` (tag 0FKS), lines 7049-7050.

The proposition is the composite of these facts for the morphism of ringed
spaces underlying `h`: `J` is flasque by 09SX, hence `h_* J` is flasque, hence
`H^{n+1}(Y, h_* J) = 0` by 09SY. Stacks works with all `𝒪_X`-modules on a
ringed space; Mathlib's `X.Modules` is exactly the category of sheaves of
modules over the structure sheaf of the scheme `X`, and the Library's
`cohomology` is the derived functor of global sections on that category,
computed from injective resolutions in `X.Modules`, exactly as Stacks defines
`H^i(X, F)` for `𝒪_X`-modules in Section 20.2 ("Cohomology of sheaves",
equation `equation-cohomology-modules`, `cohomology.tex` lines 62-74), as
`Γ(X, ⊤)`-modules. So the Lean statement is the source statement specialised to
the ringed spaces underlying schemes.

Errata: on 2026-10-29 the tag 09SY page had one comment (#772, typos in the
proof) and the Section 09SV page eight comments (typos in the proof of 09SY and
a missing reference to the morphism in 09T0, all answered "fixed"); the pages of
09SX and 09T0 had no comments. No comment changes a statement. No project
errata file exists for this source.
