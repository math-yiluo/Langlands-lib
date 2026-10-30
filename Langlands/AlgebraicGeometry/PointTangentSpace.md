# Cotangent and tangent modules at a section of a scheme over a base

Author: Worker 207.

This module defines three objects for an arbitrary scheme over an arbitrary
base, with no hypotheses:

- `cotangentAtSection`, the relative cotangent sheaf pulled back along a
  section;
- `tangentAtSection`, its sheaf dual;
- `tangentSpaceAtPoint`, the module of global sections of that dual when the
  base is affine.

All three declarations are in the namespace `Langlands.Scheme`. They are
definitions only. No property of them is stated or proved here.

## Parameters and conventions

- `S : AlgebraicGeometry.Scheme.{u}` is an arbitrary scheme in an arbitrary
  universe `u`.
- `X : Over S` is an arbitrary scheme over `S`. Its structure morphism is
  `X.hom : X.left ⟶ S`.
- `e : Over.mk (𝟙 S) ⟶ X` is a morphism in the slice category `Over S`.
  Its domain `Over.mk (𝟙 S)` is the terminal object of `Over S`. Hence `e`
  is exactly a section of `X.hom`: its underlying scheme morphism is
  `e.left : S ⟶ X.left`, and the slice compatibility of `e` says
  `e.left ≫ X.hom = 𝟙 S`. The constructions use only `e.left`. The
  section equation is part of the argument type, but no definition here
  depends on it.
- For `tangentSpaceAtPoint`, `R : CommRingCat.{u}` is an arbitrary
  commutative ring and `X : Over (Scheme.Spec.obj (op R))`. Mathlib's
  `Scheme.Spec.obj (op R)` is by definition `Spec R`. In `e : Over.mk (𝟙 _) ⟶ X`
  the placeholder is this `Spec R`.

No smoothness, flatness, finiteness, separatedness, quasicoherence or field
hypothesis is imposed on `S`, `X`, `e` or `R`.

## The constructions

Write `Omega_(X/S)` for `Langlands.Scheme.relativeDifferentials X.hom`, the
published module sheaf of relative differentials on `X.left`. It is defined
in `Langlands.AlgebraicGeometry.RelativeDifferentials` as the sheafification
of the concrete presheaf of relative differentials.

1. `cotangentAtSection X e : S.Modules` is

   ```
   e* Omega_(X/S) = (Scheme.Modules.pullback e.left).obj Omega_(X/S).
   ```

   Here `AlgebraicGeometry.Scheme.Modules.pullback` is Mathlib's pullback
   functor of sheaves of modules along a scheme morphism, applied to the
   section `e.left : S ⟶ X.left`.

2. `tangentAtSection X e : S.Modules` is

   ```
   Hom_(O_S)(e* Omega_(X/S), O_S) = Langlands.Scheme.Modules.dual (cotangentAtSection X e).
   ```

   `Langlands.Scheme.Modules.dual M` is the published internal Hom sheaf from
   `M` to the actual structure module `Langlands.SchemeModule.structureModule S`,
   from `Langlands.AlgebraicGeometry.ModuleDual`. By the published
   `internalHomSectionsEquiv`, its sections over an open `U` correspond to
   module-sheaf morphisms between the restrictions to the open subscheme `U`.
   They are not merely linear maps between modules of sections over `U`.

3. `tangentSpaceAtPoint X e : ModuleCat R`, for `X` over `Spec R`, is

   ```
   Gamma(Spec R, tangentAtSection X e)
     = (AlgebraicGeometry.moduleSpecΓFunctor (R := R)).obj (tangentAtSection X e).
   ```

   Mathlib's `moduleSpecΓFunctor`, from `Mathlib.AlgebraicGeometry.Modules.Tilde`,
   takes sections over the top open of `Spec R`. It makes them an `R`-module
   by restricting scalars along the inverse of `Scheme.ΓSpecIso R`, i.e.
   along the canonical ring isomorphism `R ≅ Gamma(Spec R, O)`.

When `R` is a field `k`, `tangentSpaceAtPoint X e` is therefore the `k`-module
of global sections of the dual of `e* Omega_(X/S)`. It is this module itself,
not a module identified with a chosen tangent space. For an arbitrary ring `R`
it is the indicated `R`-module of global sections.

All objects are built from existing constructions: the published differential
sheaf, Mathlib's module pullback, the published internal dual and Mathlib's
global-section functor over `Spec R`. No cotangent or tangent object, rank,
basis or universal property is supplied as input. No new differential
construction is made.

## Internal provenance

This is an internal construction. It introduces no new mathematical source.
The formula is the published construction pattern of
`Langlands.GroupScheme.cotangentAtIdentity` and `Langlands.GroupScheme.Lie` in
`Langlands/AbelianScheme/Lie.lean`, generalized from the identity section of a
group scheme to an arbitrary section. That module defines

```
cotangentAtIdentity G = (Scheme.Modules.pullback G.identitySection).obj
                          (relativeDifferentials G.X.hom),
Lie G = Modules.dual (cotangentAtIdentity G).
```

`cotangentAtSection` and `tangentAtSection` keep these two steps unchanged.
They replace `G.identitySection` by the underlying morphism `e.left` of an
arbitrary section `e`, given as a slice morphism from the terminal object
`Over.mk (𝟙 S)`. The paired Markdown of `Lie.lean` records the literature
behind the group case: Conrad–Gabber–Prasad, *Pseudo-reductive Groups*,
Section 2.1, and Stacks Project Lemma 29.33.16. That lemma identifies the
conormal sheaf of a section with the pullback of relative differentials.
This module does not formalize or use that identification. The last step,
taking global sections over `Spec R` as an `R`-module, is Mathlib's existing
functor.

This module does not import `Lie.lean` and does not change it. It proves no
lemma comparing `cotangentAtSection` with `cotangentAtIdentity`.

Imports, all published or Mathlib modules used unchanged:

- `Langlands.AlgebraicGeometry.RelativeDifferentials` (`relativeDifferentials`);
- `Langlands.AlgebraicGeometry.ModuleDual` (`Langlands.Scheme.Modules.dual`);
- `Mathlib.AlgebraicGeometry.Modules.Tilde` (`moduleSpecΓFunctor`; Mathlib's
  `Scheme.Modules.pullback` is available through these imports).

## Scope

This is a definition-only unit. In particular, it does not state or prove:

- an identification of `tangentAtSection` or `tangentSpaceAtPoint` with
  dual-number points, with `Hom(m/m^2, k)` at a rational point, with the
  dual of a conormal sheaf, or with first-order deformations;
- any rank, local-freeness, finiteness or base-change property;
- any relation to smoothness;
- functoriality in `X` or in the section `e`.

Each of these needs its own published statement and proof.

## Verification

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiles
`Langlands.AlgebraicGeometry.PointTangentSpace` with no errors or warnings.
Inspecting `Langlands.Scheme.tangentSpaceAtPoint` reports only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`. The file contains no
`sorry`, `admit` or new axiom.
