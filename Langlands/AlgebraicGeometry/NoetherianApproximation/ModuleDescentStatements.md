# Descent of finitely presented modules to finitely generated subalgebras

This module defines one proposition in namespace
`Langlands.AlgebraicGeometry.NoetherianApproximation`, for an arbitrary universe `u`. It does
not prove it. The proposition is a noetherian-approximation step for finitely presented module
sheaves on a scheme over an affine base.

## Setting

`FinitePresentationModuleSubalgebraDescentStatement` quantifies over:

- commutative rings `A₀` and `A` in `Type u`, with `A₀` noetherian (`[IsNoetherianRing A₀]`)
  and an algebra structure `[Algebra A₀ A]`;
- a scheme `X₀` with a morphism `f₀ : X₀ ⟶ Spec (CommRingCat.of A₀)` that is quasi-compact,
  separated and locally of finite type (`[QuasiCompact f₀] [IsSeparated f₀]
  [LocallyOfFiniteType f₀]`);
- a scheme `X` with morphisms `a : X ⟶ X₀` and `f : X ⟶ Spec (CommRingCat.of A)` satisfying

  ```lean
  IsPullback a f f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))
  ```

  So `X` is a base change of `X₀` to `Spec A`, given by any pullback square, not necessarily
  Mathlib's chosen one;
- a module sheaf `M : X.Modules` that is locally finitely presented, in the sense of Mathlib's
  `SheafOfModules.IsFinitePresentation` (finite presentations on the members of an open cover);
- a finite set `s : Finset A`.

## Conclusion

There is a finitely generated `A₀`-subalgebra `T` of `A` containing `s`
(`T.FG ∧ (↑s : Set A) ⊆ T`) and a module sheaf `M₀` on Mathlib's chosen fibre product
`pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))`, the base change of `X₀` to
`Spec T`, such that:

- `M₀.IsFinitePresentation` holds;
- for every morphism `c : X ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))`
  with `c ≫ pullback.fst _ _ = a` and
  `c ≫ pullback.snd _ _ = f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥T A))`, there is an
  isomorphism `(Scheme.Modules.pullback c).obj M₀ ≅ M`. Module pullback is Mathlib's
  `AlgebraicGeometry.Scheme.Modules.pullback`.

A morphism `c` satisfying the two equations is the canonical comparison map from `X` to the
base change over `Spec T`; it is unique by the universal property of the fibre product. The
conclusion therefore says that `M` is, up to isomorphism, the pullback of the finitely
presented module `M₀` along the map from `X` to the stage over `Spec T`. The proposition asserts
only that such an isomorphism exists; no compatibility of these isomorphisms is asserted.

The shape of the conclusion (a finitely generated subalgebra containing `s`, a module on the
chosen base change, and the comparison along every compatible `c`) is the same as in the
published `LineBundleSubalgebraDescentStatement` of
`Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleDescentStatements`, with
local finite presentation in place of being locally free of rank one.

## Sources and provenance

Stacks Project, Chapter 32 *Limits of Schemes*, `limits.tex` at commit
`a04446e57ec1fbc252a871afcec7752fb2807b14` (registered as `stacks-limits-of-schemes-a04446e5`),
Lemma `lemma-descend-modules-finite-presentation` (tag 01ZR, lines 2547–2605; part (1) at lines 2558–2562): for a
directed inverse system of quasi-compact quasi-separated schemes `S_i` with affine transition
morphisms and limit `S`, every `𝒪_S`-module of finite presentation is the pullback of an
`𝒪_{S_i}`-module of finite presentation for some `i`.

The proposition is a special case. The inverse system is the base change of `X₀` to `Spec T`
for the finitely generated `A₀`-subalgebras `T` of `A`, ordered by inclusion. Its transition
morphisms are affine, being base changes of morphisms of affine schemes, and `A` is the directed
union of the `T`, so `X` is the limit. The statement adds hypotheses that the source does not
need: `A₀` noetherian and `f₀` separated and locally of finite type (in addition to
quasi-compact, which with separatedness gives the source's quasi-compactness and
quasi-separatedness). These are the hypotheses available where the statement is used, in the
noetherian approximation of a proper finitely presented scheme over an affine base. The
presentation by an arbitrary pullback square, the chosen fibre product over `Spec T`, and the
quantification over compatible `c` are internal formulation choices, made to match the
published line-bundle descent statement.
