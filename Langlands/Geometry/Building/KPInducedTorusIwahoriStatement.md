# Iwahori subgroup of an induced torus over `K` (KP Lemma 2.5.18)

Authors: Workers 1532 and 1341. The Lean statement is Worker 1532's shared
draft, reused unchanged; Worker 1341 checked it against the Library
interfaces and the source and wrote this exposition.

`Langlands.Geometry.Building.InducedTorusIwahoriStatement.{u}` is a
proposition definition, not a theorem. It states the case `k = K` of KP
Lemma 2.5.18: for an induced torus `T` over KP's field `K`, the Iwahori
subgroup `T(K)^0` equals the maximal bounded subgroup `T(K)^1`. Nothing
here proves it.

## The proposition

For every `F : Type u` with `[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`, write `K := UnramifiedClosure F`. For every

- `T : CommGroupScheme (Spec (CommRingCat.of K))` with
  `[IsAffine T.X.left]`, and
- `L : IntermediateField K (SeparableClosure F)` with
  `[FiniteDimensional K L]` and `[IsGalois K L]`,

if

1. `IsSplitTorus (GaloisPointComparison.baseChanged K L T.toGrp)`, that is,
   `L` splits `T`, and
2. `IsInducedTorus T`, that is, `T` is induced,

then

```text
torusNormIwahori K L (intermediateValuation F L) T =
  characterValuationKernel (LocalGalois.Separable.fixedFieldValuation F) T.toGrp
```

as subgroups of `rationalPoints T.toGrp`, the group `T(K)`.

These are all the quantified data and hypotheses. The universe `u` is
arbitrary and `F` may have either characteristic. The module imports only
`Langlands.Geometry.Building.KPZeroSubgroups` and
`Langlands.GroupScheme.Torus.Induced`.

## Exact objects

- `UnramifiedClosure F` (module `Langlands.Geometry.Building.KPZeroSubgroups`)
  abbreviates `LocalGalois.Separable.inertiaFixedField F`, the fixed field
  in `SeparableClosure F` of the inertia subgroup. It is KP's `K`, the
  maximal unramified extension of `F` in the fixed separable closure.
- `LocalGalois.Separable.fixedFieldValuation F` (module
  `Langlands.Galois.Local.SeparableInertiaDefinitions`) is the restriction
  to `K` of the spectral valuation `LocalGalois.Separable.sepClosureValuation F`
  of `F^sep`, the unique extension of the valuation of `F`.
  `intermediateValuation F L` is the restriction of the same valuation to
  `L`. So the valuations on `K` and on `L` are compatible.
- `IsInducedTorus T` (module `Langlands.GroupScheme.Torus.Induced`) is the
  Library form of KP Definition 2.5.1 for the `K`-group `T`: there are a
  finite Galois extension `E/K` with `T_E` split and a `ℤ`-basis of the
  character lattice `X^*(T_E)` that `Gal(E/K)` permutes. Its paired
  Markdown explains why existence of some such `E` matches KP's use of the
  splitting extension. `E` is independent of `L`.
- `characterValuationKernel v H` is
  `{g ∈ H(k) | v(χ(g)) = 1 for every k-rational character χ of H}`. With
  `v = fixedFieldValuation F` and `H = T`, the `K`-rational characters are
  KP's `X^*(T)^Θ` with `Θ = Gal(K^s/K)`, so the right side is
  `{t ∈ T(K) | ω(χ(t)) = 0 for all χ ∈ X^*(T)^Θ}` written
  multiplicatively. This is KP's `T(K)^b = T(K)^1` in the second
  description of Proposition 2.5.8.
- `torusNormIwahori K L v T` is the image of
  `characterValuationKernel v T_L` under the Library norm
  `GaloisPointComparison.rationalNorm K L T : T(L) → T(K)`. By hypothesis 1,
  `T_L` is split, so every character of `T_L` is `L`-rational and the source
  group is `{t ∈ T(L) | ω(χ(t)) = 0 for all χ ∈ X^*(T)}`, KP's `T(L)^b`
  (Proposition 2.5.8, third description). Its norm image is KP's `T(K)^0`
  of Definition 2.5.13, computed with the given splitting field `L`.

The proposition fixes one splitting field `L` but quantifies over all of
them. It therefore asserts the equality for every finite Galois `L/K`
inside `F^sep` that splits `T`, and it does not use or assert that the norm
image is independent of `L` (KP Lemma 2.5.12).

## Source and derived formulation

Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach*,
Cambridge University Press, 2023, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. Printed page = PDF page − 31.

- §2.5(a), Definition 2.5.1, printed p. 86 / PDF p. 117: an `F`-torus `T`
  is induced if `X^*(T)`, equivalently `X_*(T)`, has a `ℤ`-basis invariant
  under the Galois group of the splitting extension of `T`.
- §2.5(c), Proposition 2.5.8, printed p. 88 / PDF p. 119: `T(k)` has a
  unique maximal bounded subgroup `T(k)^b = T(k)^1`, equal to the kernel of
  `ω_T`, to `{x | ω(χ(x)) = 0 for all χ ∈ X^*(T)^Θ}` and to
  `{x | ω(χ(x)) = 0 for all χ ∈ X^*(T)}`.
- §2.5(d), Remark 2.5.11 and Definition 2.5.13, printed pp. 89–90 / PDF
  pp. 120–121: `T(K)^0` is the image of `T(L)^b` under the norm
  `T(L) → T(K)` for a finite Galois `L/K` splitting `T`, and
  `T(k)^0 = T(K)^0 ∩ T(k)`.
- Definition 2.5.16, printed p. 91 / PDF p. 122: a `k`-torus `T` has
  induced ramification if `T_K` is induced in the sense of
  Definition 2.5.1.
- Lemma 2.5.18, printed p. 91 / PDF p. 122: if `T` has induced
  ramification, then `T(k)^0 = T(k)^1`. The proof reduces to `k = K`, and
  then to `T = R_{L/K} 𝔾_m`. For a Galois `M/K` containing `L` it writes the
  norm `T(M) = (L ⊗_K M)^× → T(K) = L^×` through `L ⊗_K M ≅ ∏_τ M`, and
  uses Remark 2.5.11 to show that `∏_τ O_M^×`, which is the bounded subgroup
  of `T(M)`, maps onto `O_L^× = T(K)^1`.

This proposition is the case `k = K` of Lemma 2.5.18. For `k = K` one has
`T_K = T`, so "induced ramification" (Definition 2.5.16) is the hypothesis
that `T` itself is induced, which is hypothesis 2. KP's reduction from a
general `k` to `K`, through `T(k)^0 = T(K)^0 ∩ T(k)` and
`T(k)^1 = T(K)^1 ∩ T(k)`, is not part of this proposition. Hypothesis 1 is
the choice of splitting field in Definition 2.5.13, made explicit and
universally quantified as explained above. KP's `k` is any discretely
valued Henselian field with perfect residue field; here the base is the
maximal unramified extension, inside `F^sep`, of a nonarchimedean local
field `F`, which is the setting of the Library's `KPZeroSubgroups` module.
The hypothesis `[IsAffine T.X.left]` is needed to form `torusNormIwahori`;
KP's tori are affine.

KP Lemma 2.6.27, printed p. 105 / PDF p. 136, uses Lemma 2.5.18 for the
induced `K`-torus `D = T/T_sc`, a quotient of a maximally split maximal
torus `T` of a minimal Levi subgroup of a simply connected group: the image
of `m ∈ M_0(K)^1` lies in `D(K)^1`, which equals `D(K)^0` by Lemma 2.5.18.

The authors' corrections of 1 November 2024, registered as
`kaletha-prasad-2024-corrections`, PDF p. 24, were checked. In §2.5 they
correct the formula for `ω_T` to `t ↦ (χ ↦ ω(χ(t)))`, replace "§7" by "§6"
in the citation of Serre's *Local Fields*, Chapter V, in Remark 2.5.11,
and replace the example of Remark 2.5.15. They do not change
Definitions 2.5.1, 2.5.13 or 2.5.16, Proposition 2.5.8 or Lemma 2.5.18.
The corrected formula has the same kernel as the multiplicative condition
`v(χ(t)) = 1` used here.

The inclusion `T(K)^0 ⊆ T(K)^1` is part of KP Lemma 2.5.14 (printed p. 90 /
PDF p. 121); the content of
Lemma 2.5.18 is the reverse inclusion. The unit-norm input of Remark
2.5.11 over `K` is stated separately in the Library as
`Langlands.ClassFieldTheory.Local.SeparableInertiaUnitNormSurjectivity`,
which this module does not import.

The statement supplies no proof. A proof is a separate obligation.
