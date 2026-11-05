# Surjectivity of Iwahori subgroups of tori over `K`

Authors: Workers 1532 and 1444. The statement and initial exposition reuse
Worker 1532's shared draft; Worker 1444 checked the source correspondence
and completed the source and correction notes.

`Langlands.Geometry.Building.TorusIwahoriSurjectivityStatement.{u}` is a
proposition definition, not a proof. It states the form of KP Lemma
2.5.20(1) that KP's proof establishes: a morphism of `K`-tori that is
surjective on cocharacters over a common splitting field maps `T₂(K)^0`
onto `T₃(K)^0`.

## The proposition

For every `F : Type u` with `[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`, write `K := UnramifiedClosure F` and, for
an intermediate field `L`, write `(-)_L` for
`CommGroupScheme.baseChange (GaloisPointComparison.baseMap K L)`. For every

- `T₂ T₃ : CommGroupScheme (Spec (CommRingCat.of K))` with
  `[IsAffine T₂.X.left]` and `[IsAffine T₃.X.left]`,
- morphism `f : T₂ ⟶ T₃` of commutative group schemes over `K`,
- `L : IntermediateField K (SeparableClosure F)` with
  `[FiniteDimensional K L]` and `[IsGalois K L]`,

if

1. `IsSplitTorus (GaloisPointComparison.baseChanged K L T₂.toGrp)`,
2. `IsSplitTorus (GaloisPointComparison.baseChanged K L T₃.toGrp)`, and
3. the map `X_*(T₂_L) → X_*(T₃_L)`, `ν ↦ ν ≫ f_L`, is surjective,

then

```text
(torusNormIwahori K L (intermediateValuation F L) T₂).map
    (rationalPoints.map (CommGroupScheme.groupHom f)) =
  torusNormIwahori K L (intermediateValuation F L) T₃
```

as subgroups of `rationalPoints T₃.toGrp`, the group `T₃(K)`.

These are all the quantified data and hypotheses. The universe `u` is
arbitrary and `F` may have either characteristic.

## Exact objects

- `UnramifiedClosure F` is KP's `K`, the inertia fixed field in
  `SeparableClosure F`.
- `cocharacterLattice T = (Gm S ⟶ T)` (module
  `Langlands.GroupScheme.Torus.Lattice`) is `X_*(T)`; hypothesis 3 uses the
  actual base change of `f` to `L`.
- `CommGroupScheme.groupHom f` is the underlying morphism of group schemes,
  and `rationalPoints.map` is the induced homomorphism `T₂(K) → T₃(K)`.
- `torusNormIwahori K L (intermediateValuation F L) T` is the image under
  the norm `T(L) → T(K)` of the kernel of the valuations of the characters
  of `T_L`. For `T` split over `L` it is KP's `T(K)^0` (Definition 2.5.13),
  computed with the given `L`. `intermediateValuation F L` is the
  restriction to `L` of the spectral valuation of `F^sep`.

The inclusion `≤` is already proved in the Library as
`map_torusNormIwahori_le` (module
`Langlands.Geometry.Building.KPTorusNormNaturality`, KP Lemma 2.5.19), from
naturality of the rational norm. The content of the proposition is the
reverse inclusion. This module does not import that one.

## Source and derived formulation

Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach*,
Cambridge University Press, 2023, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. Printed page = PDF page − 31.

- Definition 2.5.13, printed p. 90 / PDF p. 121: `T(K)^0` is the norm image
  of `T(L)^b`.
- Lemma 2.5.19, printed p. 91 / PDF p. 122: a morphism of tori maps
  `T(k)^0` into `T'(k)^0`.
- Lemma 2.5.20(1), printed p. 91 / PDF p. 122, with its proof on printed
  p. 92 / PDF p. 123: for an exact sequence `1 → T₁ → T₂ → T₃ → 1` of
  `K`-tori, `T₂(K)^0 → T₃(K)^0` is surjective. The proof chooses a finite
  Galois `E/K` splitting the three tori and tensors the exact sequence
  `0 → X_*(T₁) → X_*(T₂) → X_*(T₃) → 0`. Interpreting the tensor
  coefficient as the unit group `O_E^×` gives surjectivity of
  `T₂(E)^0 → T₃(E)^0`; the norm and its naturality then give the asserted
  surjectivity over `K`. The printed proof writes `O_E` in the tensor
  step. The multiplicative torus calculation uses `O_E^×`; this explains
  the intended coefficient rather than asserting a formal comparison
  proved in this unit.

The proposition is a derived formulation. KP's proof uses the exact
sequence only through the surjectivity of `X_*(T₂) → X_*(T₃)` over the
splitting field, which is hypothesis 3. For an exact sequence of tori this
surjectivity holds, so KP's statement is a special case; that implication
is not proved here. Hypotheses 1 and 2 say that the given `L` splits `T₂`
and `T₃`, so both are tori. No kernel `T₁` is named.

The authors' corrections of 1 November 2024, registered as
`kaletha-prasad-2024-corrections`, PDF pp. 24–25, were checked. The
Section 2.5 changes correct the sign of the character-valuation map, a
reference in Remark 2.5.11, and the example in Remark 2.5.15. They do not
change Definition 2.5.13 or Lemma 2.5.20. Reversing the valuation sign
does not change its kernel. No project errata file for these sources
was found.

KP Lemma 2.6.27, printed p. 105 / PDF p. 136, applies Lemma 2.5.20 to the
quotient map `T → D = T/T_sc` to lift an element of `D(K)^0` to `T(K)^0`.

The statement supplies no proof. A proof is a separate obligation.
