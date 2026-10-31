# Stalk dimension at a quasi-finite point

`Langlands.AlgebraicGeometry.QuasiFiniteAtStalkDimensionStatement.{u}` is the
following `Prop`-valued definition:

```lean
∀ (X Y : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ Y),
  LocallyOfFiniteType f → ∀ (x : X), f.QuasiFiniteAt x →
    ringKrullDim (X.presheaf.stalk x) ≤
      ringKrullDim (Y.presheaf.stalk (f x))
```

In words: let `f : X ⟶ Y` be a morphism of schemes that is locally of finite
type, and let `f` be quasi-finite at a point `x` of `X`. Then the Krull dimension
of the local ring `𝒪_{X,x}` is at most the Krull dimension of the local ring
`𝒪_{Y,f(x)}`. This file defines the proposition; it does not prove it.

## Interfaces and conventions

Every ingredient is an existing Mathlib declaration. The file introduces no
replacement predicate and no separate dimension carrier.

- `AlgebraicGeometry.Scheme.{u}` is Mathlib's category of schemes. The universe
  `u` is arbitrary. `X` and `Y` lie in the same universe, as a morphism
  `X ⟶ Y` requires.
- `LocallyOfFiniteType f` is Mathlib's class
  `AlgebraicGeometry.LocallyOfFiniteType`, used here as an explicit hypothesis.
  Its field `finiteType_appLE` says that for affine opens `U ⊆ Y` and
  `V ⊆ f⁻¹(U)` the ring map `f.appLE U V e : Γ(Y, U) → Γ(X, V)` is of finite
  type.
- `f.QuasiFiniteAt x` is Mathlib's `AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt`.
  By definition the stalk map `f.stalkMap x : 𝒪_{Y,f(x)} → 𝒪_{X,x}` is
  `RingHom.QuasiFinite`, that is, `Algebra.QuasiFinite`: for every prime `P` of
  `𝒪_{Y,f(x)}` the fibre `κ(P) ⊗ 𝒪_{X,x}` is finite-dimensional over the
  residue field `κ(P)`. This predicate does **not** include any finite-type
  condition, unlike the Stacks Project notion discussed below. The
  finite-type hypothesis is therefore stated separately.
- `X.presheaf.stalk x` and `Y.presheaf.stalk (f x)` are Mathlib's stalk rings,
  and `f x` is the image of the point `x` under the underlying map of `f`.
- `ringKrullDim R : WithBot ℕ∞` is Mathlib's Krull dimension,
  `Order.krullDim (PrimeSpectrum R)`: the supremum of the lengths of chains of
  prime ideals. It is `⊥` only for the zero ring, which a stalk never is, and
  `⊤` for infinite dimension. The inequality is the order on `WithBot ℕ∞`, so
  it holds trivially when `𝒪_{Y,f(x)}` is infinite-dimensional. This is the
  usual Krull dimension of a ring, with infinite dimension allowed. No new
  dimension convention is introduced.

There is no Noetherian, reducedness, field, separatedness, quasi-compactness or
global finite-type hypothesis. In particular `X` and `Y` may be
non-Noetherian.

The module imports `Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite`, for the
quasi-finiteness predicate and finite-type morphisms, and
`Mathlib.AlgebraicGeometry.Properties`, which provides the related
stalk-dimension interface `AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`
for later work. It imports nothing from the project Library.

## Derived provenance

The mathematical source is the Stacks Project, Commutative Algebra,
Lemma 10.125.4 ([Tag 00QF](https://stacks.math.columbia.edu/tag/00QF)), in the
registered snapshot `stacks-quasifinite-local-dimension-2026-10-29` (folder
`literature/Stacks Project - Quasi-finite local dimension (HTML snapshot 2026-10-29)`,
file `00QF.html`, source SHA-256
`ba09eb08688a414f24d203beeb03d2fcd9b27ed329580051d14a815177a2f832`). It
states:

> Let `R → S` be a finite type ring map. Let `𝔮 ⊂ S` be a prime lying over
> `𝔭 ⊂ R`. If `R → S` is quasi-finite at `𝔮`, then
> `dim(S_𝔮) ≤ dim(R_𝔭)`.

The statement, proof and comment section (no comments) were read. No project
errata note for this source was found.

The source is a statement about rings. It does **not** literally state this
scheme interface. The scheme proposition is its translation through affine
neighbourhoods and stalk localization, as follows. This is the intended
correspondence, not an implemented Lean proof.

1. **Affine neighbourhoods.** Choose an affine open `U ⊆ Y` containing `f(x)`
   and an affine open `V ⊆ f⁻¹(U)` containing `x`. Put `R = Γ(Y, U)`,
   `S = Γ(X, V)` and let `R → S` be `f.appLE U V e`. The point `x` corresponds
   to a prime `𝔮` of `S`, Mathlib's `hV.primeIdealOf ⟨x, _⟩`. Its contraction
   `𝔭` to `R` corresponds to `f(x)`.
2. **Finite type.** The hypothesis `LocallyOfFiniteType f` is used exactly
   here: its field `finiteType_appLE` makes `R → S` a finite-type ring map,
   which is the standing hypothesis of Tag 00QF. A pointwise hypothesis cannot
   supply this, since `Scheme.Hom.QuasiFiniteAt` contains no finiteness of
   type. The source's definition of "quasi-finite at a prime" also applies only
   to finite-type ring maps (see below). The hypothesis is therefore retained.
   This file does not claim that it is necessary for the inequality.
3. **Quasi-finiteness at `𝔮`.** Mathlib's lemma
   `AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt.quasiFiniteAt` turns
   `f.QuasiFiniteAt x` into `(f.appLE U V e).hom.QuasiFiniteAt 𝔮`, that is,
   `S_𝔮` is a quasi-finite `R`-algebra in Mathlib's sense. Its fibre over `𝔭`
   is `κ(𝔭) ⊗_R S_𝔮 ≅ S_𝔮/𝔭S_𝔮`, because elements of `R ∖ 𝔭` are already
   units in `S_𝔮`. This fibre is finite over `κ(𝔭)`, which is condition (2)
   of the Stacks Project, Lemma 10.122.2
   ([Tag 00PK](https://stacks.math.columbia.edu/tag/00PK)). By Definition 10.122.3
   ([Tag 00PL](https://stacks.math.columbia.edu/tag/00PL)), a finite-type ring
   map satisfying the equivalent conditions of that lemma is *quasi-finite at
   `𝔮`*. Both pages are in the registered snapshot
   `stacks-quasifinite-at-prime-2026-10-30` (folder
   `literature/Stacks Project - Quasi-finite at a prime (HTML snapshot 2026-10-30)`,
   files `00PK.html` and `00PL.html`, source SHA-256
   `1835359fd8d874dcdd9ce79b59fc33be9a4ef742af77c023c064fb93925a4c59`). Their
   statements, the proof of Lemma 10.122.2 and the comments (three on 00PK,
   none reporting an error; none on 00PL) were read. The docstring of Mathlib's
   `Algebra.QuasiFiniteAt` likewise records that, for (essentially) finite-type
   algebras, its condition is equivalent to `𝔮` being isolated in its fibre,
   which is condition (1) of Lemma 10.122.2.
4. **Stalks as localizations.** Mathlib's `IsAffineOpen.isLocalization_stalk`
   identifies `𝒪_{X,x}` with the localization `S_𝔮` and `𝒪_{Y,f(x)}` with
   `R_𝔭`. Krull dimension is invariant under ring isomorphism
   (`ringKrullDim_eq_of_ringEquiv`), so Tag 00QF gives
   `ringKrullDim 𝒪_{X,x} ≤ ringKrullDim 𝒪_{Y,f(x)}`.

The source proof treats the general case without Noetherian hypotheses. When
`R_𝔭` is Noetherian it concludes from Lemma 10.112.6 (Tag 00OM) and the
definitions. In general it lets `S'` be the integral closure of `R_𝔭` in
`S_𝔭`, applies Zariski's Main Theorem 10.123.12 (Tag 00Q9) to get
`S_𝔮 = S'_{𝔮'}` for a prime `𝔮'` of `S'`, and uses Lemma 10.112.3 (Tag 00OJ)
for `dim(S') ≤ dim(R_𝔭)`. The proposition keeps this general non-Noetherian
scope. These cited lemmas were not read separately; they are described only as
the 00QF proof uses them.

## Scope and formal proof boundary

This unit states the proposition only. It proves no special case, assumes no
dimension comparison, and introduces no axioms. A separate proof task must
prove this exact published proposition.
