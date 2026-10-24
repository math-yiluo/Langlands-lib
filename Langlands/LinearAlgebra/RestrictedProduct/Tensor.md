# Canonical tensor maps into restricted products

This module defines the canonical maps that move a tensor factor inside an
algebraic restricted product:

```
M ⊗[R] Πʳ i, [N i, L i]_[ℱ]  →  Πʳ i, [M ⊗[R] N i, (image of M ⊗[R] L i)]_[ℱ],
m ⊗ x  ↦  (i ↦ m ⊗ x i).
```

It imports only `Mathlib.RingTheory.TensorProduct.Basic` and
`Mathlib.Topology.Algebra.RestrictedProduct.Basic`. The second module contains
Mathlib's algebraic restricted product `Πʳ i, [N i, B i]_[ℱ]` and its `Module`
instance. No topology on a restricted product and no topological theorem is
used. Every declaration is in the namespace `RestrictedProduct`.

The index type, the filter and the coordinate submodules are arbitrary. Each
map is defined for every `ℱ : Filter ι`, not only for `Filter.cofinite`. A
private probe instantiated `lTensor` at `Filter.principal s` and at `⊥`.

The module defines maps only. It does not prove injectivity, surjectivity or
bijectivity of any map here. It defines no equivalence and assumes no
flatness, finite presentation, bijectivity or equivalence hypothesis.

## Linear restricted-product helpers

The two helpers below are linear-map versions of Mathlib maps. The pinned
Mathlib has `RestrictedProduct.mapAlong`, `mapAlongMonoidHom`, the
`to_additive` version `mapAlongAddMonoidHom`, `mapAlongRingHom` and
`inclusion`. It has no linear-map version of these. A text search of the
pinned Mathlib sources finds no `mapAlongLinearMap`, `inclusionLinearMap` or
`rangeLTensor`, and no `LinearMap` or `→ₗ` in
`Mathlib/Topology/Algebra/RestrictedProduct/`. The current Library has no
restricted-product linear or tensor API either. Its `Langlands.RestrictedTensor`
modules construct restricted tensor products of vector spaces with reference
vectors, which is a different construction.

### `mapAlongLinearMap`

The full signature has seven universe parameters. Its arguments are:

- index types `ι₁ : Type u_1` and `ι₂ : Type u_2`, explicit coordinate
  families `R₁ : ι₁ → Type u_3` and `R₂ : ι₂ → Type u_4`, and filters
  `𝓕₁ : Filter ι₁` and `𝓕₂ : Filter ι₂`;
- subobject families `S₁ : ι₁ → Type u_5` and `S₂ : ι₂ → Type u_6`, with
  `SetLike`, `AddSubmonoidClass` and `SMulMemClass … A …` instances, and
  chosen subobjects `B₁ i : S₁ i` and `B₂ j : S₂ j`;
- an explicit `f : ι₂ → ι₁` and an explicit proof of
  `Filter.Tendsto f 𝓕₂ 𝓕₁`;
- a semiring `A : Type u_7`, additive commutative monoids `R₁ i` and `R₂ j`,
  and `A`-module structures on them;
- explicit `A`-linear maps `φ j : R₁ (f j) →ₗ[A] R₂ j`, together with an
  explicit proof that `Set.MapsTo (φ j) (B₁ (f j)) (B₂ j)` holds for
  `𝓕₂`-eventually all `j`.

The result is an `A`-linear map
`Πʳ i, [R₁ i, B₁ i]_[𝓕₁] →ₗ[A] Πʳ j, [R₂ j, B₂ j]_[𝓕₂]`.
Its underlying additive map is Mathlib's `mapAlongAddMonoidHom` built from
the same data. Additivity therefore comes from Mathlib. The new field
`map_smul'` is checked coordinatewise with `map_smul (φ i)`.

`mapAlongLinearMap_apply` is the `simp` lemma

```
mapAlongLinearMap R₁ R₂ f hf φ hφ x j = φ j (x (f j)),
```

and it holds by `rfl`.

Both declarations are needed in this module. `lTensor` and `lTensorLeft` are
built from `mapAlongLinearMap`, and the proof of `lTensorLeft_tmul` rewrites
with `mapAlongLinearMap_apply`. In the source, the later proof of
`lTensor_bijective` also uses `mapAlongLinearMap_apply`.

### `inclusionLinearMap`

Its arguments are `A : Type u_1` with `[CommRing A]`, an implicit
`ι : Type u_2`, an explicit `R : ι → Type u_3` with
`[∀ i, AddCommGroup (R i)] [∀ i, Module A (R i)]`, explicit
`A`-submodules `C i : Submodule A (R i)`, implicit filters `𝓕 𝓖 : Filter ι`,
and an explicit proof `h : 𝓕 ≤ 𝓖`. The result is

```
inclusionLinearMap A R C h : Πʳ i, [R i, C i]_[𝓖] →ₗ[A] Πʳ i, [R i, C i]_[𝓕].
```

It is `mapAlongLinearMap R R id h (fun _ ↦ LinearMap.id) _`. The `MapsTo`
side condition holds for every index, because the identity maps each `C i`
into itself. Coordinatewise, it is the identity, the linear form of Mathlib's
`RestrictedProduct.inclusion`.

No declaration in this module uses `inclusionLinearMap`. It is retained as
the one linear restricted-product definition needed by the later statement
and proof phases of parent task `2ff17b0a-7a93-4668-a2e6-b740e4205e6d`. In
the source, `lTensor_bijective` writes `M ⊗[R] Πʳ i, [N i, L i]_[ℱ]` as a
direct limit over the principal filters `𝓟 s` with `s ∈ ℱ`. The transition
maps of that direct limit are `inclusionLinearMap`
(`TensorRestrictedProduct.lean` lines 174–194, and
`IsDirectLimitRestricted.lean` lines 59–102). Putting this definition in the
definition phase lets later Prop statements name a published declaration.

## Image submodules

`rangeLTensor R M N L i` has arguments `R : Type u_1` and `M : Type u_2` with
`[CommRing R] [AddCommGroup M] [Module R M]`, an implicit `ι : Type u_3`,
`N : ι → Type u_4` with `[∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]`,
`L : ∀ i, Submodule R (N i)` and `i : ι`. It is the `R`-submodule

```
LinearMap.range (LinearMap.lTensor M (L i).subtype) ⊆ M ⊗[R] N i,
```

the image of `M ⊗[R] L i` under the map induced by the inclusion
`L i → N i`. The source docstring calls this "`M ⊗_R (L i)` as a submodule".
Without further hypotheses it is only the image. It is isomorphic to
`M ⊗[R] L i` when the induced map is injective, for instance when `M` is flat
over `R`. No such injectivity is asserted here.

`rangeLTensorLeft R M N L i` keeps the source's weaker hypotheses:
`[CommSemiring R] [CommSemiring M] [Algebra R M]`, coordinate semirings
`[∀ i, Semiring (N i)] [∀ i, Algebra R (N i)]`, and arbitrary `R`-submodules
`L i`. It is the range of Mathlib's heterobasic
`TensorProduct.AlgebraTensorModule.lTensor` applied to `(L i).subtype`, an
`M`-linear map `M ⊗[R] L i →ₗ[M] M ⊗[R] N i`. So it is the same image, now as
an `M`-submodule. Here `M` acts on `M ⊗[R] N i` through the left tensor
factor. It is declared `noncomputable`, as in the source.

## The canonical maps

### `lTensor`

```
lTensor R M N ℱ L :
  M ⊗[R] Πʳ i, [N i, L i]_[ℱ] →ₗ[R]
    Πʳ i, [M ⊗[R] N i, rangeLTensor R M N L i]_[ℱ]
```

The hypotheses are those of `rangeLTensor`, together with an explicit
`ℱ : Filter ι`. The explicit arguments come in the source order `R M N ℱ L`.
The four universes `u_1` to `u_4` of `R`, `M`, `ι` and `N` are independent.

For `m : M`, the coordinate maps `TensorProduct.mk R M (N i) m : n ↦ m ⊗ n`
send `L i` into `rangeLTensor R M N L i`. This holds for every `i`, hence
`ℱ`-eventually: the image of `n ∈ L i` is the image of `m ⊗ ⟨n, hn⟩`. Thus
`mapAlongLinearMap` with `f = id` and `Filter.tendsto_id` gives an `R`-linear
map `x ↦ (i ↦ m ⊗ x i)`. It is additive and `R`-linear in `m`, which is
checked coordinatewise by `ext; simp`. `lTensor` is `TensorProduct.lift` of
this bilinear map.

### `lTensorLeft`

```
lTensorLeft R M N ℱ L :
  M ⊗[R] Πʳ i, [N i, L i]_[ℱ] →ₗ[M]
    Πʳ i, [M ⊗[R] N i, rangeLTensorLeft R M N L i]_[ℱ]
```

Here `R` and `M` are commutative rings with `[Algebra R M]`. The coordinates
`N i` are rings with `[∀ i, Algebra R (N i)]`, and the `L i` are arbitrary
`R`-submodules. The explicit arguments again come in the order `R M N ℱ L`,
with the universes of `R`, `M`, `ι` and `N` independent. The domain is an
`M`-module through the left tensor factor. The codomain is an `M`-module by
Mathlib's restricted-product `Module` instance, with each `rangeLTensorLeft`
an `M`-submodule.

The construction takes the `R`-linear map
`g = mapAlongLinearMap … id Filter.tendsto_id (fun i ↦ (n ↦ 1 ⊗ n)) _`, so
`g x i = 1 ⊗ x i`, and applies Mathlib's `LinearMap.liftBaseChange M`.
That function sends `m ⊗ x` to `m • g x`. The coordinate subobjects of the
codomain are `M`-submodules. To view the codomain as an `R`-module and `g` as
`R`-linear, the definition supplies
`SMulMemClass (Submodule M (M ⊗[R] N i)) R _` for each `i`, by
`SMulMemClass.ofIsScalarTower`. For `liftBaseChange` it proves
`IsScalarTower R M` on the codomain, coordinatewise. Both are local `have`
terms inside the body, proved from Mathlib's existing scalar actions. No
global instance and no extra hypothesis is added.

## Pure-tensor coordinate formulas

Both formulas are `simp` lemmas:

```
lTensor_tmul R M N ℱ L m f i :
  lTensor R M N ℱ L (m ⊗ₜ f) i = m ⊗ₜ (f i)

lTensorLeft_tmul R M N L ℱ m f i :
  lTensorLeft R M N ℱ L (m ⊗ₜ f) i = m ⊗ₜ (f i)
```

The hypotheses are those of the corresponding map. In `lTensorLeft_tmul`, `L`
comes before `ℱ` among the explicit arguments, as in the source.
`lTensor_tmul` holds by `rfl`. The proof of `lTensorLeft_tmul` unfolds
`lTensorLeft` and rewrites with `LinearMap.liftBaseChange_tmul`, the
coordinate formula `smul_apply` for restricted products, and
`mapAlongLinearMap_apply`. This turns the goal into `m • (1 ⊗ₜ f i) = m ⊗ₜ f i`,
which `simp` closes using `smul_tmul'` and `m • 1 = m`. That proof runs under
`set_option backward.isDefEq.respectTransparency.types false`, as in the
source. A private check without this option fails at the
`mapAlongLinearMap_apply` rewrite.

## Checks

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) built the module
with no errors or warnings. The full unapplied types of all nine declarations
were inspected with universes shown, and the signatures above follow them.
`rangeLTensor`, `rangeLTensorLeft`, `lTensor`, `lTensorLeft`, `lTensor_tmul`
and `lTensorLeft_tmul` depend only on `propext`, `Classical.choice` and
`Quot.sound`. `mapAlongLinearMap`, `mapAlongLinearMap_apply` and
`inclusionLinearMap` depend only on `propext` and `Quot.sound`. The module
has no `sorry`, `admit` or new axiom.

## Omitted source material

- `inclusionLinearMap_apply` (source `RestrictedProduct/Basic.lean` lines
  90–91) is omitted. In the source it is declared in the root namespace, and
  no file in the source tree uses it.
- `coe_lTensorLeft_eq_lTensor`, `tmulEquivRangeLTensor`,
  `lTensorPrincipalEquiv`, `lTensor_bijective`, `lTensorLeft_bijective`,
  `lTensorEquiv` and `lTensorEquivLeft` (source lines 93 onwards) are omitted.
  Their flatness, finite-presentation, bijectivity and equivalence content
  belongs to later statement and proof phases. No definition here contains
  such a proof.
- The unused section variables `A₁` and `A₂` (source `Basic.lean` line 45)
  and the block of variable declarations at `Basic.lean` lines 22–36, which
  contains no declarations, are omitted.

## Provenance and modification notice

The source is ImperialCollegeLondon/FLT at commit
`923d45174c500aa1d994ba973bac38ea39eacbf7`, retained in registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`ImperialCollegeLondon--FLT/source`. The adapted lines are:

- [`FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean`, lines 28–91](https://github.com/ImperialCollegeLondon/FLT/blob/923d45174c500aa1d994ba973bac38ea39eacbf7/FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean#L28-L91):
  section variables 28–32, `rangeLTensor` 34–36, `rangeLTensorLeft` 38–42,
  `lTensor` 44–58, `lTensorLeft` 60–76, `lTensor_tmul` 78–81 and
  `lTensorLeft_tmul` 83–91. That file is copyright 2025 Matthew Jasper,
  author Matthew Jasper.
- [`FLT/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean`, lines 40–88](https://github.com/ImperialCollegeLondon/FLT/blob/923d45174c500aa1d994ba973bac38ea39eacbf7/FLT/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean#L40-L88):
  section variables 40–56, `mapAlongLinearMap` 58–69,
  `mapAlongLinearMap_apply` 71–74 and `inclusionLinearMap` 76–88. That file is
  copyright 2025 Matthew Jasper, authors Matthew Jasper, Kevin Buzzard and
  Ruben Van de Velde.

Both original copyright, license and author headers are retained in the Lean
file. The upstream root Apache-2.0 `LICENSE` is retained byte-for-byte at
[licenses/ImperialCollegeLondon-FLT/LICENSE](../../../licenses/ImperialCollegeLondon-FLT/LICENSE).
The source snapshot contains no `NOTICE` file.

Worker 217's modifications are:

- the two source files are combined into one standalone module, which imports
  two Mathlib modules instead of the FLT import closure. The
  `module`/`public import`/`@[expose] public section` keywords are replaced
  by plain imports, following the Library convention;
- the module docstring no longer says that `M` is flat;
- the `set_option backward.isDefEq.respectTransparency false` before
  `lTensor` (source line 44) is dropped. A private check showed that it is
  unnecessary at this project's Lean and Mathlib pin. The option before
  `lTensorLeft_tmul` is kept;
- the omissions listed above.

The declaration names, the namespace `RestrictedProduct`, binder orders,
hypotheses, definition bodies and proofs are otherwise unchanged. None of the
audit's compatibility patches (a)–(d) applies to these lines, and no
Anthropic derivative code is used. The public audit
[finite-adele base change](../../../notes/reuse/finite-adele-base-change-audit.md),
sections 2–6 and Appendix B, describes the surrounding source closure.
