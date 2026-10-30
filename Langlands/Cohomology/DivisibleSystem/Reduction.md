# The ℓ-divisible system of reductions of an ℓ-torsion-free object

Author: Worker 61. Built on the published modules
`Langlands.Cohomology.DivisibleSystem` (`powSMul`, `powSMul_zero`,
`powSMul_comp_powSMul`, `comp_powSMul`, `DivisibleSystem`, its morphisms and
`hom_ext`), `Langlands.Cohomology.DivisibleSystem.Cokernel` (`ofFlat`) and
`Langlands.Cohomology.DivisibleSystem.FreeTorsionProjective`
(`powSMul_hom_apply`). From Mathlib it uses cokernels (`cokernel`,
`cokernel.π`, `cokernel.desc`, `cokernelIsCokernel`, `CokernelCofork.ofπ`),
short complexes and short exact sequences
(`ShortComplex.exact_of_g_is_cokernel`, `ShortComplex.exact_iff_epi`), the
snake lemma (`ShortComplex.SnakeInput` with `L₃_exact`, `L₂'_exact` and
`epi_L₃_g`), refinements in abelian categories
(`ShortComplex.exact_iff_exact_up_to_refinements`,
`surjective_up_to_refinements_of_epi`), `KernelFork.IsLimit.ofMonoOfIsZero`,
`CokernelCofork.IsColimit.ofId`, `ObjectProperty.FullSubcategory`,
`Rep.mono_iff_injective` and `IsSMulRegular`.

## Conventions

`C` is an abelian category (preadditive in the first section) and `ℓ` a
natural number. `powSMul ℓ m X` is the published endomorphism
"multiplication by `ℓ ^ m`" of an object `X`. Write `L / ℓ ^ m L` for
`cokernel (powSMul ℓ m L)` and `π_m : L ⟶ L / ℓ ^ m L` for its projection.
"Multiplication by `ℓ` is a monomorphism on `L`" is the instance argument
`[Mono (powSMul ℓ 1 L)]`. As in the published Cokernel module, `i` and `j`
denote the maps `T m' ⟶ T m` and `T m ⟶ T (m - m')` of an `ℓ`-divisible
system (`m' < m`). Element language ("the class of `x`") describes
statements about morphisms out of `L`.

## Monomorphisms (namespace `Langlands.Cohomology`)

- `mono_powSMul ℓ L m`: if multiplication by `ℓ` is a monomorphism on `L`, so
  is multiplication by `ℓ ^ m`, for every `m`. Induction on `m`: `ℓ ^ 0` is
  the identity (`powSMul_zero`), and `ℓ ^ (m + 1)` is `ℓ ^ m` followed by `ℓ`
  (`powSMul_comp_powSMul`), a composite of monomorphisms.
- `mono_powSMul_one_iff_isSMulRegular ℓ X`: for a representation `X` of a
  monoid `G` over a commutative ring `R` (an object of `Rep R G`),
  multiplication by `ℓ` is a monomorphism if and only if the scalar
  `(ℓ : R)` is a non-zero-divisor on `X` (`IsSMulRegular X (ℓ : R)`, that is,
  `x ↦ ℓ • x` is injective). Monomorphisms in `Rep R G` are the injective
  maps, and the underlying map of `powSMul ℓ 1 X` is `x ↦ ℓ • x`
  (`powSMul_hom_apply`).

## The reductions (namespace `Langlands.Cohomology.DivisibleSystem`)

`L` is an object of `C`; no hypothesis on `L` is needed until
`shortExact_powSMul_reductionπ`. Every declaration takes `ℓ` and `L` as
explicit arguments; they are omitted below where the meaning is clear.

- `powSMul_comp_cokernelπ_of_le ℓ L h` and `powSMul_comp_reductionπ_of_le`:
  for `h : n ≤ m`, multiplication by `ℓ ^ m` followed by `π_n` is zero,
  because `ℓ ^ m` is `ℓ ^ (m - n)` followed by `ℓ ^ n`.
- `reductionTower ℓ L : ℕᵒᵖ ⥤ C` has object `L / ℓ ^ m L` at `m`. For
  `n ≤ m` its map `L / ℓ ^ m L ⟶ L / ℓ ^ n L` is induced by `π_n`
  (`cokernel.desc`), the projection. Identity and composition laws are
  checked after composing with the projections.
- `reductionπ ℓ L m` is `π_m`. It is an epimorphism (instance).
  `powSMul_comp_reductionπ` says that `ℓ ^ m` followed by `π_m` is zero, and
  `reductionπIsCokernel` that `π_m` is a cokernel of `ℓ ^ m`.
  `reductionπ_map` says that the maps of `reductionTower` commute with the
  projections.
- `reductionInclusion ℓ L h`, for `h : m' < m`, is the map
  `i : L / ℓ ^ m' L ⟶ L / ℓ ^ m L` induced by `ℓ ^ (m - m')` followed by
  `π_m`. This is well defined since `ℓ ^ m'` followed by `ℓ ^ (m - m')` is
  `ℓ ^ m`. `reductionπ_inclusion` says that `i` sends the class of `x` to the
  class of `ℓ ^ (m - m') x`.
- `reduction_powSMul_eq_zero m`: multiplication by `ℓ ^ m` is zero on
  `L / ℓ ^ m L`. It commutes with `π_m` (`comp_powSMul`), and `π_m` is an
  epimorphism.
- `reductionInclusion_comp h`: `i` followed by the projection
  `j : L / ℓ ^ m L ⟶ L / ℓ ^ (m - m') L` is zero. After composing with
  `π_{m'}` it is `ℓ ^ (m - m')` followed by `π_{m - m'}`.
- `shortExact_powSMul_reductionπ ℓ L m`: if multiplication by `ℓ` is a
  monomorphism on `L`, the sequence `0 ⟶ L ⟶ L ⟶ L / ℓ ^ m L ⟶ 0` with maps
  `ℓ ^ m` and `π_m` is short exact. Exactness holds because `π_m` is a
  cokernel, and the first map is a monomorphism by `mono_powSMul`.

From here on multiplication by `ℓ` is a monomorphism on `L` (section
instance argument).

- `reductionSnakeInput ℓ L h`, for `h : m' < m`, is a snake input
  (`ShortComplex.SnakeInput`). Its middle rows are `L ⟶ L ⟶ 0` (identity,
  zero) and `L ⟶ L ⟶ L / ℓ ^ (m - m') L` (`ℓ ^ (m - m')`, then
  `π_{m - m'}`). The vertical maps between them are `ℓ ^ m'`, `ℓ ^ m` and
  `0`. The bottom row is `L / ℓ ^ m' L ⟶ L / ℓ ^ m L ⟶ L / ℓ ^ (m - m') L`
  (`i`, then `j`), the cokernels of the vertical maps, with projections
  `π_{m'}`, `π_m` and the identity. The top row is the zero complex
  `0 ⟶ 0 ⟶ 0`, the kernels of the vertical maps: the first two are
  monomorphisms by `mono_powSMul`, and the third starts at a zero object.
  The first middle row is exact with an epimorphism onto `0`; the second is
  exact with first map a monomorphism.
- `reduction_shortExact h`: the sequence
  `0 ⟶ L / ℓ ^ m' L ⟶ L / ℓ ^ m L ⟶ L / ℓ ^ (m - m') L ⟶ 0` of `i` and `j` is
  short exact. The snake lemma gives exactness of the bottom row
  (`L₃_exact`) and that `j` is an epimorphism (`epi_L₃_g`). The connecting
  morphism starts at the zero object, so it is zero, and exactness at the
  next spot of the snake sequence (`L₂'_exact`) makes `i` a monomorphism.
- `reduction_flat a b`: on `L / ℓ ^ (a + b) L`, the kernel of
  multiplication by `ℓ ^ b` is the image of multiplication by `ℓ ^ a`. Let
  `z` be killed by `ℓ ^ b` and lift it to `y` in `L`. Then `π_{a+b}` kills
  `ℓ ^ b y`, so `ℓ ^ b y = ℓ ^ (a + b) x` for some `x` in `L`, by
  `shortExact_powSMul_reductionπ`. Since `ℓ ^ b` is a monomorphism,
  `y = ℓ ^ a x`, and `z` is `ℓ ^ a` times the class of `x`. The proof
  carries out this chase with refinements.
- `reductionSystem ℓ L` (the entry declaration): the `ℓ`-divisible system
  `{L / ℓ ^ m L}`, built by the published `ofFlat` from `reductionTower`,
  `reductionInclusion` and the results above; its field `torsion_exact`
  comes from `ofFlat`. `reductionSystem_tower` and
  `reductionSystem_inclusion` identify its tower and its maps `i`.

## Functoriality

`f : L ⟶ L'` and `g : L' ⟶ L''` are morphisms of `C`.

- `reductionMap ℓ f m : L / ℓ ^ m L ⟶ L' / ℓ ^ m L'` is induced by `f`
  followed by `π_m` for `L'`; it is well defined because `f` commutes with
  `ℓ ^ m`. `reductionπ_reductionMap` says that it sends the class of `x` to
  the class of `f x`.
- `reductionTowerMap ℓ f : reductionTower ℓ L ⟶ reductionTower ℓ L'` is the
  natural transformation with these components (`reductionTowerMap_app`,
  `reductionπ_reductionTowerMap_app`). `reductionTowerMap_id` and
  `reductionTowerMap_comp` say that it preserves identities and composition.
- `reductionSystemMap ℓ f : reductionSystem ℓ L ⟶ reductionSystem ℓ L'`,
  when multiplication by `ℓ` is a monomorphism on `L` and on `L'`, is the
  morphism of `ℓ`-divisible systems with underlying natural transformation
  `reductionTowerMap ℓ f` (`reductionSystemMap_tower`). It commutes with the
  maps `i` because both composites send the class of `x` to the class of
  `ℓ ^ (m - m') (f x)`. `reductionSystemMap_id` and `reductionSystemMap_comp`
  give the functor laws.
- `powSMulMono C ℓ : ObjectProperty C` is the property "multiplication by `ℓ`
  is a monomorphism".
- `reductionFunctor ℓ` is the functor from the full subcategory of such
  objects to `DivisibleSystem C ℓ` sending `L` to `reductionSystem ℓ L` and
  `f` to `reductionSystemMap ℓ f` (`reductionFunctor_obj`).

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 4, printed p.311 (one-based PDF
page 13; Worker 61 read the rendered scanned page): "Now we want to let `m`
vary. Let the `K_ℓ`-modules `(ρ, W)` and `𝓛 = 𝓛_W` be as in §3; let
`𝓛_m = 𝓛 ⊗_𝒪 𝒪_m` for any `m`. Then `𝓛_m` forms an inverse system of
`𝒪`-modules, and the inverse system `{𝓛̃_m}` defines a lisse `ℓ`-adic sheaf
`W̃ = lim 𝓛̃_m ⊗_𝒪 L_ℓ` on `S̄_K(N)`." In §3 (printed p.307, one-based PDF
page 9): "Let `𝒪` denote the ring of integers of `L_ℓ`, and let `𝓛_W` be a
`K_ℓ`-stable `𝒪`-lattice in `W(L)`."

In our reading `𝒪_m` is `𝒪/ℓ^m𝒪`: §3 (printed p.308) uses `𝒪/ℓ^m𝒪` as the
coefficients at level `m` (the modules `D_m(K_ℓ) = C(K_ℓ, 𝒪/ℓ^m𝒪)`), and on
p.312 Harris calls the modules built from `𝓛_m` free
`𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules. The identification
`𝓛 ⊗_𝒪 𝒪/ℓ^m𝒪 = 𝓛/ℓ^m𝓛` is the standard isomorphism `M ⊗_R R/I ≅ M/IM`,
which is not formalized here; the Lean works with the cokernels
`L / ℓ ^ m L` directly. A lattice is a free `𝒪`-module, so multiplication by
`ℓ` on it is injective: this is the hypothesis `[Mono (powSMul ℓ 1 L)]`,
and `mono_powSMul_one_iff_isSMulRegular` restates it for representations.
Applied in `Rep 𝒪 K_ℓ` to `L = 𝓛_W`, `reductionSystem ℓ L` is the inverse
system `{𝓛_m}` of `𝒪[K_ℓ]`-modules; this application is our interpretation.

Harris states only that the `𝓛_m` form an inverse system. This module
proves more: they satisfy the axioms of an `ℓ`-divisible system of (2.1)
(section 2, printed p.304), as formalized in the published
`DivisibleSystem`, whose field `flat` renders freeness over `ℤ/ℓ^m`. For a
lattice these are standard facts. The formulation and all proofs are ours;
the module is derived.

The Library module `Langlands.Coefficients.AdicSystem` builds the quotient
system `M / I ^ n M` of a module `M` over a ring `R` in `ModuleCat R`. The
present module works in an arbitrary abelian category, with multiplication
by `ℓ ^ m`, and proves the `ℓ`-divisible-system axioms; the two are not
compared.

## Scope

The module does not construct the lisse sheaves `𝓛̃_m` on `S̄_K(N)`, their
inverse limit `W̃`, or the lattice `𝓛_W`. It does not prove the isomorphism
`𝓛 ⊗_𝒪 𝒪_m ≅ 𝓛/ℓ^m𝓛`.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
