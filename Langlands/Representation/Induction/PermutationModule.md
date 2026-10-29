# Compact induction of trivial representations as permutation modules

Author: Worker 61. Built on the published
`Langlands.Representation.Induction.OpenAdjunction` (`quotientSupport_finite`,
`compactFunctions_ext`) and, through it, on
`Langlands.Representation.Induction.Definitions` (`LeftQuotient`,
`quotientMap`, `eval`, `CompactFunctions`, `compactFunctionOf`,
`compactInduced`, `compactInductionFunctor`), on the Library's smooth
representations (`IsSmooth`, `smoothVectors`, `SmoothRep`, `SmoothRep.of`,
`SmoothRep.ofHom`, `SmoothRep.mkIso`). From Mathlib it uses finitely
supported functions (`Finsupp.lmapDomain`, `Finsupp.mapRange.linearMap`,
`Finsupp.curryLinearEquiv`, `Finsupp.domLCongr`, `Finsupp.ofSupportFinite`),
the monoid algebra (`MonoidAlgebra.coeffLinearEquiv`), the representations
`Representation.ofMulAction`, `Representation.leftRegular`,
`Representation.free`, `Representation.finsupp` and `Representation.trivial`,
equivalences of representations (`Representation.Equiv`), the functor
`Rep.trivialFunctor`, and `QuotientGroup.quotientRightRelEquivQuotientLeftRel`
(the bijection `H \ G ≃ G ⧸ H` induced by `x ↦ x⁻¹`).

All new names are in the namespace `Langlands.Induction`. `R` is a
commutative ring and `M`, `N` are `R`-modules.

## Conventions

`G ⧸ H` is Mathlib's quotient by the left cosets `x H`, on which `G` acts by
left multiplication. The published compact induction uses right cosets:
`CompactFunctions H σ` consists of the functions `f : G → V` with
`f (h x) = σ h (f x)` for `h ∈ H`, fixed under right translation by some open
subgroup of `G`, whose support has compact image in `H \ G`
(`LeftQuotient H`); `eval H σ f.1 x` is the value `f x`, and
`compactInduced H σ` lets `g` act by right translation, `(g f)(x) = f (x g)`.
The identifications below pass from `H \ G` to `G ⧸ H` by `H x ↦ x⁻¹ H`.

## Permutation representations

`G` is a group acting on a set `X`.

- `permutation R G X M`: the representation of `G` on finitely supported
  functions `X →₀ M` in which `g` moves the value at `x` to `g • x`; it is
  Mathlib's `Finsupp.lmapDomain` along `x ↦ g • x`.
- `permutation_single g x m` (simp lemma): `g` sends the function with single
  value `m` at `x` to the function with single value `m` at `g • x`.
- `permutation_apply g φ x`: the value of `g • φ` at `x` is `φ (g⁻¹ • x)`.
- `permutationMap f`: for an `R`-linear map `f : M → N`, applying `f` to the
  values is an intertwining map from `permutation R G X M` to
  `permutation R G X N`; `permutationMap_apply` gives its values.
- `permutationSelfEquiv R G X`: with coefficients `R`, the permutation
  representation is equivalent to Mathlib's `Representation.ofMulAction R G X`
  on the monoid algebra `R[X]`; the linear equivalence is the inverse of
  `MonoidAlgebra.coeffLinearEquiv`, and the intertwining condition holds by
  definition.
- `permutationFinsuppEquiv R G X I`: with coefficients in the free module
  `I →₀ R`, the permutation representation is equivalent to
  `(Representation.ofMulAction R G X).finsupp I`, the direct sum over `I` of
  copies of `R[X]`. The linear equivalence uncurries `X →₀ I →₀ R` to
  `X × I →₀ R`, swaps the factors, curries to `I →₀ X →₀ R` and applies the
  inverse of `MonoidAlgebra.coeffLinearEquiv` to each value.

## Smoothness on cosets of an open subgroup

`G` is a topological group and `H` a subgroup with `hH : IsOpen (H : Set G)`.

- `isOpen_stabilizer_mk H hH x`: the stabilizer of the coset `x H` in `G`,
  which is `x H x⁻¹`, is open.
- `cosetStabilizer H hH x`: that stabilizer as an open subgroup.
- `isSmooth_permutation H hH`: the permutation representation of `G` on
  `G ⧸ H →₀ M` is smooth. Each finitely supported function is a finite sum of
  functions with a single value, and the function with single value at `x H`
  is fixed by `cosetStabilizer H hH x`; smooth vectors form a submodule.

## Compact induction of a trivial representation

`G` is a topological group, `H` a subgroup with `hH : IsOpen (H : Set G)`,
and `Representation.trivial R H M` the trivial representation of `H` on `M`.

- `cosetValue H f q`: for `f` in `CompactFunctions H (trivial R H M)`, the
  value of `f` at `y⁻¹` for any `y` with `q = y H`; it is well defined since
  `f` is invariant under left translation by `H`. `cosetValue_mk` states the
  defining equation.
- `cosetValue_support_finite H hH f`: `cosetValue H f` has finite support.
  The published `quotientSupport_finite` says that the image of the support
  of `f` in `H \ G` is finite for `H` open; its image under `H \ G ≃ G ⧸ H`
  contains the support of `cosetValue H f`.
- `toPermutation R M H hH`: the `R`-linear map sending `f` to
  `cosetValue H f` as a finitely supported function on `G ⧸ H`;
  `toPermutation_mk` gives its value at `y H` as `f (y⁻¹)`.
- `ofPermutation H hH φ`: for `φ : G ⧸ H →₀ M`, the compactly induced
  function `x ↦ φ (x⁻¹ H)`, built with the published `compactFunctionOf`. It
  is invariant under left translation by `H`; it is fixed under right
  translation by an open subgroup fixing `φ` under the permutation action
  (chosen from `isSmooth_permutation`); and its support has finite, hence
  compact, image in `H \ G`, the image of the support of `φ` under
  `G ⧸ H ≃ H \ G`. `eval_ofPermutation` states its values.
- `permutationLinearEquiv R M H hH`: `toPermutation` and `ofPermutation` are
  inverse `R`-linear equivalences between `CompactFunctions H (trivial R H M)`
  and `G ⧸ H →₀ M` (both composites are the identity because `x⁻¹⁻¹ = x`;
  the first uses the published `compactFunctions_ext`).
- `permutationEquiv R M H hH`: `permutationLinearEquiv` is an equivalence of
  representations of `G` from `compactInduced H (trivial R H M)` to
  `permutation R G (G ⧸ H) M`. Right translation by `g` on `f` gives
  `y H ↦ f (y⁻¹ g)`, and the permutation action of `g` on
  `toPermutation f` gives `y H ↦ f ((g⁻¹ y)⁻¹) = f (y⁻¹ g)`.
- `smoothPermutation R M H hH`: the permutation representation on
  `G ⧸ H →₀ M` as an object of `SmoothRep R G` (by `isSmooth_permutation`),
  in the universe `max uG uM` of the published `compactInductionFunctor`.
- `compactInductionTrivialIso R M H hH`: the isomorphism in `SmoothRep R G`
  from `(compactInductionFunctor H).obj (Rep.trivial R H M)` to
  `smoothPermutation R M H hH` given by `permutationEquiv`
  (`SmoothRep.mkIso`).

## Naturality in the coefficient module

- `permutationFunctor R H hH : ModuleCat R ⥤ SmoothRep R G`: sends `M` to
  `smoothPermutation R M H hH` and a linear map `f` to `permutationMap f`.
- `compactInductionTrivialNatIso R H hH`: the natural isomorphism from
  `Rep.trivialFunctor R H ⋙ compactInductionFunctor H` (trivial
  representation of `H`, then compact induction to `G`) to
  `permutationFunctor R H hH`, with components
  `compactInductionTrivialIso`. Naturality holds pointwise by definition.

## Normal subgroups and free modules

`H` is a normal subgroup of `G`.

- `ofMulAction_quotient R H`: the representation
  `Representation.ofMulAction R G (G ⧸ H)` on `R[G ⧸ H]` equals Mathlib's left
  regular representation `Representation.leftRegular R (G ⧸ H)` composed with
  the quotient map `QuotientGroup.mk' H : G →* G ⧸ H`.
- `finsupp_ofMulAction_quotient R H I`: the direct sum over `I` of copies of
  `R[G ⧸ H]` equals Mathlib's free representation
  `Representation.free R (G ⧸ H) I` (the free `R[G ⧸ H]`-module of rank `I`)
  composed with the quotient map.
- `compactInducedFreeEquiv R H hH I`: for `H` open and normal, compact
  induction of the trivial representation of `H` on `I →₀ R` is equivalent,
  as a representation of `G`, to the free `R[G ⧸ H]`-module of rank `I`
  pulled back along the quotient map. It is `permutationEquiv` followed by
  `permutationFinsuppEquiv`, with target rewritten by
  `finsupp_ofMulAction_quotient`.

The ring `R` is arbitrary. For `R = 𝒪/ℓ^m𝒪`, `compactInducedFreeEquiv`
describes the free `𝒪/ℓ^m𝒪[G ⧸ H]`-modules of rank `I` as compact inductions
of trivial representations with coefficients in `𝒪/ℓ^m𝒪`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), proof of Proposition 4.10 (Worker 61 read
the rendered scanned pages):

- printed pp.311-312 (one-based PDF pages 13-14): `C^j(ẽ)` "has been chosen
  to be a direct limit of free `𝒪/ℓ^m𝒪[S(ẽ)/H(ẽ)]`-modules as `H(ẽ)` varies
  over a family of open subgroups of `S(ẽ)`";
- printed p.312 (one-based PDF page 14): "Since `C^j_m(ẽ)^{H_p}` and
  `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are both free `𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it
  follows that the maps (4.10.3) are surjective for all m."

The published PowTorsionProjective and PermutationProjective modules treat
surjectivity of maps like (4.10.3) for compact inductions. The first writes
the free module `𝒪/ℓ^m𝒪[S(ẽ)/H_p]` informally as
`c-Ind_{H_p}^{S(ẽ)} 𝒪/ℓ^m`, and the Scope of the second states that it does
not identify compact inductions of trivial representations with permutation
modules or free `R[G/H]`-modules. This module supplies that identification
for an open subgroup `H` of a topological group `G`, and, for `H` also
normal, the free-module form: a free `𝒪/ℓ^m𝒪[G ⧸ H]`-module of rank `I`,
viewed as a representation of `G`, is equivalent to `compactInduced` of the
trivial representation of `H` on `I →₀ 𝒪/ℓ^m𝒪`.

The module is derived: that compact induction of a trivial representation
from an open subgroup is the permutation module on its cosets is standard,
and all definitions and proofs are ours. The passage from `H \ G` to
`G ⧸ H` by inversion is a choice made here so that `G` acts on `G ⧸ H` by
Mathlib's left multiplication.

## Scope

The module does not prove that Harris's modules `C^j(ẽ)`, `C^j_m(ẽ)^{H_p}`
or `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are free, and it does not connect them to the
Library's objects. The quotient by `ℓ^m` is handled by taking the coefficient
ring `R = 𝒪/ℓ^m𝒪`, not by identifying the cokernel of multiplication by
`ℓ^m` on a compact induction over `𝒪`. The result is about the trivial
representation; compact induction of other representations is not described.
Direct limits of free modules are not treated.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
