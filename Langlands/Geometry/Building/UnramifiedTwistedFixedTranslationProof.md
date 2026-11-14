# Proof: twisted-fixed translations of the special apartment are split directions

Authors: Worker 2094 and Worker 88.

Lean module: `Langlands.Geometry.Building.UnramifiedTwistedFixedTranslationProof`.

Theorem: `Langlands.Geometry.Building.unramifiedTwistedFixedTranslation :
UnramifiedTwistedFixedTranslationStatement.{u}`. It holds for every universe `u` and in
every characteristic, with no hypotheses beyond those of the statement.

## What is proved

Let `F` be a nonarchimedean local field, `K = inertiaFixedField F` its maximal unramified
extension, `G` a connected reductive `F`-group, and `iS : S → G` a maximal `F`-split torus.
Let `f : S → T` and `iT : T → G` satisfy `f ≫ iT = iS`, and assume that `T_K` is a maximal
`K`-split torus of `G_K`. Let `h ∈ G(K)` commute with the `K`-points of `S`, and let
`n_σ = h⁻¹ σ(h)` lie in the normalizer of `T_K` for every `σ ∈ Aut(K/F)`. If a reduced
translation `v` of the `T_K`-apartment satisfies `n_σ · σ(v) = v` for every `σ`, then `v`
lies in `splitTranslationDirections F K iT f`, the image of `V(S_K)`.

## Relation to Kaletha–Prasad

The statement is a derived formulation of the first paragraph of the proof of
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Proposition 9.3.13, printed
page 338 (PDF page 369). Just before that proposition, KP define `S′`, for a `k`-torus `S`
of `G`, as the maximal subtorus of `S` contained in `G_der`. In the proof, `T` is a special
`k`-torus containing `S`, `V(S′) = ℝ ⊗ X_*(S′)` and `V(T′) = ℝ ⊗ X_*(T′_K)`. KP state
`V(T′)^Γ = V(S′)` because `S′` is the maximal `k`-split torus in `T′`. So `T′` and `S′`
are derived subtori. The corrections (`kaletha-prasad-2024-corrections`, pages 39–40) leave
this paragraph unchanged.

In the Lean setting, KP's special torus corresponds to the full conjugate
`U_K = h T_K h⁻¹`. This proof never passes to its derived part. `U_K` is `Aut(K/F)`-stable
because every `n_σ` normalizes `T_K`, and it contains `S_K` because `h` commutes with `S_K`.
Conjugation by `h` carries the twisted action `λ ↦ σ(λ) · n_σ` on `X_*(T_K)` to the Galois
action on `X_*(U_K)`. For the full tori, the analogue of KP's identity is the unreduced
equality `V(U_K)^Γ = V(S_K)`: `S` is the maximal `F`-split torus in the `F`-torus `U` that
`U_K` defines by Galois descent. This paragraph is explanation only and is not formalized.
The unreduced equality is not KP's `V(T′)^Γ = V(S′)`. For split `G = GL₂` with `S = T`
diagonal and `h = 1`, both `V(U_K)^Γ` and `V(S_K)` have dimension 2, while `V(S′)` has
dimension 1.

The Lean statement and this proof use neither derived subtori nor the unreduced equality.
They work in the reduced translation space `TranslationSpace`, the quotient of `V(T_K)` by
`rootAnnihilator`. The conclusion is membership in `splitTranslationDirections F K iT f`,
the image of `V(S_K)` in that quotient. The published statement Markdown explains why this
quotient image plays the role of KP's `V(S′)`. The proof establishes two inclusions. The
first is the lattice-level form of `V(U_K)^Γ ⊆ V(S_K)`: every twisted-fixed cocharacter of
`T_K` comes from `S_K`. The second, derived from it, is the inclusion of twisted-fixed
reduced translations into `splitTranslationDirections`. The reverse inclusions are not needed
and are not proved here.

## Route

KP derive the fixed-space identity from the fact that `S′` is the maximal `k`-split torus in
`T′`, and they give no further argument. The Lean proof uses the same idea for the full
torus `U_K`. It is presented through `T_K` and the twisted action, and it has two halves. The
second half, averaging over a finite image, is the implemented justification of the passage
from fixed cocharacters to fixed real vectors. It is not a step written out in KP.

1. **Integral half: twisted-fixed cocharacters come from `S_K`.** Let `λ` be a cocharacter of
   `T_K` with `σ(λ) · n_σ = λ` for every `σ`.
   - Conjugating by `h` gives a Galois-invariant cocharacter `λ ≫ i_K ≫ Int(h)` of `G_K`
     (`TwistedFixedTranslation.isInvariant_conj_of_twisted_fixed`, module
     `TwistedFixedTranslationLattice`).
   - It descends to a cocharacter of `G` over `F`, although `K/F` is infinite
     (`InfiniteGaloisCocharacterDescent.descend`, module
     `Langlands.GroupScheme.Absolute.InfiniteGaloisCocharacterDescent`).
   - Since `h` centralizes `S_K` (`TwistedFixedTranslationCentralizer.comp_innerIso_eq_of_commute`),
     the descended cocharacter commutes with `S`. By maximality of `S` it factors through `S`.
     Base change back to `K` and cancelling `Int(h)` and the monomorphism `i_K` give
     `λ = ν ≫ f_K` for a cocharacter `ν` of `S_K`
     (`TwistedFixedTranslationSplitDescent.exists_split_of_twisted_fixed`).
2. **Real half: averaging over a finite image.** The twisted maps `λ ↦ σ(λ) · n_σ` form a group
   action on the cocharacter lattice of `T_K` with finite image. That image is contained in the
   product set of the finite Weyl image and the finite Galois image on a torus split over `K`.
   Averaging over this finite image passes from the integral half to twisted-fixed reduced
   translations
   (`TwistedFixedTranslationAveraging.mem_splitTranslationDirections_of_inv_mul_conjugate`).

Each helper module has its own Markdown with its statements and proofs.

## The proof in this file

After introducing the binders of the statement, the proof

- installs the instances `IsAffineHom G.X.hom` (from `hG.isAffineHom`) and
  `LocallyOfFiniteType G.X.hom` (from `hG.smooth`), and the monomorphism instance for the
  underlying morphism of `i_K` (published `mono_of_isMaximalSplitTorus hiT`), as the statement
  itself does;
- shows that `K` is infinite: `F` is infinite (published
  `LocalField.infinite_of_isNonarchimedeanLocalField`) and `algebraMap F K` is injective;
- obtains the integral input `hfix` from
  `TwistedFixedTranslationSplitDescent.exists_split_of_twisted_fixed`, applied with
  `k = F` and `K = inertiaFixedField F` to `hS`, `hf`, `h`, the centralizer hypothesis `hh`,
  `n` and `hn`. Galois-ness of `K/F` is the published instance `inertiaFixedField_isGalois`;
- concludes with
  `TwistedFixedTranslationAveraging.mem_splitTranslationDirections_of_inv_mul_conjugate iT f hiT h n hn hfix v hv`.

`hfix` is introduced by a separate `have` before the final `exact`. Writing it inline inside
the `exact` makes elaboration exceed the default heartbeat limit.

## Published Library inputs

The proof does not use `UnramifiedTorusUnitFixedApartmentStatement`,
`UnramifiedTorusUnitFixedApartmentReductionStatement`,
`UnramifiedGaloisFixedBuildingPointStatement`, `UnramifiedBuildingDescentStatement`,
`UnramifiedBuildingDescentReductionStatement`,
`UnramifiedBuildingDescentRemainingReductionStatement`, or any theorem that consumes them. None
of the modules defining them is imported, directly or indirectly.

This file uses `IsConnectedReductive.isAffineHom`, `IsConnectedReductive.smooth`,
`mono_of_isMaximalSplitTorus`, `LocalField.infinite_of_isNonarchimedeanLocalField` and the
instance `inertiaFixedField_isGalois`. The main published inputs of the helper modules are:

- Galois descent of cocharacters: `GaloisCocharacterDescent.coordinates_fixed`,
  `faithful_algebraPullback`, `isMonHom_of_faithfulMap`, `baseChangedMorphism_universal`,
  `LaurentGaloisDescent.extend_injective`, and Mathlib's
  `InfiniteGalois.mem_range_algebraMap_iff_fixed`;
- coefficient transport and inner automorphisms: `descent_comp_innerIso_of_eq`,
  `rationalConjugate_eq_baseChange_descent`, `transportCocharacter_naturality`,
  `innerIso_mul_hom`, `comp_innerIso_hom`, `isNormalizingPoint_normalizingAut`;
- centralizers: `TorusDensity.dense_rationalPoints_of_isSplitTorus_baseChange` and
  `hom_ext_of_denseRationalPoints`;
- maximal split tori: `IsMaximalSplitTorus.exists_factor_of_commute`, `isSplitTorus_gm`,
  `IsSplitTorus.baseChange`;
- finiteness and averaging: the finite Weyl image of a split torus
  (`splitTorusWeylImageFinite`), the continuity of the Galois action on cocharacters
  (`torusLatticeGaloisContinuity`), and the identification of the real twisted maps
  with the published `normalizerAction` and `galoisCocharacterAction`.
