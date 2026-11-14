# The rank-one homomorphism from binary SL of a linked root parametrization

Module `Langlands.GroupScheme.Reductive.LinkedRootSpecialLinearHom`, namespace
`Langlands.GroupScheme.LinkedRootParametrization`.

Let `k` be any field, finite or infinite. Let `G` be a group scheme over `Spec k` whose
structure morphism is affine (`IsAffineHom G.X.hom`). Let `i : T ⟶ G` be a map from a
commutative group scheme, `α` a character and `ν` a cocharacter of `T`. Let
`X : LinkedRootParametrization i α ν` be a linked parametrization of the root groups of
`±α` (module `Reductive.LinkedRootParametrization`). Its fields used here are:

- `positive_equivariant` and `negative_equivariant`, the torus conjugation laws of
  weights `α` and `-α` over every test scheme;
- `relation`, the rank-one relation over every test scheme.

Assume `⟨α, ν⟩ = 2` (hypothesis `h2`). The module builds a group homomorphism
`SL₂(k) → G(k)` that sends `upper t`, `lower t` and `diag v` to `x₊(t)`, `x₋(t)` and
`ν(v)`. Here `x₊(t) = X.xpPoint t`, `x₋(t) = X.xmPoint t` and `ν(v) = cocharacterPoint i ν v`
are the rational points of module `Reductive.LinkedRootRationalRelation`.

The construction uses the big-cell presentation of module
`GroupScheme.SpecialLinearBinaryPresentation`. That presentation gives a lift
directly only over fields with at least three elements. To cover every field, the
relations are first established over an algebraic closure `E` of `k`, in the group of
`E`-points, and then descended along the injective map `G(k) → G(E)`.

## Over an arbitrary test scheme

Fix a test scheme `Z` over `Spec k`.

- `cocharacterPointAt Z i ν : Γ(Z, ⊤)ˣ →* (Z ⟶ G.X)` sends a unit `u` of the global
  sections to the point `ν(u)` of `T` followed by `i`. It is the version of
  `cocharacterPoint` over `Z`. `cocharacterPointAt_apply` unfolds it.
- `cu_cocharacterAt u`: on the point `ν(u)`, the character `α` takes the unit value
  `u ^ ⟨α, ν⟩`. The proof is the one of `cu_cocharacter`: it writes `ν ≫ α` as
  `⟨α, ν⟩ • 𝟙` with `eq_gmEndEquiv_zsmul` and `latticePairing_apply`, then applies
  `comp_groupHom_zsmul`.
- `cocharacterPointAt_conj_positive h2 u c`:
  `ν(u) x₊(c) ν(u)⁻¹ = x₊(u² c)` for points over `Z`. This is
  `X.positive_equivariant` at the point `ν(u)`, with the character value from
  `cu_cocharacterAt`.
- `cocharacterPointAt_conj_negative h2 u c`:
  `ν(u) x₋(c) ν(u)⁻¹ = x₋(u⁻² c)`. This is `X.negative_equivariant`, with `cu_neg`.
- `bigCellRelationsAt Z h2 E σ`, for a field `E` and a ring map
  `σ : E →+* Γ(Z, ⊤)`, is a `BigCellRelations E (Z ⟶ G.X)`. Its maps are
  `x c = gpt (σ c) ≫ X.positive`, `y c = gpt (σ c) ≫ X.negative` and
  `h v = cocharacterPointAt Z i ν (σ v)`. Additivity comes from `gpt_add`. The torus laws
  are the two conjugation lemmas above. The big-cell relation is the field `X.relation`
  at `Z`, applied to the points with coordinates `σ a`, `σ b`, `σ (u⁻¹ a)` and
  `σ (u⁻¹ b)`. The `simp` lemmas `bigCellRelationsAt_x`, `_y` and `_h` unfold the
  three maps.

## Over the field `k`

- `bigCellRelations h2 : BigCellRelations k (rationalPoints G)` is
  `bigCellRelationsAt` at the identity test scheme with `σ = secMap k`.
  `bigCellRelations_x`, `_y` and `_h` state that its maps are exactly `X.xpPoint`,
  `X.xmPoint` and `cocharacterPoint i ν`. All three hold by `rfl`.

## Over a field extension

For a field extension `E` of `k`:

- `extensionTest k E` is the test scheme `Spec E → Spec k`, with structure map the
  Library's `GaloisPointComparison.baseMap k E`.
- `extensionMap k E` is its map to the identity test scheme.
- `extensionPoints k E : rationalPoints G →* (extensionTest k E ⟶ G.X)` is
  precomposition with `extensionMap k E`. It is a homomorphism by `MonObj.comp_one` and
  `MonObj.comp_mul`; `extensionPoints_apply` unfolds it.
- `extensionPoints_injective`: this map is injective. The proof identifies the
  underlying scheme map of `extensionPoints k E x` with that of the Library's
  `GaloisPoint.extend k E G` applied to `rationalCoeffEquiv k G x`. Both are
  `baseMap k E ≫ x.left`. Then it uses `GaloisPoint.extend_injective`. That result
  needs `IsAffine G.X.left`, which follows from `IsAffineHom G.X.hom` by Mathlib's
  `isAffine_of_isAffineHom`.
- `extensionSecMap k E : E →+* Γ(Spec E, ⊤)` is the inverse of `Scheme.ΓSpecIso`.
- `extensionMap_appTop_secMap c`: pulling back the global section `secMap k c` along
  `extensionMap k E` gives `extensionSecMap k E (c)`, with `c` viewed in `E`. This is
  Mathlib's `Scheme.ΓSpecIso_inv_naturality`.

## The homomorphism

- `exists_specialLinearHom h2`: there is a homomorphism
  `φ : SL₂(k) →* rationalPoints G` with `φ (upper t) = X.xpPoint t`,
  `φ (lower t) = X.xmPoint t` and `φ (diag v) = cocharacterPoint i ν v` for all `t`
  and all units `v`.

  Proof. Take `E = AlgebraicClosure k`, which is infinite, so the condition of
  `exists_ne_ne_of_infinite` holds for `E`. Apply `exists_hom_of_embedding` of module
  `SpecialLinearBinaryPresentation`. Its inputs are the relations
  `bigCellRelationsAt (extensionTest k E) h2 E (extensionSecMap k E)`, the field map
  `algebraMap k E`, and the injective homomorphism `extensionPoints k E`. The three
  compatibilities say that `extensionPoints` sends `x₊(t)`, `x₋(t)` and `ν(v)` to the
  values of those relations at `t` and `v` viewed in `E`. The first two follow from
  `comp_gpt` and `extensionMap_appTop_secMap`. The third follows from the Library's
  `RootCell.symm_pointsEquiv_comp` and the same lemma.
- `specialLinearHom h2` is a chosen such homomorphism. Its values are given by
  `specialLinearHom_upper`, `specialLinearHom_lower` and `specialLinearHom_diag`.
- `specialLinearHom_weylMatrix`: the Library's Weyl matrix
  `SpecialLinear.BinaryUpper.weylMatrix` (the matrix `[0, -1; 1, 0]`) goes to
  `x₊(-1) x₋(1) x₊(-1)`, by `weylMatrix_eq`.
- `eq_specialLinearHom`: every homomorphism `SL₂(k) →* rationalPoints G` that agrees
  with `x₊` on the upper and with `x₋` on the lower unipotent matrices equals
  `specialLinearHom h2`, by `hom_ext`.

## Provenance

This is internal glue between the Library's linked root parametrizations and the
big-cell presentation of binary `SL` in `SpecialLinearBinaryPresentation`. Every step
is proved in Lean; no literature result is assumed. The existence of a homomorphism
from `SL₂` attached to a root, with these values on the root groups and the torus, is
standard in the theory of reductive groups. Here it is proved directly from the rank-one
relation recorded in `LinkedRootParametrization`, on rational points only. The
homomorphism is not claimed to come from a morphism of group schemes.
