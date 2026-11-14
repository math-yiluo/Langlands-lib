# Twisted-fixed cocharacters come from the maximal split torus

Authors: Worker 88, with Worker 2094 (route; fix in `commute_conj_values`).

Lean module: `Langlands.Geometry.Building.TwistedFixedTranslationSplitDescent`.

This module is a helper for the proof of `UnramifiedTwistedFixedTranslationStatement`
(Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Proposition 9.3.13, first
paragraph of the proof, printed page 338). That paragraph states `V(T')^Γ = V(S')` because the
maximal `F`-split torus of `T'` is `S'`. There `T'` and `S'` are the maximal subtori of `T` and
`S` contained in the derived group `G_der` (KP's notation, defined just before 9.3.13).

The module proves an integral fact about the full tori, not their derived parts, which the
proof needs. A cocharacter `λ` of `T_K` that is fixed by the twisted action
`λ ↦ σ(λ) · n_σ` comes from a cocharacter of `S_K`. Through conjugation by `h` this is the
lattice-level form of the inclusion `V(h T_K h⁻¹)^Γ ⊆ V(S_K)`.
The argument has three steps:

1. Conjugation by `h` makes `λ` a Galois-invariant cocharacter of `G_K`.
2. That cocharacter descends to a cocharacter of `G` over `k` that commutes with `S`.
3. By maximality of `S`, the descended cocharacter factors through `S`.

This reformulation is internal to the project and is not a numbered result of KP.

## Setting

`k` and `K` are fields in the same universe, with `K` a `k`-algebra, and `b = algebraBaseMap k K`.
`S` and `T` are commutative group schemes over `Spec k`, and `G` is a group scheme over `Spec k`.
The maps are:

- `iS : S → G`, `iT : T → G` and `f : S → T`;
- base changes `iS_K`, `i_K : T_K → G_K` and `f_K : S_K → T_K`;
- `Int(h)`, the inner automorphism `(G_K).innerIso h` of `G_K` for `h ∈ G(K)`.

## Statements

- `baseChange_iS_eq`: if `f ≫ iT = iS` (with `f` read as a group homomorphism), then
  `iS_K = f_K ≫ i_K`.
- `commute_conj_values`. Assume `f ≫ iT = iS` and `iS_K ≫ Int(h) = iS_K`. Let `λ` be a
  cocharacter of `T_K`, `U` a scheme over `Spec K`, `x : U → Gm_K` and `y : U → S_K`. Then the
  `U`-points `x ≫ (λ ≫ i_K ≫ Int(h))` and `y ≫ iS_K` of `G_K` commute.
- `commute_descend_values`. Assume moreover that `K/k` is Galois, that `G` is affine over
  `Spec k`, and that `λ ≫ i_K ≫ Int(h)` satisfies `GaloisCocharacterDescent.IsInvariant`.
  Let `U` be a scheme over `Spec k`, `x : U → Gm_k` and `y : U → S`. Then
  `x ≫ InfiniteGaloisCocharacterDescent.descend (λ ≫ i_K ≫ Int(h))` and `y ≫ iS` commute in
  `G(U)`.
- `exists_split_of_twisted_fixed`. The hypotheses are:
  - `K/k` is Galois, `K` is infinite, and `G` is affine over `Spec k`;
  - the underlying scheme morphism of `i_K` is a monomorphism;
  - `iS` is a maximal split torus of `G` (`IsMaximalSplitTorus iS`), and `f ≫ iT = iS`;
  - `h ∈ G(K)` commutes with the image in `G(K)` of every `K`-point of `S`;
  - `n` is a family of normalizer points of `i_K` with `n σ = h⁻¹ · σ(h)` for every
    `σ ∈ Aut(K/k)`;
  - `λ` is a cocharacter of `T_K` with
    `cocharacterLattice.galoisRepresentation k K T σ λ ≫ (normalizingAut i_K (n σ)).hom = λ`
    for every `σ`.

  Then there is a cocharacter `ν` of `S_K` with `ν ≫ f_K = λ`.

  The hypotheses on `h` and `n` are stated as in `UnramifiedTwistedFixedTranslationStatement`.
  The hypothesis on `λ` and the conclusion have the shape of the hypothesis `hfix` of
  `TwistedFixedTranslationAveraging.mem_splitTranslationDirections_of_inv_mul_conjugate`.

## Proof

- `baseChange_iS_eq`: base change is a functor, so it preserves the composite `f ≫ iT`.
- `commute_conj_values`: by `hA` and `baseChange_iS_eq`, `iS_K = f_K ≫ i_K ≫ Int(h)`. So both
  points are images under the group homomorphism `i_K ≫ Int(h)` of the `U`-points `x ≫ λ` and
  `y ≫ f_K` of the commutative group scheme `T_K`. These commute, and so do their images,
  since postcomposition with a group homomorphism is multiplicative (`MonObj.mul_comp`).
- `commute_descend_values`: pullback along `Spec K → Spec k` is faithful (published
  `GaloisCocharacterDescent.faithful_algebraPullback`) and preserves products of points
  (`Functor.map_mul`). So it suffices to compare the pullbacks of the two products.
  - The pullback of the first point is the pullback of `x`, followed by `Gm.baseChangeIso`
    and by `λ ≫ i_K ≫ Int(h)`. This is `InfiniteGaloisCocharacterDescent.baseChange_descend`.
  - The pullback of the second point is the pullback of `y` followed by `iS_K`.

  These commute by `commute_conj_values`.
- `exists_split_of_twisted_fixed`:
  1. `TwistedFixedTranslation.isInvariant_conj_of_twisted_fixed` shows that
     `λ ≫ i_K ≫ Int(h)` is Galois-invariant.
  2. `S_K` is a split torus (`IsSplitTorus.baseChange`). So
     `TwistedFixedTranslationCentralizer.comp_innerIso_eq_of_commute` gives
     `iS_K ≫ Int(h) = iS_K`. This uses that `K` is infinite and that `G` is separated, which
     holds because `G` is affine.
  3. Let `d = InfiniteGaloisCocharacterDescent.descend (λ ≫ i_K ≫ Int(h)) : Gm_k → G`. By
     `commute_descend_values`, `d` commutes with `iS` on all test points. The published
     `IsMaximalSplitTorus.exists_factor_of_commute`, applied to the split torus `Gm_k`
     (`isSplitTorus_gm`), gives `ν_k : Gm_k → S` with `ν_k ≫ iS = d`.
  4. Take `ν = (Gm.baseChangeIso b).inv ≫ (ν_k)_K`, a cocharacter of `S_K`. Then
     `ν ≫ f_K ≫ i_K ≫ Int(h) = ν ≫ iS_K ≫ Int(h) = ν ≫ iS_K`, which is the base change of `d`
     precomposed with `(Gm.baseChangeIso b).inv`. This is `λ ≫ i_K ≫ Int(h)` by
     `baseChange_descend`.
  5. Cancel the isomorphism `Int(h)`, then the monomorphism `i_K`: the underlying morphism of
     `i_K` in `Over (Spec K)` is mono by `Over.mono_of_mono_left`. This gives `ν ≫ f_K = λ`.
