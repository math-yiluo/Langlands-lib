# Transitivity of normalized induction and Jacquet restriction for represented parabolics

Author: Worker 6. Module `Langlands.Representation.Exponents.LeviParabolicTransitivityStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `LeviParabolicTransitivityStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.1.4, printed pp.136–137 / PDF pp.142–143. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. In translation, the paragraph before the Lemma says: let `P = MN` and `Q = LU` be semi-standard parabolic subgroups of `G` with `P ⊂ Q`; then `L ∩ P = M(L ∩ N)` is a parabolic subgroup of `L`, `N = (N ∩ L)U` and `(L ∩ P)U = MN = P`. The Lemma says: for such `P = MN ⊂ Q = LU`,

`i_P^G = i_Q^G ∘ i_{P∩L}^L` and `r_P^G = r_{L∩P}^L ∘ r_Q^G`.

The proof begins by saying that these equalities of functors are in fact natural isomorphisms. The Lean statement asserts them as such.

This is a **derived** formulation, for three reasons. The functors are the published normalized functors of the represented-parabolic interface. The parabolic `L ∩ P` of `L` is described by explicit data pinned down by its rational points (see "The parabolic of the Levi"). Carrier universes are explicit (see "Universes").

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for that topology. It then quantifies over three actual rational parabolic triples:

- `P = MN` in `G`: a parabolic `p : P ⟶ G` with `hp`, a rational Levi `m : M ⟶ P` with `hm`, and a matching geometric unipotent radical `n : N ⟶ P` with `hn` and `hmul`;
- `Q = LU` in `G`: a parabolic `q : Q ⟶ G` with `hq`, a rational Levi `l : L ⟶ Q` with `hl`, and a matching geometric unipotent radical `uQ : U ⟶ Q` with `huQ` and `hmulQ`;
- `P_L = M N_L` in `L`: a parabolic `pL : PL ⟶ L` with `hpL`, a rational Levi `mL : M ⟶ PL` with `hmL` and the same Levi group scheme `M`, and a matching geometric unipotent radical `nL : NL ⟶ PL` with `hnL` and `hmulL`.

It assumes

1. `pointImage p ≤ pointImage q`, that is `P(F) ⊆ Q(F)` inside `G(F)`;
2. `mL ≫ pL ≫ l ≫ q = m ≫ p`, that is `M` sits in `G` through `P_L ⊂ L ⊂ Q` by the same embedding as through `P`;
3. `pointImage (pL ≫ l ≫ q) = pointImage (l ≫ q) ⊓ pointImage p`, that is `P_L(F) = L(F) ∩ P(F)` inside `G(F)`.

It installs on `rationalPoints L` the affine instance `hl.isConnectedReductive.isAffineHom`, the canonical topology `leviPointTopology l hl`, and the instances `leviPoints_locallyCompactSpace q l hq hl` and `leviPoints_nonarchimedeanGroup q l hq hl`. It installs on `rationalPoints M` the affine instance `hm.isConnectedReductive.isAffineHom` and the canonical topology `leviPointTopology m hm`. It then asserts the conjunction of

- `Nonempty (leviInductionFunctor.{u, v} p m n hp hn hm hmul ≅ leviInductionFunctor.{u, v} pL mL nL hpL hnL hmL hmulL ⋙ leviInductionFunctor.{u, max u v} q l uQ hq huQ hl hmulQ)`;
- `Nonempty (leviJacquetFunctor.{u, v} p m n hp hn hm hmul ≅ leviJacquetFunctor.{u, v} q l uQ hq huQ hl hmulQ ⋙ leviJacquetFunctor.{u, v} pL mL nL hpL hnL hmL hmulL)`.

`F₁ ⋙ F₂` applies `F₁` first, so the two isomorphisms are Renard's `i_P^G ≅ i_Q^G ∘ i_{P∩L}^L` and `r_P^G ≅ r_{L∩P}^L ∘ r_Q^G`. Each is `Nonempty` of an actual natural isomorphism between functors on the full categories of smooth complex representations.

## The parabolic of the Levi

Renard's `L ∩ P` is a parabolic subgroup of `L` with Levi `M` and unipotent radical `L ∩ N`. The interface has no intersection of group schemes, so the statement takes a parabolic `P_L` of `L` with Levi `M` as data and identifies it by hypotheses 2 and 3. Hypothesis 2 says `M` is a Levi of `P_L` with the same embedding in `G`; in particular it forces `M ⊂ L`. Hypothesis 3 says that `P_L` and `L ∩ P` have the same rational points.

These hypotheses determine `P_L` as `L ∩ P`. A parabolic subgroup of a connected reductive group is smooth, connected and unirational over `F` (it is `M ⋉ N` with `M` connected reductive and `N` split unipotent), so its rational points are Zariski dense. Hence `P_L = L ∩ P` as soon as both are parabolics of `L` with the same rational points. The unipotent radical `N_L` of `P_L` is then `L ∩ N`. The same density argument turns hypothesis 1 into `P ⊂ Q`. These arguments explain the hypotheses; they are not part of the statement. The statement quantifies over every such triple, so it covers every nested pair as soon as the parabolic `L ∩ P` is given as actual group-scheme data. Constructing that data is a structural question not addressed here.

The canonical topology `leviPointTopology` on `M(F)` depends only on `M`, so the functors along `P` and along `P_L` use the same topology on `M(F)`.

## Semi-standard pairs

Renard assumes that `P` and `Q` are semi-standard, that is, both contain the fixed maximal split torus `A_0`, and he takes their Levi factors containing `A_0`. Then `M ⊂ L`. The statement instead assumes `P(F) ⊆ Q(F)` and that the given Levi `M` of `P` embeds in the given Levi `L` of `Q` compatibly (hypotheses 1 and 2). Every semi-standard pair satisfies these hypotheses. Conversely, a maximal split torus `S` of `M` is a maximal split torus of `G`: a maximal split torus of `G` containing `S` centralizes the split component of `M`, so it lies in `M`. Since `S ⊂ M ⊂ L`, the pair is semi-standard relative to `S`, with `M` and `L` its Levi factors containing `S`. So the statement covers exactly the semi-standard pairs, relative to any maximal split torus. Again this explains the hypotheses and is not part of the statement.

## The functors

- `leviInductionFunctor p m n …` is the published normalized parabolic induction `i_P^G`. It pulls back along the inverse of `leviPointsEquiv p m hp hm` and applies the published `inductionFunctor` from the Levi image. The twist is the square root of the usual Haar modulus, which is Renard's `δ_P^{-1/2}` in (VI.1.2.1), because Renard's `δ_P` is the inverse of the usual modulus.
- `leviJacquetFunctor p m n …` is the published normalized Jacquet functor `r_P^G`. It takes coinvariants for the radical image `pointImage (n ≫ p)`, twists by the inverse square root of the usual modulus, and pulls back along `leviPointsEquiv p m hp hm`.
- The functors along `P_L` are the same constructions with `L` in place of `G`. They need `L(F)` to be locally compact and a nonarchimedean group for its canonical topology; the statement derives these from the corresponding properties of `G(F)` with the published `leviPoints_locallyCompactSpace` and `leviPoints_nonarchimedeanGroup`, rather than assuming them.

Each functor carries its own normalization, so the statement compares the normalized functors directly. The identity of modulus characters `δ_P = δ_{P∩L} δ_Q` on `M`, which the source proves from the root decomposition on `A_M` and the Cartan decomposition of `M`, is part of the proof obligation and is not assumed.

## Universes

The source does not consider universes. In Lean, `leviInductionFunctor.{u, w}` sends carriers in `Type w` to carriers in `Type (max u w)`, and `leviJacquetFunctor.{u, w}` preserves the carrier universe. For an arbitrary carrier universe `v`, `i_P^G` and `i_{P_L}^L` go from `Type v` to `Type (max u v)`, and `i_Q^G` is taken at `w = max u v`, which it preserves since `max u (max u v) = max u v`. So both sides of the induction isomorphism go from `SmoothRep.{0, u, v} ℂ (rationalPoints M)` to `SmoothRep.{0, u, max u v} ℂ (rationalPoints G)`. All Jacquet functors are taken at `v`, and both sides go from `SmoothRep.{0, u, v} ℂ (rationalPoints G)` to `SmoothRep.{0, u, v} ℂ (rationalPoints M)`. Both isomorphisms are asserted for every carrier universe `v`.

## Faithfulness notes

- No admissibility, finite length or finite type is assumed for any representation.
- The local-compactness and nonarchimedean-group instances of `G(F)` are hypotheses. Those of `L(F)` are derived from them, not assumed.
- The degenerate case `P = Q` is included; then `P_L(F) = L(F)`, so `P_L = L`.
- The dynamic interface has its own version of this Lemma, `DynamicNestedParabolicTransitivityStatement` in `Langlands.Representation.Aubert.General.DynamicNestedParabolicTransitivityStatement`. That statement uses cocharacter parabolics and takes the decompositions `L ∩ P = M(L ∩ N)`, `N = (L ∩ N)U` and `P = (L ∩ P)U` as a visible structural input. The present statement is for actual rational parabolic triples and takes no such input: those decompositions are consequences of the hypotheses and belong to the proof.

## Remaining obligations

The proof is a separate obligation. The source proves the Jacquet isomorphism by commuting the forgetful functors, the coinvariant functors `j_{N∩L}`, `j_U` and the twists, using transitivity of coinvariant functors (Lemma III.2.9), the decompositions above, the triviality of `δ_Q` on `N ∩ L`, and `δ_P = δ_{P∩L} δ_Q` on `M`. It deduces the induction isomorphism by adjunction and uniqueness of adjoints (A.V), with the first adjointness of VI.1.2. On the represented interface that adjointness is the published `LeviFrobeniusReciprocityStatement`, a linear bijection of intertwining spaces `Hom_G(π, i_P^G σ) ≃ Hom_M(r_P^G π, σ)`. The structural facts about `L ∩ P` on rational points must also be established from the hypotheses. None of this is asserted here.

## Provenance

This is a derived statement of the Lemma of VI.1.4 for the represented-parabolic interface. The functors are the published `leviInductionFunctor` and `leviJacquetFunctor`. The parabolic `L ∩ P` of `L` is given by an actual rational parabolic triple with Levi `M`, with the same embedding of `M` in `G`, whose rational points are `L(F) ∩ P(F)`. The equalities of functors are natural isomorphisms, as the source's proof says, on carriers in an arbitrary universe `v` for the representations of `M(F)`.
