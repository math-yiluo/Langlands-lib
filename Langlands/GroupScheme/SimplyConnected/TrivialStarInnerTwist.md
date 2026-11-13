# Pinned base-change isomorphisms onto groups with trivial star action are inner twists

This helper module, namespace `Langlands.GroupScheme.TrivialStarInnerTwist`, proves that
a pinned isomorphism between two groups over a finite Galois extension has inner
discrepancy when the second group has trivial star action. It serves the reduction in
`Langlands.GroupScheme.SimplyConnected.InnerTypeANormOneReduction`. All results are at
universe parameter `u`. The main theorem uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Setting

`k` and `L` are fields in `Type u` with `L` a `k`-algebra that is algebraic over `k`.
`M` and `G` are group schemes over `Spec k` with affine structure morphisms. The data are:

- `pM : SplitPinning M`, a split pinning of `M` over `k`;
- `d : GaloisPinningData k L G`, Galois pinning data of `G` over `L`. This is a split
  pinning of `G_L` whose torus is the base change of a `k`-torus `d.torus`, together
  with the Galois action and star action of `Aut_k(L)` on its root datum;
- `E : SplitPinning.Iso (pM.baseChange (F := L)) d.toSplitPinning`, a pinned
  isomorphism from the base change of `pM` to `L` onto the pinning of `G_L`. It consists
  of a group isomorphism `E.groupIso : M_L ≅ G_L` and a torus isomorphism `E.torusIso`
  with `E.square`: the torus inclusions intertwine them.

## Results

- `galoisRepresentation_of_isSplitTorus`: if `T` is a split `k`-torus, the Galois
  action of `σ ∈ Aut_k(L)` on the characters of `T_L` is trivial. Every character of
  `T_L` is the base change of a character of `T` (`characterLattice.baseChangeEquiv`),
  and base-changed characters are fixed (`characterLattice.galoisRepresentation_baseChange`).
- `torusIso`: `E.torusIso`, with its domain written as the base change of the `k`-torus
  of `pM`.
- `twistIso σ`: the automorphism `σ^*E ∘ E⁻¹` of `G_L`, that is,
  `E.groupIso.symm ≪≫ Descent.pullIso (galoisBaseMap k L σ) … E.groupIso`.
- `twistTorusIso σ`: the corresponding automorphism of the torus `T'_L` of `d`. It is the
  composite of `torusIso⁻¹`, the inverse descent comparison
  `CommGroupScheme.descentBaseChangeIso` for the torus of `pM`, the `σ`-pullback of
  `torusIso`, and the descent comparison for `d.torus`.
- `inclusion_comp_twistIso`: the torus inclusion of `d` intertwines `twistTorusIso σ`
  with `twistIso σ`. The proof unfolds both automorphisms into composites of `E`, its
  `σ`-pullback and the descent comparison isomorphisms. It then rewrites with
  `E.square` (and its inverse form), and with naturality of the descent comparison
  (`descentBaseChangeIso_naturality`) for the torus inclusions of `pM` and `d`.
- `characterAut_twistTorusIso_apply`: on characters of `T'_L`, the torus twist acts as
  the ordinary Galois action `characterLattice.galoisRepresentation k L d.torus σ`. The
  proof unfolds both sides into compositions of characters with the descent comparison
  isomorphisms and the `σ`-pullback. The `pM`-torus contributions cancel because the
  Galois action on the characters of the base-changed split torus of `pM` is trivial
  (first result).
- `characterAut_twistTorusIso_mem_weylImage`: if `d.starAction σ = 1`, the character
  automorphism of `twistTorusIso σ` lies in the actual Weyl image `weylImage` of the
  pinned torus of `G_L`. By `GaloisPinningData.starAction_eq_one_iff`, trivial star
  action means that `d.galoisAction σ` lies in the abstract Weyl group of the root datum.
  `IsRootDatumOf.abstractWeylImage_le` puts this abstract Weyl element in the actual Weyl
  image, and by the previous result its weight map is the character automorphism of the
  torus twist.
- `hasInnerDiscrepancy` (main theorem). Assume also that `L/k` is finite Galois, that
  `G` is locally of finite type, and that `d.starAction σ = 1` for every
  `σ ∈ Aut_k(L)`. Then for every actual adjoint quotient `q : M ⟶ A`
  (`IsAdjointQuotient q`), the local group isomorphism
  `LocalGroupIso.ofBaseChangeIso E.groupIso` (over the ring test of `L`) has all-test
  inner discrepancy with respect to `hq.innerAction`.

## Proof of the main theorem

1. Choose an adjoint quotient `q' : G_L ⟶ A'` with `adjointQuotientExistence`. It
   applies because `G_L` is connected reductive (`d.isConnectedReductive`).
2. `IsAdjointQuotient.hasInnerDiscrepancy_of_galois_baseChange` reduces the claim to
   the following. For each `σ ∈ Aut_k(L)`, the automorphism `σ^*E ∘ E⁻¹`, computed on
   the model side, is conjugation by an `L`-point of the base change of `A`.
3. For a fixed `σ`, `SplitPinning.exists_adjointPoint_of_weylImage` applied to
   `twistIso σ`, `twistTorusIso σ`, `inclusion_comp_twistIso` and
   `characterAut_twistTorusIso_mem_weylImage` gives an `L`-point `y` of `A'` whose
   inner action is `twistIso σ`. The torus inclusion is a closed immersion
   (`d.isMaximalTorus`).
4. The base change `q_L` of `q` is an adjoint quotient of `M_L`
   (`adjointQuotientBaseChangeStatement.isAdjointQuotient`). The isomorphism
   `E.groupIso` induces an isomorphism `Φ` of adjoint quotients (`IsAdjointQuotient.mapIso`).
   The point `y ≫ Φ⁻¹` is the required point of `A_L`. Its inner action is computed with
   `IsAdjointQuotient.basePointIso_trans`, which transports inner actions along `Φ`.

## Context

Mathematically this is the standard fact that a group whose star action is trivial is an
inner form of its quasi-split model (Tits 1966, §2.3, printed p.39). The Galois twist
of a pinned isomorphism normalizes the torus and acts on characters through the Weyl
group, so it is inner. The Lean proof above is a direct verification for the finite
Galois stage `L`.
