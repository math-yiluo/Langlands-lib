# Proof: factorization into elementary Weyl elements (Renard VI.5.4)

`Langlands.GroupScheme.standardWeylElementaryChain` proves the published
proposition `Langlands.GroupScheme.StandardWeylElementaryChainStatement`
(module `Langlands.GroupScheme.Rational.StandardWeylElementaryChainStatement`).
That statement is Renard 2026, VI.5.4, Lemma (printed p. 175, PDF p. 181),
which is Bernstein–Zelevinsky 1977, Lemma 2.17. The universe `u` is kept, and
no hypothesis is added. The statement's Lean/Markdown pair and its imports are
unchanged.

Let `L_I = levi i ν I` be the standard Levi subgroups, `W_G = relativeWeylGroup i`,
and `W_I = standardRelativeWeylGroup i ν (rootSet i ν I)`. As in the statement,
`W(L_I, L_J)` (the `let` `WLM`) is the set of Weyl elements with a lift `n`
satisfying `n L_I n⁻¹ = L_J`. The conclusion says: if `I ≠ univ`, every
`w ∈ W(L_I, L_J)` is a product `w_{m-1} ⋯ w_0` of elementary elements along a
chain of index sets from `I` to `J`.

## Route

The proof follows Bernstein–Zelevinsky's proof 6.5 (registered source
`bernstein-zelevinsky-1977-induced-i`, journal pp. 469–470, PDF pp. 30–31).
All combinatorics take place in the Coxeter system of the relative Weyl group,
in the helper module `Langlands.Group.RelativeWeylElementaryChain` (see its
Markdown). That module proves `hasElementaryChain` for an abstract transport
relation `R` that has three properties:

* `hR1`: `R I J x` implies conjugation by `x` carries `W_I` onto `W_J`;
* `hR2`: an `x` that is positive on the simple reflections of `I` and sends them
  bijectively onto those of `J` satisfies `R I J x`;
* `hR3`: every `x ∈ W_I` satisfies `R I I x`.

This module instantiates `R I J x := x ∈ W(L_I, L_J)` and checks the three
properties. The companion V.4.6 statement is not used.

## Library inputs

* `relativeWeylCoxeter` (`RelativeWeylCoxeterProof`). It gives finiteness of
  `W_G` and of the simple roots, and a Coxeter system `cs` on `W_G` labelled by
  the simple relative roots, with a realization `h`. Two parts of the
  realization are used:
  * `h.2.2.1`: `ℓ x < ℓ(x s_a)` iff `x · a` is a positive relative root;
  * `h.2.2.2.2 I`: `standardSubgroup cs I = W_I`.
* `IsRelativeWeylCoxeterRealization.root_eq_of_conj_simple`
  (`SimpleReflectionConjugacy`): if `x · a` is positive and
  `x s_a x⁻¹ = s_b`, then `x · a = b` on characters.
* `levi_map_conj_of_character_image` (`RationalAssociatedLeviConjugation`),
  with the proved `standardLeviConjugation`: if a normalizer point `n` sends
  `rootSet I` onto `rootSet J` under `weylAction`, then
  `(L_I).map (conj n) = L_J`.
* `mem_standardRelativeWeylGroup_iff` (`StandardParabolic`): `x ∈ W_I` iff `x`
  has a lift in `L_I`. Also `schemeWeylCharacterAction_mk`.
* `parabolic_mono` (`StandardFamilyStructure`), with the proved
  `standardParabolicOrder`: `I ⊆ S` implies `P_I ≤ P_S`.

## Bridge lemmas

* `subgroup_map_conj_eq_self_of_mem`: conjugation by an element of a subgroup
  maps it onto itself.
* `mem_standardRelativeWeylGroup_conj_iff` (gives `hR1`): suppose
  `(L_I).map (conj n) = L_J`, and let `x` be the class of `n`. Then for every
  `g`, `g ∈ W_J ↔ x⁻¹ g x ∈ W_I`. Write `g` as the class of `m ∈ L_J`. Then
  `m = n l n⁻¹` with `l ∈ L_I`, and `n⁻¹ m n = l` is a lift of `x⁻¹ g x`.
  Conversely, a lift `m ∈ L_I` of `x⁻¹ g x` gives the lift `n m n⁻¹ ∈ L_J` of
  `g`.
* `exists_levi_map_conj_self_of_mem` (gives `hR3`): an element of `W_I` has a
  lift `n ∈ L_I`, and conjugation by `n` maps `L_I` onto itself.
* `exists_levi_map_conj_of_simple_bijection` (gives `hR2`): in a realization,
  suppose `ℓ x < ℓ(x s_a)` for all `a ∈ I`, and `a ↦ x s_a x⁻¹` sends the simple
  reflections of `I` into and onto those of `J`. Then `x` has a lift `n` that
  carries `L_I` onto `L_J`. The proof takes an arbitrary lift `n` (by
  `QuotientGroup.mk_surjective`). Positivity turns each `x s_a x⁻¹ = s_b` into
  `x · a = b` (`root_eq_of_conj_simple`), so `weylAction n` maps `rootSet I`
  onto `rootSet J`. Then `levi_map_conj_of_character_image` applies.

## The main theorem

After introducing the data, re-establish the instances `hG.isAffineHom` and
`hi.isSplitSubtorus.mono`, and obtain `cs` and `h` from `relativeWeylCoxeter`.
Use `Fintype.ofFinite` for the simple roots. Then:

1. Set `hWS I := h.2.2.2.2 I`, which identifies `standardSubgroup cs I` with
   the statement's `WS I`.
2. Prove `hR1`, `hR2` and `hR3` from the bridge lemmas, rewriting with `hWS`.
3. Apply `hasElementaryChain cs R hR1 hR2 hR3 WS hWS ha hw`. This gives `m`,
   `Ls`, `ws`, the endpoint equalities and the product formula verbatim.
4. For each step `j`, the Coxeter module gives:
   * `ws j ∈ W(L_{j}, L_{j+1})`;
   * an index set `S` with `Ls j.castSucc ⊆ S`, `Ls j.succ ⊆ S` and
     `ws j ∈ WS S`;
   * the coset count, which is literally the statement's `ell S (Ls j.succ) = 2`.

   The statement's `IsElementary` asks for parabolic inclusions instead of
   index inclusions; `parabolic_mono hG hi hν standardParabolicOrder` turns the
   index inclusions into `P_{Ls j.castSucc} ≤ P_S` and `P_{Ls j.succ} ≤ P_S`.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
