# The local split Isomorphism Theorem from Weyl normalization and root relations

This module reduces the target `LocalSplitIsomorphismTheoremStatement` (module
`Langlands.GroupScheme.Reductive.LocalSplitIsomorphismTheoremStatement`) to three
statements that it introduces. The base is an arbitrary commutative local ring,
which may have nilpotents. The three statements are not proved here.

## The three statements

All three concern a commutative local ring `R`, a finite type `I` with decidable
equality and a type `J` in universe `u`. They also concern reductive group schemes
over `Spec R`, with the instance binders `IsAffineHom` for their structure
morphisms, and coordinate split tori `T_I` that are maximal on every residue-field
fibre (`IsFibrewiseMaximalTorus`). Finally, they concern a coordinate root datum
`P : RootDatum J (I → ℤ) (I → ℤ)` that is a fibrewise root datum
(`IsFibrewiseRootDatumOf`), and a base `b` of `P`.

- `LocalSplitSimpleRootGroupLocalStatement` is the published
  `LocalSplitSimpleRootGroupStatement` (module
  `Langlands.GroupScheme.Reductive.LocalSplitReducedIsomorphismReduction`) without its
  hypothesis `[IsReduced R]`. For a reductive `G` with a closed (`IsClosedSubgroup`)
  such torus `i`, a fibrewise root datum `P` and every base `b`, there is
  `u : J → (𝔾ₐ ⟶ G)` with three properties. For every simple root `a`, `u a` is a root
  parametrization of `i` for `P.root a`. Also, `u (-a)` is one for
  `P.root (-a)`, where `-a = P.reflectionPerm a a`. And
  `weylPoint (u a) (u (-a)) = u(-a)(-1) · u(a)(1) · u(-a)(-1)` is a Weyl point of `i`
  acting by the simple reflection `P.reflection a` (`IsWeylPoint`).
- `LocalSplitWeylCommutatorStatement`: let `G` and `H` be reductive, with closed such
  tori `i : T_I → G` and `i' : T_I → H` and one fibrewise root datum `P` for both. Let
  `b` be a base and `W` a choice of simple words (`SimpleWord P b α`) that is
  descending (`IsDescendingWords`, below). Let `u`, `u'` be Weyl-normalized simple-root
  data: for each simple `a`, `u a` is a root parametrization of `i` for `P.root a`,
  `u (-a)` is one for `P.root (-a)`, and `rootWeylPoint P u a` is a Weyl point of `i`
  acting by `P.reflection a`; likewise for `u'`, `i'`. These are exactly the
  conclusions of the first statement. Let `pos : Fin n ≃ {α // b.IsPos α}`
  enumerate the positive roots with `b.height (pos p)` monotone in `p`. Then
  `CommutatorRelations b W u u' pos` holds (module
  `Langlands.GroupScheme.Reductive.LocalSplitCommutatorLaws`). That is, over every local
  test ring `A` with separably closed residue field and for all positions `k < l`,
  each expression of the commutator
  `(u_W(pos k)(x) · u_W(pos l)(y))⁻¹ · (u_W(pos l)(y) · u_W(pos k)(x))` as a product
  `∏_q u_W(pos q)(e q)` of the positive cell factors of the Weyl family
  `u_W = weylFamily P W u` of `G` holds with the same `e` for the Weyl family of `H`.
- `LocalSplitWeylNegSimpleStatement`: the same data (closed tori, descending words,
  Weyl-normalized simple-root data and `pos`), together with an enumeration
  `neg : Fin m ≃ {α // ¬ b.IsPos α}` of the non-positive roots. The conclusion is
  `NegSimpleRelations` (module
  `Langlands.GroupScheme.Reductive.LocalSplitSimpleGeneratorRelations`) for the big-cell
  maps of the two Weyl families. Over every local test ring with separably closed
  residue field and for every simple root `a`, if `Ω(x) · u_{-a}(-1) = Ω(y)` holds
  between cell points of `G`, then `Ω'(x) · u'_{-a}(-1) = Ω'(y)` holds in `H`.

## Statement

`LocalSplitWeylRelationsReductionStatement.{u}` says that the three statements
together imply `LocalSplitIsomorphismTheoremStatement.{u}`. The module proves it as
`localSplitWeylRelationsReduction`, through the theorem
`localSplitIsomorphismTheorem_of_weylRelations`.

The namespace `LocalSplitCell` also contains:

- `exists_equiv_monotone`: a finite type has an enumeration by `Fin (card α)` along
  which a given integer-valued function is monotone;
- `IsDescendingWords P b W`: a choice `W` of simple words built by descending height.
  It has three conditions. (1) For a simple root `a`, `W a` has simple root `a` and the
  empty word. (2) For a positive non-simple root `α`, there is a simple root `c` with
  `0 < P.pairing α c`, that is `0 < ⟨α, c^∨⟩`, such that `W α` has the simple root of
  `W (s_c α)` and the word `c :: (W (s_c α)).word`. Here `s_c α` is the root with index
  `P.reflectionPerm c α`, whose height is `b.height α - ⟨α, c^∨⟩`. (3) For a non-positive
  root `α`, `W α` has the simple root `s` of `W (-α)` and the word
  `(W (-α)).word ++ [s]`, where `-α` has index `P.reflectionPerm α α`. With
  `wordConj`, the Weyl family is then `u_W(a) = u_a` at simple roots,
  `u_W(α) = Ad(N_c) ∘ u_W(s_c α)` at positive non-simple roots, and
  `u_W(α) = (Ad(N_s) ∘ u_s)` conjugated along the word of `-α` at non-positive roots;
- `descMeasure`, `height_reflectionPerm_of_mem`, `descMeasure_lt_of_not_pos`,
  `exists_mem_support_pos_pairing` and `descMeasure_lt_of_pos`: the recursion measure
  (twice the height of a positive root, one more than twice the absolute height of a
  non-positive root) and the facts that make it decrease;
- `descWord P b` and `isDescendingWords_descWord`: descending words exist when `J` is
  finite and `P` is reduced;
- `nonempty_iso_of_commonTorus_local`: the conclusion `Nonempty (G ≅ H)` for groups
  with closed tori on the same `I` and the same fibrewise root datum, from the three
  statements.

## Proof

**Common torus.** Given the data of the target, with tori `i : T_I → G`,
`i' : T_{I'} → H` and an equivalence `e : RootPairing.Equiv P Q`, compose `i'` with the
torus isomorphism `T_I ≅ T_{I'}` of the weight equivalence (imported
`precompTorus e.weightEquiv`). The imported lemmas `isClosedSubgroup_precompTorus`,
`isFibrewiseMaximalTorus_precompTorus` and `isFibrewiseRootDatumOf_precompTorus` make
`H` a group with a closed fibrewise maximal torus on `I` and fibrewise root datum
`P`. This is the same transport as in the published reduced case
(`localSplitReducedIsomorphismTheorem_of_rootGroups`).

**Common-torus case.** The root datum `P` is finite and reduced (fields `finite` and
`isReduced` of `IsFibrewiseRootDatumOf`), so it has a base `b` (imported
`RootDatumBase.nonempty_base`). The first statement gives Weyl-normalized simple-root
data `u` for `G` and `u'` for `H`. The words are `W = descWord P b`, which are
descending, in particular empty at the simple roots. The
enumeration `neg` comes from Mathlib's `Finite.equivFin`. The enumeration `pos` is
monotone in height, by `exists_equiv_monotone`. That lemma orders the finite type
lexicographically by the pair (height, index) through `LinearOrder.lift'`, then
uses Mathlib's `Fintype.orderIsoFinOfCardEq`. With these choices, the second and
third statements give the hypotheses of the imported
`localSplitCommutatorLawIsomorphism`, which yields `ψ : G ≅ H`.

**Descending words.** `descWord P b α` is defined by well-founded recursion on
`descMeasure P b α`. A simple root gets the empty word. For a positive non-simple root,
Mathlib's `IsPos.exists_mem_support_pos_pairingIn` and
`RootPairing.zero_lt_pairingIn_iff'` give a simple `c` with `0 < ⟨α, c^∨⟩`
(`exists_mem_support_pos_pairing`), and `descWord` takes a chosen one. The root `s_c α`
is positive by Mathlib's `IsPos.reflectionPerm` and has height
`b.height α - ⟨α, c^∨⟩` (`height_reflectionPerm_of_mem`, from `height_add_zsmul`), so
the measure drops. A further branch, used only if no such `c` existed, takes any simple
word from the imported `nonempty_simpleWord`. For a non-positive root `α`, the root
`-α` is positive with height `-b.height α` (Mathlib's `height_reflectionPerm_self` and
`height_ne_zero`), so the measure drops from `2 |h| + 1` to `2 |h|`. The equations
`root_eq` follow from `reflection_same`, `reflection_apply_self` and the imported
`wordReflect_neg`. `isDescendingWords_descWord` unfolds the definition once in each
case.

## Provenance and scope

The target is the Isomorphism Theorem of B. Conrad, *Reductive group schemes*, in
*Autour des schémas en groupes*, Panoramas et Synthèses 42–43, 2014, Theorem 6.1.17,
over a local base. The division into Weyl normalization (Corollary 5.1.9 there),
commutation relations of positive root groups (Proposition 5.1.14 and Lemma 6.2.8)
and rank-one relations follows the structure of that proof and of SGA 3, Exp. XXIII.
The statements and the reduction are internal to this formalization. The first
statement corresponds to the existence of root groups and of normalized opposite
root groups over a general base (Conrad, Theorem 4.1.4 and Corollary 5.1.9). The
second and third follow from the Isomorphism Theorem for pinned split reductive
groups. All three remain open in the Library, and this module does not prove the
target without them. The descending words follow the construction by increasing height
in the proof that the Weyl group is presented by the simple reflections (SGA 3,
Exp. XXI, Lemme 5.2). The second and third statements assume descending words because
the planned proof of the commutator relations uses induction on height. That proof
does not need the full lemma of Tits (SGA 3, Exp. XXI, 5.6) for arbitrary words.
