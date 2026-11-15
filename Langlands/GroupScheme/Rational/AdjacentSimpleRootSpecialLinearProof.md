# Ternary special linear homomorphisms at adjacent simple roots: proof

Module `Langlands.GroupScheme.Rational.AdjacentSimpleRootSpecialLinearProof`.

The main theorem is

```
theorem Langlands.GroupScheme.adjacentSimpleRootSpecialLinear :
    AdjacentSimpleRootSpecialLinearStatement.{u}
```

It proves the Library statement
`Langlands.GroupScheme.AdjacentSimpleRootSpecialLinearStatement`, whose Lean
file and Markdown are unchanged. Here is what the statement says. Take:
- a field `k`;
- a group scheme `G` over `Spec k` with affine structure morphism;
- a split pinning `p` of `G`, with normalized simple-root parametrizations `x`;
- simple roots `a, b` with `⟨a, b^∨⟩ = ⟨b, a^∨⟩ = -1`.

Then some group homomorphism `φ : SL₃(k) →* G(k)` restricts to `rootSL2 x a`
on the upper-left block copy `left` of `SL₂(k)` and to `rootSL2 x b` on the
lower-right block copy `right`.

## Strategy

The group theory is done in two imported internal modules:

- `Langlands.GroupScheme.SpecialLinearTernaryLift` proves
  `TernaryRelations.exists_lift`: two homomorphisms `φ₁ φ₂ : SL₂(F) →* H`
  satisfying nine exact relations extend to `SL₃(F)`.
- `Langlands.GroupScheme.SpecialLinearTernaryWeakRelations` derives those nine
  relations from the 13 weaker conditions of `WeakTernaryRelations φ₁ φ₂`.
  Here commutators are required only up to a point of the third root group,
  and root groups must be separated. The derivation also needs one more
  hypothesis: `φ₁(w) φ₂(w)` conjugates `φ₁(lower t)` to `φ₂(lower t)`.

This module checks those conditions for `φ₁ = rootSL2 x a`, `φ₂ = rootSL2 x b`
and `H = G(k)`, using facts about root subgroups and the torus normalizer
already in the Library.

Notation:
- `upper t`, `lower t`, `diag u` and `w = [0, -1; 1, 0]` are the binary
  matrices, as in the imported modules;
- `cornerPoint φ ψ t = φ(w) ψ(upper (-t)) φ(w)⁻¹`;
- `U_χ` is `RelativeRoot.subgroup p.inclusion χ`, the root subgroup of the
  character `χ`. Its rational points are its carrier at `Over.mk (𝟙 _)`.

All results except the final theorem are in namespace
`Langlands.GroupScheme.SplitPinning`, with implicit `k`, `G` and `p`. The local
instance `adjacentSpecialLinearMono` records that the torus inclusion is a
monomorphism; this comes from maximality of the pinned torus. The option
`backward.isDefEq.respectTransparency false` is set for the whole file.

## Root datum facts (section `RootDatum`)

- `reflection_root_of_pairing_eq_neg_one`: if `⟨b, a^∨⟩ = -1`, then
  `s_a(b) = a + b`.
- `latticePairing_root_coroot`: the integral pairing of the character lattice
  with the cocharacter lattice, on a root and a coroot, is the root datum
  pairing.

## Points of the rank-one homomorphisms (section `Points`)

These restate Library formulas for `rootSL2` from
`OrthogonalOrbitSpecialLinear` and `OrthogonalOrbitCorootWords`:

- `rootSL2_upper_eq_xpPoint` and `rootSL2_upper_eq_rationalPoint`:
  `rootSL2 x a (upper t)` is the point of `U_a` with coordinate `t`.
- `rootSL2_lower_eq_negPoint` and `rootSL2_lower_eq_xmPoint`:
  `rootSL2 x a (lower t)` is the point `(x a).negPoint t` of `U_{-a}`.
- `rootSL2_diag_eq_map`: `rootSL2 x a (diag u)` is the image in `G(k)` of the
  torus point `a^∨(u)`.
- `rootSL2_upper_mem` and `rootSL2_lower_mem`: membership in `U_a` and
  `U_{-a}`.

## Weyl elements (section `Weyl`)

- `rootWeyl x a` is `rootSL2 x a w`, as an element of the torus normalizer
  `normalizerPoints p.inclusion`; the Library lemma `rootSL2_weylMatrix_mem`
  gives membership. `coe_rootWeyl` unfolds it.
- `rootSL2_weylMatrix_inv` writes `(rootSL2 x a w)⁻¹` as
  `negPoint(-1) · unitPoint · negPoint(-1)`.
- `weylAction_rootWeyl`: `rootWeyl x a` acts on characters by the reflection
  `s_a`. Proof: by the uniqueness of opposite factor pairs, the inverse of
  `rootWeyl x a` is the point of the Library's reflection representative of
  `x a`. That representative acts by `s_a` on characters, and `s_a` is an
  involution.
- `cocharacterAut_rootWeyl`: on cocharacters, `rootWeyl x a` acts by the
  coreflection `s_a^∨`. The pairing of characters with cocharacters is
  invariant (`latticePairing_characterAut_cocharacterAut`), the dual of
  `s_a` is `s_a^∨`, and the root datum pairing is perfect.
- `rootSL2_weyl_conj_diag`: if `⟨a, b^∨⟩ = -1`, then
  `ν_a h_b(u) ν_a⁻¹ = h_a(u) h_b(u)`, where `ν_a = rootSL2 x a w` and
  `h_b(u) = rootSL2 x b (diag u)`. The proof conjugates the torus point
  `b^∨(u)` by `rootWeyl x a` (`conj_map_inclusion`), applies
  `cocharacterAut_rootWeyl`, and uses `s_a^∨(b^∨) = a^∨ + b^∨`.

## Torus action (section `Torus`)

If `⟨b, a^∨⟩ = -1`, the torus point `a^∨(u)` acts on `U_b` through the
character `b`, by `u^{⟨b, a^∨⟩} = u⁻¹`
(`conj_xpPoint`, `charEval_torusCocharacterPoint`). Hence:

- `rootSL2_conj_diag_upper`: `h_a(u) x_b(t) h_a(u)⁻¹ = x_b(u⁻¹ t)`;
- `rootSL2_conj_diag_lower`: `h_a(u) y_b(t) h_a(u)⁻¹ = y_b(u t)`.

## The root group of `a + b` (section `Corner`)

Assume `⟨b, a^∨⟩ = -1`.

- `cornerPoint_mem`: `cornerPoint (rootSL2 x a) (rootSL2 x b) t` lies in
  `U_{a+b}`. Conjugation by a normalizer point moves root subgroups according
  to the Weyl action (`RelativeRoot.normalizer_conj_mem`), and `s_a(b) = a + b`.
- `exists_cornerPoint_eq`: every rational point of `U_{a+b}` is such a corner
  point. Conjugate by `(rootWeyl x a)⁻¹` into `U_b`, then use that the
  coordinate of `x b` is surjective on rational points
  (`exists_rationalPoint_eq`).

## Commutation and separation (section `Commutation`)

- `commute_of_mem_root_of_mem_sum`: for adjacent `a ≠ b` with both pairings
  `-1`, rational points of `U_b` and `U_{a+b}` commute. This is the Library
  lemma `commute_of_no_strict_root_combinations`. Its hypothesis holds because
  `n b + m (a + b) = m a + (n + m) b` with `n, m > 0` is never a root
  (`adjacent_root_combination`: a combination `i a + j b` of adjacent simple roots with `i, j > 0` is a root only when `i = j = 1`) and is nonzero
  (`simple_add_ne_zero`).
- `rootSL2_weak_commutator`:
  `x_a(s) x_b(c) x_a(s)⁻¹ = x_b(c) · cornerPoint(f)` for some `f`. By the
  Library lemma `adjacent_commutator_mem`, the commutator lies in `U_{a+b}`.
  Then apply `exists_cornerPoint_eq`.
- `rootSL2_separation`: if `x_b(e)` equals a corner point, then `x_b(e) = 1`.
  The point lies in `U_b`, and `⟨b, -a^∨⟩ = 1 > 0`. It also lies in `U_{a+b}`,
  and `⟨a + b, a^∨⟩ = 1 > 0`. So it lies in the unipotent radical, hence the
  parabolic, of the cocharacter `a^∨` (`RelativeRoot.subgroup_le_dynamicUnipotent`).
  By the Library lemma
  `RelativeRoot.eq_one_of_mem_subgroup_of_mem_negative_parabolic` it is `1`.

## Lower root groups (section `Lower`)

`rootSL2_weyl_mul_weyl_conj_lower` assumes both pairings are `-1` and that
`m = ν_a ν_b` conjugates `x_a(t)` to `x_b(t)` for every `t`. It concludes that
`m` conjugates `y_a(t)` to `y_b(t)`. Proof for `t ≠ 0`:
1. Take `c = -t⁻¹`. The Library gives an opposite factor pair `(y_a(t), y_a(t))`
   of `x_a(c)` (`isOppositeFactorPair_rationalPoint`): both lie in `U_{-a}`,
   and `y_a(t) x_a(c) y_a(t)` normalizes the torus.
2. `m` acts on characters by `s_a s_b` (`weylAction_rootWeyl`), which sends
   `-a` to `-b`.
3. Conjugating by `m` therefore gives an opposite factor pair of `x_b(c)` with
   both entries `m y_a(t) m⁻¹`.
4. The opposite factor pair is unique (`eq_negPoint_of_isOppositeFactorPair`).
   So `m y_a(t) m⁻¹ = y_b(t)`.

## Assembly

`weakTernaryRelations_rootSL2`: for adjacent `a ≠ b` with both pairings `-1`,
`WeakTernaryRelations (rootSL2 x a) (rootSL2 x b)` holds. The fields come from:
- the torus lemmas, for `torus_upper`, `torus_lower` and `torus_upper'`;
- `rootSL2_weyl_conj_diag`, for `weyl_torus`;
- the Library lemma `commute_simple_neg_simple`, for `commute_lower_upper`
  and `commute_lower_upper'`: points of `U_a` and `U_{-b}` commute for distinct
  simple roots;
- `commute_of_mem_root_of_mem_sum`, for the three corner commutations;
- `rootSL2_weak_commutator`, for both weak commutators;
- `rootSL2_separation`, for both separations.

Proof of `adjacentSimpleRootSpecialLinear`:
1. The pairing `⟨a, a^∨⟩ = 2 ≠ -1`, so `a ≠ b`.
2. Hence `weakTernaryRelations_rootSL2` gives `R`.
3. `R.weyl_mul_weyl_conj_upper` says that `ν_a ν_b` conjugates the upper root
   group of `a` to that of `b`. With it, `rootSL2_weyl_mul_weyl_conj_lower`
   gives the lower-root-group hypothesis.
4. Then `R.exists_lift` gives the homomorphism `φ : SL₃(k) →* G(k)`.

The theorem depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

Internal. This is the classical fact that adjacent simple roots of a split
reductive group span a homomorphic image of `SL₃` compatible with the pinning
(the `A₂` case of the Chevalley–Steinberg relations). The proof is implemented
here from Library facts about root subgroups and the torus normalizer. No
literature theorem is used, and no source is cited.
