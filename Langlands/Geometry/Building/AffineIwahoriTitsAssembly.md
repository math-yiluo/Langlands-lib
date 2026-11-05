# Assembling the actual affine Iwahori–Tits system on `G(F)^0`

This module carries out the proof of Kaletha–Prasad Theorem 7.5.1 directly on
`G(F)^0` for the actual data of `P : ParahoricBuildingData G`. It does not pass
through the simply connected cover. The deep group-theoretic facts that the
source proof cites are collected, unproved, in the Prop structure
`AffineIwahoriTitsInputs`. From these inputs, the apartment axioms and a
comparison `e` realizing the apartment action, the module proves every field
of `P.AffineIwahoriTitsWith C e`.

This module does **not** prove `AffineIwahoriTitsStatement`. The inputs, the
two normalities and the existence of the comparison remain open. Worker 1565
is the author.

## Setting

The Tits datum is the one of `Langlands.Geometry.Building.AffineIwahoriTits`:

- ambient group `G(F)^0 = P.zeroSubgroup`;
- `B = P.parahoricInZero C`, the generated parahoric `P_C` restricted to `G(F)^0`;
- `N = P.normalizerInZero`, i.e. `N(F) ∩ G(F)^0`;
- `W = P.affinePart` with the literal projection `P.affineTitsProjection`;
- `S = P.chamberSimpleInAffinePart e C`, the preimage under `e` of the
  geometric chamber-simple reflections of `C`.

Write `Z(F)^0` for `P.centralizerZero` mapped into `G(F)` by
`rationalPoints.map P.centralizer.j`, `U_ψ` for `P.apartment.affineRootGroup α ψ`
and `U_{ψ+}` for `P.apartment.affineRootGroupPlus α ψ`.

## The inputs (`AffineIwahoriTitsInputs C`)

`AffineIwahoriTitsInputs C` is a structure of eight propositions about `P` and
the chamber `C`. Each is a hypothesis; none is proved here.

1. `parahoric_le_zeroSubgroup`: `P_Ω ⊆ G(F)^0` for every `Ω ⊆ A`.
2. `mem_normalizerZero_of_mem_parahoric`: every `n : normalizerPoints P.i`
   lying in `P_C` lies in `P.normalizerZero`. This is the inclusion
   `I ∩ N ⊆ Z` of KP Lemma 7.5.2(1), from Corollary 7.4.9.
3. `zeroSubgroup_le_sup`: `G(F)^0 ⊆ P_C ⊔ (N(F) ∩ G(F)^0)`. In KP's proof of
   Theorem 7.5.1 this is the step showing that `I` and `N` generate the group.
4. `closure_chamberSimpleReflections`: the geometric chamber-simple
   reflections of `C` generate `W(Ψ)` (KP Proposition 1.3.22(1)).
5. `twoCell`: for every relative root `α` and affine functional `ψ` with
   derivative `rootForm P.i α` and `U_{ψ+} ≠ U_ψ`, the conclusion of
   `AffineRankOneTwoCellStatement` for `P`: a normalizer point `m` in
   `P.affineRankOneSubgroup α ψ`, acting as `affineReflection ψ hv.1` for every
   coroot `v` of `ψ`, with
   `L = U_{-ψ+} Z(F)^0 U_ψ ∪ U_ψ m Z(F)^0 U_ψ` as sets (KP Lemma 7.1.5(3)).
6. `simpleFactorization`: for a chamber-simple root `ψ` of `C` with
   derivative `rootForm P.i α` and any coroot `v` of `ψ`, write `r` for
   `affineReflection ψ hv.1`. Every `b ∈ P_C` is `b' u` with
   `b' ∈ P_{r C}` and `u ∈ U_ψ`. Since `P_{r C} = s P_C s⁻¹`, this is the
   inclusion `s I ⊆ I s U_α` of KP (7.5.1).
7. `rootGroup_inf_parahoricAt_le`: `U_a(F) ∩ P_x ⊆ U_{a,x,0}` for every
   relative root `a` and point `x`. KP's proof of Lemma 7.4.13(1) cites this
   as Proposition 7.3.12.
8. `mem_centralizerZero_of_forall_mem_parahoric`: an element of `G(F)` lying
   in `P_{n C}` for every `n ∈ N(F) ∩ G(F)^0` lies in `Z(F)^0`. KP's proof of
   Theorem 7.5.1 states `⋂_{n ∈ N} n I n⁻¹ = Z`; this is that equality,
   written with `n P_C n⁻¹ = P_{n C}`.

Inputs 2, 3 and 8 quantify over the actual normalizer points of `G(F)^0`.
Input 1 is needed for `B` to be the whole parahoric. The source proof is
written for simply connected `G` and transferred to `G(F)^0` by KP Lemma
7.5.2 and Theorem 7.5.3. Here the source arguments are run on `G(F)^0`
itself, with the source facts restated for `G(F)^0` as above.

## Supporting lemmas

- `AffineRootSystem.pos_of_mem_facetClosure`: if `y` is in the closure of the
  facet of `x` and a root `f` is positive at `y`, then `f` is positive on the
  facet of `x`.
- `AffineRootSystem.exists_mem_facetClosure_of_mem_simpleAffineRoots`: a
  chamber-simple root of `C` vanishes at some point of the closure of `C`.
- `coe_eq_neg_of_rootForm_eq_neg`: if two relative roots have opposite
  apartment forms, they are opposite characters. The lattice pairing of the
  split torus `S` is perfect.
- `exists_neg_relativeRoot`: under the apartment axioms, every relative root
  `α` has a relative root `β = -α` with `rootForm β = -rootForm α`. The
  apartment axioms identify the derivative roots with the forms of the
  relative roots, and `Ψ` is stable under negation.
- `affineRootGroup_le_parahoric`: `U_ψ ⊆ P_Ω` when `ψ` has derivative `α` and
  is non-negative on `Ω`. This combines the published root-fixer inclusions.
- `affineRootGroupPlus_neg_le_parahoric`: for a chamber-simple `ψ` with
  derivative `α`, `U_{-ψ+} ⊆ P_C`. A nontrivial `u ∈ U_{-ψ+}` has an
  extended affine root `f = ψ^u_{-a}` with `f > -ψ` (published
  `mem_affineRootGroupPlus_iff_reflectionFunctional`). At a point `y` of the
  closure of `C` with `ψ y = 0`, `f y > 0`. By AS 4, `f` or `2 f` is in `Ψ`,
  so `f` is positive on `C`, and `u ∈ U_f ⊆ P_C`.
- `conj_mem_parahoric_smul`, `mem_parahoric_smul_iff`: `n P_Ω n⁻¹ ⊆ P_{n Ω}`
  and `g ∈ P_{n Ω} ↔ n⁻¹ g n ∈ P_Ω`, from the published `map_parahoric_conj`.
  These need `[P.normalizerZero.Normal]`, as do all statements about the
  projection below.
- `affineTitsProjection_eq_one_iff`: the projection of `t` is trivial iff `t`
  lies in `Z(F)^0`.
- `normalizerAffineEquiv_eq_of_comparison`, `normalizerPoint_smul_eq`,
  `affineTitsProjection_eq_of_action`: under `P.IsAffineWeylComparison e`, a
  representative `n` acts on `A` by `e (π n)`. A representative acting as
  `e s` projects to `s`.
- `affineRankOneSubgroup_le_zeroSubgroup`: if every `P_Ω` lies in `G(F)^0`,
  then so does `P.affineRankOneSubgroup α ψ`. Its three generators lie in
  `P_{ψ ≥ 0}`, `P_{-ψ ≥ 0}` and `P_∅`.
- `toNormalizerInZero` (definition): an element of `N(F)` lying in `G(F)^0`,
  as an element of `N(F) ∩ G(F)^0`.
- `mem_centralizerZero_of_mem_iInf`: under the inputs, an element of
  `⋂_n n B n⁻¹` lies in `Z(F)^0` (input 8 with the conjugation lemma).

## The Tits axioms

- `affineTitsProjection_surjective`: the projection is surjective. This
  holds without inputs, since `P.affinePart` is the image.
- `ker_affineTitsProjection`: with input 2, `ker π = B ∩ N`. The inclusion
  `Z(F)^0 ⊆ P_C` is published.
- `parahoricInZero_sup_normalizerInZero`: with inputs 1 and 3, `B ⊔ N = ⊤`.
- `closure_chamberSimpleInAffinePart`, `chamberSimpleInAffinePart_mul_self`,
  `chamberSimpleInAffinePart_ne_one`: transport along `e` of input 4 and of
  the published square-one and non-identity facts for chamber-simple
  reflections.
- `exists_simple_data`: an element `s` with `e s` chamber-simple has a
  chamber-simple root `ψ`, a relative root `α` with `ψ.linear = rootForm α`,
  the jump `U_{ψ+} ≠ U_ψ`, and a coroot
  `v` with `e s` equal to `affineReflection ψ hv.1`. The jump holds because
  `ψ ∈ P.affineRoots` means `U_ψ ⊄ U_{ψ+} · U_{2α}(F)`.
- `mul_mem_cell_of_inputs` (the multiplication axiom). This applies the
  published `TitsSystem.forall_mul_mem_cell_of_rankOne` with
  `B' = P_{r C} ∩ G(F)^0`, `U = U_ψ ∩ G(F)^0` and
  `P = {w | ψ ≥ 0 on (e w) C}`. Its five hypotheses are checked as follows.
  - `B ⊆ B' U` is input 6.
  - `n B' n⁻¹ ⊆ B` when `π n = s`, since `n` moves `r C` to `C`.
  - `n U n⁻¹ ⊆ B ∪ B s B`: `n` lies in `L = P.affineRankOneSubgroup α ψ`,
    because `n m⁻¹` projects trivially, so lies in `Z(F)^0 ⊆ L`, and `m ∈ L`
    by input 5. Hence `n u n⁻¹ ∈ L`. By input 5, either
    `n u n⁻¹ ∈ U_{-ψ+} Z(F)^0 U_ψ ⊆ P_C`, using
    `affineRootGroupPlus_neg_le_parahoric`, or
    `n u n⁻¹ ∈ U_ψ m Z(F)^0 U_ψ`, which lies in the cell `B s B`.
  - `m⁻¹ U m ⊆ B` for `w ∈ P` and `π m = w`, since `U_ψ ⊆ P_{(e w) C}`.
  - `w ∈ P` or `s w ∈ P`: the chamber `(e w) C` lies on one side of `ψ = 0`,
    and `r` exchanges the sides.
- `conj_not_le_of_inputs` (the nondegeneracy axiom). Take
  `u ∈ U_ψ ∖ U_{ψ+}`, which exists by the jump. Then `u ∈ B`. If
  `n u n⁻¹ ∈ B`, then `u ∈ P_{n⁻¹ C} = P_{r C}`. For `x ∈ C`, the point
  `y = r x` satisfies `ψ y = -ψ x < 0`, and `u ∈ P_y`. Input 7 gives
  `x_α(u) ≥ 0` at `y`. Since `u ∈ U_ψ ∖ U_{ψ+}`, the published membership
  criteria give `x_α(u) = ψ(y)` at `y`, a contradiction.
- `isSaturated_of_inputs` (saturation). If `g ∈ ⋂_n n B n⁻¹`, then
  `g ∈ Z(F)^0 ⊆ B ∩ N` by `mem_centralizerZero_of_mem_iInf`. Conversely, if
  `g ∈ B ∩ N`, then `π g = 1` by `ker_affineTitsProjection`. Hence
  `π (n⁻¹ g n) = 1`, so `n⁻¹ g n ∈ B` and `g ∈ n B n⁻¹`.

## Assembly

- `affineIwahoriTitsWith_of_inputs hA hC hact h : P.AffineIwahoriTitsWith C e`.
  Assume `[P.normalizerZero.Normal]`, the apartment axioms `hA`, a chamber `C`,
  a comparison `e` with `P.IsAffineWeylComparison e`, and
  `h : P.AffineIwahoriTitsInputs C`. The containment field is input 1. The
  action field is `hact`. The Tits fields and saturation are the theorems
  above.
- `affineIwahoriTits_of_inputs`: the same with the comparison supplied as an
  existence hypothesis, concluding `P.AffineIwahoriTits C`.

The published target `AffineIwahoriTitsStatement` also asserts that
`P.normalizerZero` and `P.zeroSubgroup` are normal. It assumes only the
apartment axioms and the chamber premise. To deduce it from this module one
still needs the two normalities, the existence of the comparison, and a proof
of `AffineIwahoriTitsInputs C` from the apartment axioms.

## Sources

- Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023):
  Theorem 7.5.1 and its proof, and Lemma 7.5.2, printed pp. 259–261
  (PDF pp. 290–292); Lemma 7.1.5(3), printed pp. 243–244 (PDF pp. 274–275);
  Corollary 7.4.9 and the proof of Lemma 7.4.13(1), citing Proposition 7.3.12,
  printed pp. 257–258 (PDF pp. 288–289); Proposition 1.3.22(1).
- Kaletha–Prasad, *Corrections and additions* (1 November 2024),
  PDF pp. 33–35. Saturation is the intersection of the conjugates
  `n I n⁻¹`, as used here.

The projection-surjectivity and projection-kernel membership lemmas are reused from
`AffineIwahoriTitsProjection`; the centralizer-zero subgroup is unchanged.
