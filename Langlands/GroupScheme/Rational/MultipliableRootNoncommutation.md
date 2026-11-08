# Noncommuting points of a multipliable relative root group

Let `G` be a connected reductive group over a field `k`, and let `f ≫ j : S → T → G` be a
maximal split torus whose full centralizer in `G` is the closed torus `j : T → G`. Let `L/k` be
a finite Galois extension splitting `T`, and let `P` be a root datum of `j_L : T_L → G_L`.
Let `a` be a relative root such that `2 • a` is a relative root and no `n • a` with `n ≥ 3` is
a relative root. The main theorem `notCommuteOver` says that the relative root subgroup
`RelativeRoot.subgroup (f ≫ j) a` has two points over `Spec L` (viewed over `Spec k`) that do
not commute. `not_pointsCommute` restates this for a group scheme `U` representing that
subgroup: `¬ RelativeRoot.PointsCommute U`.

Combined with `HeisenbergNormalForm.exists_form_ne_swap`
(`Langlands.GroupScheme.Rational.RootDoubleCommutatorRationalPoints`), this gives the field
`form_nonsymm` of `HeisenbergUnitaryData`.

Provenance: internal. Classically, the relative root group of a multipliable root `a` of a
quasi-split group contains, after splitting, the root subgroups of two absolute roots `β, β'`
restricting to `a` with `β + β'` a root, and these do not commute. The module supplies the
pair `β, β'` from Galois orbit sums and the orbit-partner lemmas of
`Langlands.GroupScheme.Reductive.RootDatumOrbitPartners`. The noncommutation over `L` comes from
`RootPairNoncommutation.exists_not_commute`
(`Langlands.GroupScheme.Reductive.RootPairNoncommutation`). It then moves the points into the
relative root group using Library base-change lemmas.

All declarations live in namespace `Langlands.GroupScheme.MultipliableRootNoncommutation`.
Here `b = algebraBaseMap k L`, and `T_L`, `S_L`, `f_L`, `j_L`, `G_L` are the base changes along
`b`. For a character `a` of `S`, `a_L` is `characterLattice.baseChange b S a`.

## Definition

- `IsObtusePair k L f P a r r'`, for a root datum `P` of characters of `T_L` and a character
  `a` of `S`: the roots `P.root r` and `P.root r'` both restrict to `a_L` on `S_L`
  (`f_L ≫ P.root r = a_L` and `f_L ≫ P.root r' = a_L`), `P.pairing r r' = -1`, and
  `P.root r + P.root r'` is a root of `P`.

## A field element

- `exists_ne_zero_add_ne_zero k L hσ`: if `σ : L ≃ₐ[k] L` is not the identity, some `x : L`
  has `x ≠ 0` and `1 + x ≠ 0`.

  Proof. Pick `x` with `σ x ≠ x`. Since `σ` fixes `0` and `-1`, `x` is neither.

## No higher absolute roots

- `restrict_ne_nsmul k L f j hS hT hhigh hχ hzero n hn`. Let `S` and `T_L` be split. Suppose
  no `n • a` with `n ≥ 3` is a relative root of `f ≫ j` (`hhigh`). Let `χ` be a root of `j_L`
  whose restriction `f_L ≫ χ` is nonzero. Then `f_L ≫ χ ≠ n • a_L` for `n ≥ 3`.

  Proof. Suppose `f_L ≫ χ = n • a_L`; this is nonzero. By
  `weightSpace_comp_eq_iSup_roots`, the weight space of `n • a_L` for `f_L ≫ j_L` is the sum of
  the weight spaces of the roots of `j_L` restricting to `n • a_L`. It contains the nonzero
  weight space of `χ`, so `n • a_L` is a root of `f_L ≫ j_L`, which is the base change of
  `f ≫ j` (`Functor.map_comp`). By `mem_roots_baseChange_iff`, `n • a` is a relative root of
  `f ≫ j`, contradicting `hhigh`.

## The obtuse pair

- `exists_partner k L f j hS hf hT hj hP hzero hred ha h2a`. The hypotheses are: `S` split,
  `f` the largest split subtorus of `T` (`hf`), `T_L` split, `j_L` a closed immersion,
  `P` a root datum of `j_L` indexed by a finite type, no root of `j_L` restricting to `0` on
  `S_L` (`hzero`), and no `P.root r + P.root r` a root (`hred`). If `a` and `2 • a` are
  relative roots of `f ≫ j`, there are `r, r'` with `IsObtusePair k L f P a r r'` and a
  Galois automorphism `σ ≠ 1` carrying `P.root r` to `P.root r'`
  (`characterLattice.galoisRepresentation k L T σ (P.root r) = P.root r'`).

  Proof. Let `ρ` be the Galois action on the root datum
  (`IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus`). Its orbit sums are the Galois
  orbit sums of characters (`IsRootDatumOf.galoisRootIndexEquiv_root`), and they are all
  nonzero (`galoisOrbitSum_ne_zero_of_restrict_ne_zero` with `hzero`). Pick a root `P.root p`
  restricting to `a` and a root `P.root m` restricting to `2 • a`
  (`rootRestrictionFiber_nonempty`). Then `P.root m` and `2 • P.root p` have the same
  restriction, so they have the same Galois orbit sum
  (`IsLargestSplitSubtorus.galoisOrbitSum_eq_of_restrict_eq`). Hence the orbit sum of `m` is
  twice that of `p`. By `exists_root_eq_add_of_orbitSum_eq_two_nsmul`,
  `P.root m = P.root (ρ g • p) + P.root q` for some `g` and some `q` whose orbit sum equals that
  of `ρ g • p`. By `exists_smul_eq_of_rootOrbitSum_eq`, `q = ρ σ • (ρ g • p)` for some `σ`. With
  `hred`, `isOrbitPartner_of_root_eq_add` makes `q` an orbit partner of `r := ρ g • p`, so
  `P.pairing r q = -1` (`IsOrbitPartner.pairing_eq_neg_one`). Galois translates of a root
  restricting to `a` restrict to `a` (`rootsGaloisAction_mem_restrictionFiber`), so `r` and `q`
  both restrict to `a`, and `P.root r + P.root q = P.root m` is a root. The automorphism `σ`
  carries `P.root r` to `P.root q`, and `σ ≠ 1` because `q ≠ r`.

## Noncommutation

- `notCommuteOver k L f j hG hjc hf hcent hT hP ha h2a hhigh`. Here `G` is connected reductive,
  `j` is a closed subgroup, `f ≫ j` is a maximal split torus, `j` represents the torus
  centralizer of `f ≫ j` (`hcent`), `T_L` is split, `P` is a root datum of `j_L` indexed by a
  finite type in universe `u`, and `ha`, `h2a`, `hhigh` are as above. The conclusion is
  `RootPairNoncommutation.NotCommuteOver (subgroup (f ≫ j) a) (subgroup (f ≫ j) a) Z_L`, where
  `Z_L` is `Spec L` viewed over `Spec k` (`(Over.map b).obj (Over.mk (𝟙 (Spec L)))`).

  Proof.
  1. Over `L`: no root of `j_L` restricts to zero (`root_restrict_ne_zero_of_torusCentralizer`).
     `j` is its own torus centralizer, so `j_L` is a maximal torus
     (`isMaximalTorus_baseChange_of_torusCentralizer_eq`). `G_L` is connected reductive
     (`IsConnectedReductive.baseChange_of_algebraicExtension`). The root datum has no root
     `2 β` (`RootPairNoncommutation.hasNoHigherRoots`), which is `hred`.
  2. `exists_partner` gives an obtuse pair `r, r'` and a Galois automorphism `σ ≠ 1`.
  3. `RootPairNoncommutation.strict_combination_not_root`, applied to restriction
     `χ ↦ f_L ≫ χ` and with `restrict_ne_nsmul`, shows that no strict combination
     `n β - m β'` is zero or a root.
  4. `exists_ne_zero_add_ne_zero` gives `x ∈ L` with `x ≠ 0` and `1 + x ≠ 0`. Its image `c` in
     `Γ(Spec L, ⊤)` under `Scheme.ΓSpecIso` is nonzero with `1 + c` a unit. By
     `RootPairNoncommutation.exists_not_commute`, some point of `U_β` and some point of `U_β'`
     over `Spec L` do not commute.
  5. Both points lie in the root subgroup of `f_L ≫ β = a_L` for the torus `f_L ≫ j_L`
     (`RelativeRoot.mem_subgroup_precomp_torus_hom`), which is the base change of `f ≫ j`.
     The multiplicative equivalence `RelativeRoot.subgroupPointsBaseChangeEquiv` carries them
     to points of `subgroup (f ≫ j) a` over `Z_L`, and these still do not commute.

- `not_pointsCommute k L f j hG hjc hf hcent hT hP ha h2a hhigh hU`: under the same hypotheses,
  if `jU : U ⟶ G` represents `subgroup (f ≫ j) a`, then `¬ RelativeRoot.PointsCommute U`.

  Proof. The two noncommuting points of `notCommuteOver` have the form `x₀ ≫ jU` and
  `y₀ ≫ jU`. If `x₀` and `y₀` commuted, so would their images under the homomorphism `jU`.
