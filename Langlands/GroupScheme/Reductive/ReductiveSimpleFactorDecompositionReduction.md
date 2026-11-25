# The reductive simple-factor decomposition from the semisimple one

This module proves that Conrad's decomposition theorem for semisimple groups
(Theorem 5.1.19) implies its reductive version (Exercise 5.5.2), both over a field.
It does not prove either statement. It adds no axioms. The theorem uses only `propext`,
`Classical.choice` and `Quot.sound`.

## Statement

```lean
def ReductiveSimpleFactorDecompositionReductionStatement : Prop :=
  SimpleFactorDecompositionStatement.{u} → ReductiveSimpleFactorDecompositionStatement.{u}
```

- `SimpleFactorDecompositionStatement.{u}` (module
  [`Reductive.SimpleFactorDecompositionStatement`](SimpleFactorDecompositionStatement.md))
  is Theorem 5.1.19. For a semisimple group `G` over a field `k : Type u`, it gives a finite
  family `a i : A i ⟶ G` listing the `k`-simple factors (the minimal nontrivial smooth
  connected closed normal subgroups) without repetition, together with:
  - each `A i` is almost simple;
  - the multiplication `∏ A i ⟶ G` is a central isogeny;
  - the subgroups `G_J` for `J : Set I`;
  - every smooth connected closed normal subgroup is a unique `G_J`;
  - further clauses that this proof does not use.
- `ReductiveSimpleFactorDecompositionStatement.{u}` (module
  [`Reductive.ReductiveSimpleFactorDecompositionStatement`](ReductiveSimpleFactorDecompositionStatement.md))
  is Exercise 5.5.2. Let `G` be connected reductive over `k`, `z : Z ⟶ G` its maximal
  central torus, `d : D ⟶ G` its derived group, and `a i : A i ⟶ D` (with `I` finite) a
  list of the `k`-simple factors of `D` without repetition. Then:
  1. the `a i ≫ d` are exactly the minimal non-central smooth connected closed normal
     subgroups of `G`;
  2. some `p : pi A ⟶ G` restricts to `a i ≫ d` on each factor, and the multiplication
     `Z ⊗ pi A ⟶ G`, `(x, y) ↦ z(x) p(y)`, is a central isogeny;
  3. smooth connected closed normal semisimple subgroups of `D` are normal in `G`.

Both statements are for the same universe `u`. The two sides are used exactly as
published. `reductiveSimpleFactorDecomposition_reduction` proves
`ReductiveSimpleFactorDecompositionReductionStatement.{u}` and assumes nothing else.

## Helper declarations

These are all in the namespace `Langlands.GroupScheme.ReductiveSimpleFactorDecomposition`.

- Three predicates that unfold to the local `let`s of the two statements.
  `IsSmoothConnectedNormal n` is `IsNormalSubgroup`: closed, smooth, connected, with
  normal range. `IsMinimalSmoothConnectedNormal n` is `IsMinimalNormalSubgroup`.
  `IsMinimalNoncentralSmoothConnectedNormal n` is `IsMinimalNoncentralNormalSubgroup`.
  The final theorem passes them to the statements by definitional unfolding.
- `isPullback_id_tensorHom` and `isCentralIsogeny_id_tensor`: `𝟙 K ⊗ f` is the base change
  of `f` along the second projection. Hence it is a central isogeny when `f` is one. Its
  kernel is `1 × ker f`, which is central.
- Range comparisons through a monomorphism `d`:
  - `range_comp_le_range_comp_iff` and `range_comp_eq_range_comp_iff` compare ranges
    after composing with `d`;
  - the existing `SubgroupFunctor.isNormal_range_of_mono_comp` says normality in `G` descends to `D`;
  - `commute_of_isCentral_comp` says centrality of `m ≫ d` makes the source commutative;
  - `isCentral_of_range_eq_bot` says a homomorphism with trivial range is central.
- `isCentralIsogeny_comp_of_center_mul_derived`, over a field. This is a variant of the
  Library's `IsCentralIsogeny.comp_of_derivedSubgroup_eq_top`
  ([`CentralIsogeny.PerfectComposition`](../CentralIsogeny/PerfectComposition.md)) with the
  same proof. The perfectness hypothesis is weakened: every point of the source must be a
  central point times a point of the derived subgroup. The fixed subgroup of the
  conjugation action of `ker (f ≫ q)` is representable (`fieldFixedSubgroupRepresentability`).
  It contains every commutator (`IsCentralIsogeny.commute_commutator_of_comp_eq_one`), so
  it contains the derived subgroup (`derivedSubgroup_le_range`). It also contains the
  centre.
- `piFactorInclusion_eq_hom` and `derivedSubgroup_pi_eq_top`: a finite product of perfect
  group schemes is perfect. Each point of `pi A` is the product of its factor insertions
  (`piPointsEquiv_symm_eq_list_prod`). Each insertion lies in the derived subgroup by
  `mem_derivedSubgroup_comp`.
- `isNormal_range_comp_of_isCentralIsogeny_mul`: suppose `z` is central and the
  multiplication `Z ⊗ D ⟶ G` is a central isogeny. Then the image in `G` of every normal
  subgroup of `D` is normal. The multiplication is flat, surjective and quasi-compact. So
  `SubgroupFunctor.mem_range_of_local_quotient_lift` reduces the claim to points
  `g = z(c) d(e)`. There `z(c)` is central and `d(e)` normalizes the subgroup. No
  smoothness is used.
- `tensor_center_mul_derived`: in `Z ⊗ P` with `Z` commutative and `P` perfect,
  `(c, y) = (c, 1) * (1, y)`. The first factor is central and the second is in the derived
  subgroup.
- `isCentralIsogeny_prodHom_comp`: let `Z ⊗ D ⟶ G` be a central isogeny, `z` a central
  monomorphism, `p : P ⟶ D` a central isogeny and `P` perfect. Then
  `prodHom z (p ≫ d)` is a central isogeny. It equals `(𝟙 Z ⊗ p) ≫ (Z ⊗ D ⟶ G)`, and
  the two previous items apply.
- `prodHom_iso_comp`: precomposing the second argument of `prodHom` with an isomorphism
  `Φ` precomposes the product map with `𝟙 Z ⊗ Φ`.
- `exists_equiv_of_injective`: two injective families with the same set of values are
  related by a bijection of index types.
- `exists_pi_iso_of_range_eq`: two families of closed subgroups with equal ranges, matched
  by `ε : I ≃ I'`, give isomorphisms `w i : A i ≅ A' (ε i)` over `D`
  (`IsClosedSubgroup.sourceIsoOfRangeEq`). They also give an isomorphism `pi A ≅ pi A'`
  compatible with the factor insertions (`Pi.mapIso`, `Pi.reindex`,
  `piFactorInclusionHom_comparison`).
- `range_eq_of_le_comp`: let `a` be minimal nontrivial smooth connected closed normal in
  `D`, and `d` a closed subgroup of `G`. Then every non-central smooth connected closed
  normal subgroup of `G` contained in `a ≫ d` equals it. Such a subgroup factors through
  `d`. Its factor is nontrivial (otherwise it is central), normal in `D` and contained in
  `a`.
- `main`: the reductive decomposition for one group, with the named predicates.

## Implemented proof of `main`

Fix `G`, `z`, `d` and the family `a` as in Exercise 5.5.2.

1. **Setup.**
   - `D` is semisimple (`derivedSubgroupSemisimple`).
   - `z` is a maximal central relative torus. The field-level torus conditions convert by
     `IsTorus.isRelativeTorus` and `RelativeTorus.IsTorus.isTorus`.
   - The multiplication `q : Z ⊗ D ⟶ G` is therefore a central isogeny
     (`IsMaximalCentralRelativeTorus.isCentralIsogeny_commutingMultiplication`, using the
     finite centre of `D`).
2. **Clause 3.** `isNormal_range_comp_of_isCentralIsogeny_mul` with `q`. Semisimplicity of
   `K` is not used.
3. **The semisimple decomposition of `D`.** Apply `SimpleFactorDecompositionStatement` to
   `D`. This gives a family `a' j : A' j ⟶ D`, almost-simple `A' j`, a central isogeny
   `p' : pi A' ⟶ D` restricting to `a' j`, and subgroups `b J : B J ⟶ D`. The `b J` contain
   the `a' j` with `j ∈ J` and are the smallest closed subgroups doing so. Every smooth
   connected closed normal subgroup of `D` is a unique `b J`. Both `a` and `a'` list the
   minimal nontrivial smooth connected closed normal subgroups of `D`, injectively. So
   `exists_equiv_of_injective` gives `ε : I ≃ I'` with `range (a i) = range (a' (ε i))`.
   Then `exists_pi_iso_of_range_eq` gives `w i : A i ≅ A' (ε i)` and `Φ : pi A ≅ pi A'`.
   Each `A i` is almost simple (`IsAlmostSimple.of_iso`).
4. **Clause 1, first half.** `a i ≫ d` is closed and smooth connected, and normal in `G`
   by step 2. It is non-central: otherwise `A i` would be commutative
   (`commute_of_isCentral_comp`), contradicting `IsAlmostSimple.noncommutative`.
   Minimality is `range_eq_of_le_comp`.
5. **Clause 1, second half.** Let `n : K ⟶ G` be minimal among the non-central smooth
   connected closed normal subgroups.
   - Let `E ⟶ K` be the derived subgroup of `K` (`smoothConnectedCommutatorImage`). It is
     smooth and geometrically connected, hence connected.
   - `E` is nontrivial. Otherwise `K` is commutative, hence solvable
     (`isSolvableGroupScheme_of_isSolvable_points`). Then `n` would be central by
     `IsSolvableGroupScheme.isCentral_of_normal_of_isConnectedReductive_field`.
   - The image of `E` in `G` lies in the derived subgroup of `G` (`mem_derivedSubgroup_comp`),
     which is the range of `d`. So it factors as `m : E ⟶ D` with `m ≫ d = E ⟶ K ⟶ G`.
     Here `m` is closed (`IsClosedSubgroup.of_comp`). It is normal in `D`: its image is
     normal in `G` (`IsDerivedSubgroup.isNormal_comp`), and normality descends along `d`.
   - So `range m = range (b J)` for some `J`.
   - `J` is nonempty. Otherwise `range (b ∅) ≤ range (kernelUnit D) = ⊥` by the
     least-subgroup property of `b ∅` (`kernelUnit_isClosedSubgroup`, `range_kernelUnit`).
     Then `m`, hence the inclusion of `E`, would be trivial.
   - For `j ∈ J`, `range (a (ε⁻¹ j)) = range (a' j) ≤ range (b J) = range m`. So
     `a (ε⁻¹ j) ≫ d` lies in the image of `E`, hence in `n`. By step 4 it is non-central
     smooth connected closed normal in `G`. Minimality of `n` gives
     `range n = range (a (ε⁻¹ j) ≫ d)`.
6. **Clause 2.** Put `p := Φ.hom ≫ p' ≫ d`. On the `i`-th factor,
   `piFactorInclusionHom A i ≫ Φ.hom = (w i).hom ≫ piFactorInclusionHom A' (ε i)`. So
   `p` restricts to `(w i).hom ≫ a' (ε i) ≫ d = a i ≫ d`. Next, `pi A'` is perfect: each
   almost-simple `A' j` is perfect (`IsAlmostSimple.derivedSubgroup_eq_top`), so
   `derivedSubgroup_pi_eq_top` applies. Hence `prodHom z (p' ≫ d)` is a central isogeny by
   `isCentralIsogeny_prodHom_comp` with `q` and `p'`. Finally,
   `prodHom z p = (𝟙 Z ⊗ Φ.hom) ≫ prodHom z (p' ≫ d)` (`prodHom_iso_comp`).
   Precomposition with an isomorphism keeps it a central isogeny
   (`IsCentralIsogeny.iso_comp`).

`reductiveSimpleFactorDecomposition_reduction` introduces the hypotheses of
Exercise 5.5.2 and applies `main`.

## Sources

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`
(SHA-256 `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page
numbers are the printed ones.

- Theorem 5.1.19, p.150: the decomposition theorem for semisimple groups (the premise).
- Exercise 5.5.2, p.182: its reductive generalization (the conclusion). Conrad leaves the
  exercise to the reader. He notes that for finite `k` an argument is needed for the
  normality of the `G′_i` in `G`; step 2 above uses the fpqc-local description of points
  of `G` instead of density of `G(k)`.

## Provenance

The implication is internal: it formalizes no new assertion from the literature. It
composes the two published Library statements above. The proof uses only Library results
and the helpers in this module.

## Scope

This module does not prove `SimpleFactorDecompositionStatement` or
`ReductiveSimpleFactorDecompositionStatement`. The first is proved as
`simpleFactorDecomposition` (`Reductive.SimpleFactorDecompositionProof`); applying
`reductiveSimpleFactorDecomposition_reduction` to it proves the second, as
`reductiveSimpleFactorDecomposition` (`Reductive.ReductiveSimpleFactorDecompositionProof`).
