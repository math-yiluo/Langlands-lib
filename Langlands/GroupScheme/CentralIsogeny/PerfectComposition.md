# Composites of central isogenies out of a perfect field group

This module proves that over a field `k`, the composite of two central isogenies
`f : H' ⟶ H` and `q : H ⟶ G` is a central isogeny whenever the source `H'` is perfect in the
scheme-theoretic sense, `derivedSubgroup H' = ⊤`. Central isogenies are the Library's
`IsCentralIsogeny` (`CentralIsogeny/Basic`): finite, flat, surjective and locally of finite
presentation, with full scheme-theoretic kernel inside the all-test-scheme centre.

Only centrality of the kernel needs work. Being an isogeny and local finite presentation are
both stable under composition.

## Statements

- `commute_commutatorElement_of_forall_commute` (an arbitrary group `M`). Let `z ∈ M`, and
  suppose every commutator `⁅w, z⁆` is central in `M`. Then `z` commutes with every
  commutator `⁅x, y⁆`. Commutators are `⁅a, b⁆ = a b a⁻¹ b⁻¹`, Mathlib's scoped
  `commutatorElement`.
- `IsCentralIsogeny.commute_commutator_of_comp_eq_one`. Let `f`, `q` be central isogenies
  over `Spec k`, and let `z` be a `T`-point of `H'` killed by `f ≫ q`. Then `z` commutes
  with `⁅x, y⁆` for all `T`-points `x, y` of `H'`.
- `IsCentralIsogeny.comp_of_derivedSubgroup_eq_top (hperf : derivedSubgroup H' = ⊤) hf hq :
  IsCentralIsogeny (f ≫ q)`.

The groups are arbitrary `GroupScheme (Spec (CommRingCat.of k))` for a field `k : Type u`.
The theorem needs no smoothness, connectedness or reductivity hypothesis beyond `hperf`.

## Proofs

**Group lemma.** If every `⁅w, z⁆` is central, then `⁅a b, z⁆ = ⁅a, z⁆ ⁅b, z⁆`. This is a
direct calculation using one commutation, checked by `group`. So `w ↦ ⁅w, z⁆` is a
homomorphism `M →* Subgroup.center M` into a commutative group. It therefore sends
`⁅x, y⁆` to `1`, which gives `⁅⁅x, y⁆, z⁆ = 1`.

**Points killed by the composite.** The point `z ≫ f` is killed by `q`, so it is central in
`H` (`IsCentralIsogeny.mem_center_of_comp_eq_one` for `q`). For every point `w` of `H'`,
the image of `⁅w, z⁆` under `f` is `⁅w ≫ f, z ≫ f⁆ = 1`. So `⁅w, z⁆` is killed by `f`
and is central in `H'` (the same lemma for `f`). The group lemma, applied to the group of
`T`-points of `H'`, finishes the proof.

**Main theorem.** Let `K = kernel (f ≫ q)`. It is finite over `Spec k`, as the base
change of the finite morphism `f ≫ q` (`kernel_isPullback_scheme`), and so it is affine.
Let `a` be the conjugation action of `K` on `H'` through `kernelι (f ≫ q)`
(`AutomorphicAction.conjugation`).

1. The published `fieldFixedSubgroupRepresentability` provides a closed subgroup
   `j : C ⟶ H'` whose range is the fixed subgroup functor `a.fixedSubgroup`.
2. That range contains every commutator. A commutator `x y x⁻¹ y⁻¹` of `T`-points is fixed
   if, after every refinement `b : T' ⟶ T`, conjugation by every point `h` of `K` fixes
   `b ≫ (x y x⁻¹ y⁻¹) = ⁅b ≫ x, b ≫ y⁆`. The point `h ≫ kernelι` is killed by `f ≫ q`
   (`mem_range_kernelι_iff`), so the previous lemma applies.
3. Hence `derivedSubgroup H' ≤ a.fixedSubgroup` (`derivedSubgroup_le_range`). With `hperf`,
   every point of `H'` is fixed by conjugation by every point of `K`.
4. Centrality of `kernelι (f ≫ q)` is checked through `isCentral_kernelι_iff`. Let `x` be a
   `T`-point killed by `f ≫ q`, `b : T' ⟶ T` a refinement and `g` a `T'`-point of `H'`.
   The point `b ≫ x` comes from the `T'`-point `h` of `K` given by `kernelPointsEquiv`.
   Fixedness of `g` under `h` gives `(b ≫ x) g (b ≫ x)⁻¹ = g`, which is the required
   commutation.

## Relation to the literature

Milne, *Algebraic Groups* (2017), Proposition 18.2 (printed p.387) says that a composite of
multiplicative isogenies of connected group varieties is multiplicative. By the remarks after
Definition 18.1, a central isogeny out of a reductive group is multiplicative (17.62), and a
multiplicative isogeny is central (12.38). Milne's proof uses rigidity, Corollary 12.41
(printed p.244). The official errata snapshot of 2026-11-02 corrects the hypothesis of 12.41:
`N` should be a central subgroup of `H`. That correction does not affect the result.

This module takes another route, used for groups that are equal to their derived group
(Milne, Definition 12.45, printed p.245). Rigidity is replaced by the derived subgroup
argument above, which works with the published closed fixed-subgroup theorem and the
scheme-theoretic `derivedSubgroup` of `Derived/Basic`. The theorem is internal
infrastructure. Its intended use is with `SemisimplePerfectStatement`
(`Derived/SemisimplePerfectStatement`), which says that semisimple field groups are
perfect. Then composites of central isogenies between semisimple groups are central. This
module does not assume that statement.
