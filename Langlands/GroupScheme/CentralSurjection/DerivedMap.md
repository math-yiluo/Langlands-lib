# Derived subgroups under a surjection with central kernel

Module `Langlands.GroupScheme.CentralSurjection.DerivedMap`, namespace
`Langlands.GroupScheme`. Internal helper for the comparison of buildings along
a surjection with central kernel (Kaletha–Prasad Axiom 4.1.1, case of a central
quotient). Author: Worker 230.

Throughout, `k` is a field, `G`, `G'` are group schemes over `Spec k`,
`f : G ⟶ G'` is a homomorphism, and `d : D ⟶ G`, `d' : D' ⟶ G'` exhibit the
derived subgroups (`IsDerivedSubgroup`). The induced homomorphism
`f_D = hd.map hd' f : D ⟶ D'` is the Library's `IsDerivedSubgroup.map`, with
`f_D ≫ d' = d ≫ f` (`IsDerivedSubgroup.map_comp`).

## Statements

In namespace `IsDerivedSubgroup`, with `hd : IsDerivedSubgroup d` and
`hd' : IsDerivedSubgroup d'`:

- `comp_map_eq_one_iff`: a point `x` of `D` is killed by `f_D` iff `x ≫ d` is
  killed by `f`.
- `isCentral_kernelι_map`: if the kernel of `f` is central
  (`IsCentral (kernelι f)`), so is the kernel of `f_D`.
- `isFinite_kernel_map`: if `G`, `G'` are connected reductive and the kernel
  of `f` is central, the kernel of `f_D` is finite over `Spec k`.
- `surjective_map`: if `G`, `G'` are connected reductive and `f` is surjective
  on underlying schemes, so is `f_D`.
- `isCentralIsogeny_map`: under the hypotheses of the previous two items,
  `f_D` is a central isogeny (`IsCentralIsogeny`: finite, flat, surjective,
  locally of finite presentation, central kernel).

In namespace `Langlands.GroupScheme`:

- `exists_eq_map_mul_centralizer_of_centralSurjection`: let `G`, `G'` be
  connected reductive, `f` surjective with central kernel, `i' : S' ⟶ G'` a
  maximal split torus and `j' : Z' ⟶ G'` a representative of its centralizer
  (`(torusCentralizer i').IsRepresentedBy j'`). Every `g' ∈ G'(k)` is
  `f(g) · j'(z)` for some `g ∈ G(k)` and `z ∈ Z'(k)`.

## Proofs

**Kernel.** `comp_map_eq_one_iff` cancels the monomorphism `d'` in
`x ≫ f_D ≫ d' = x ≫ d ≫ f`. For centrality, a point killed by `f_D` maps by
`d` to a point killed by `f`, which is central in `G` by
`isCentral_kernelι_iff`. So `kernelι f_D ≫ d` is central, and
`IsCentral.of_comp` removes the monomorphism `d`.

**Finite kernel.** The published `derivedCentralIntersectionFiniteness` gives a
finite closed subgroup `c : C ⟶ D` whose range is `(center G).comap d`. The
range of `kernelι f_D` lies in it (previous paragraph), so `kernelι f_D`
factors as `a ≫ c` (`IsRepresentedBy.factorHom`). As `kernelι f_D` is a closed
immersion (`D'` is affine), so is `a`
(`IsClosedImmersion.of_comp_isClosedImmersion`). Hence the kernel is finite
over `Spec k`, being closed in the finite `C`.

**Surjectivity.** `D` is smooth (`IsDerivedSubgroup.smooth_of_connected`),
connected (`derivedSubgroupConnectedness`) and affine. `f` is quasi-compact,
and flat by `flat_of_surjective` since `G'` is smooth. The published
`HomImage.exists_image` factors `d ≫ f` as `fac ≫ inc` with `fac` surjective
and `inc : C ⟶ G'` a closed subgroup. By
`PerfectQuotientImage.containsCommutators_range_of_factor` the range of `inc`
contains all commutators of `G'`, so `derivedSubgroup_le_range` gives
`range d' = derivedSubgroup G' ≤ range inc`. Then `d' = a ≫ inc` for some
`a`, and `f_D ≫ a = fac` because `inc` is a monomorphism. The map `a` is
injective on points, because `a ≫ inc = d'` is a closed immersion. Given
`y ∈ D'`, pick `x` with `fac x = a y`. Then `a (f_D x) = a y`, so `f_D x = y`.

**Central isogeny.** Flatness of `f_D` is `flat_of_surjective` (`D'` is
smooth). Finiteness is `isFinite_of_finite_kernel` from the finite kernel.
Local finite presentation follows from local finite type over the locally
noetherian `D'`. Centrality is `isCentral_kernelι_map`.

**Fact 2.6.22 along `f`.** The published `simplyConnectedDerivedCoverExistence`
gives simply connected derived covers `π : C ⟶ D` of `G` and `π' : C' ⟶ D'` of
`G'` (`IsSimplyConnectedDerivedCover`). The composite `π ≫ f_D` is a central
isogeny by `IsCentralIsogeny.comp_of_derivedSubgroup_eq_top`. That theorem
needs the source to be perfect, and `C` is: it is semisimple, so
`semisimplePerfect` applies. The universal property of `π'`
(`HasCentralCoverUniversalProperty`, applied to the semisimple `C`) gives
`a : C' ⟶ C` with `a ≫ π ≫ f_D = π'`. The published
`simplyConnectedCentralizerProduct` (KP Fact 2.6.22) writes
`g' = (π' ≫ d')(c') · j'(z)`. Since
`π' ≫ d' = a ≫ π ≫ f_D ≫ d' = (a ≫ π ≫ d) ≫ f`, one may take
`g = (a ≫ π ≫ d)(c')`.

## Provenance

This is internal content. In the source, Kaletha–Prasad, *Bruhat–Tits Theory:
A New Approach* (2023), Axiom 4.1.1 (printed pp.157–158) asserts that a
surjection with central kernel induces an isomorphism of buildings, and
Fact 2.6.22 gives `G(k) = G(k)^♮ · Z(k)`. The statements here are the
group-scheme inputs used to prove that comparison through the derived
subgroups. They are standard (a central surjection restricts to a central
isogeny of derived groups, and simply connected covers lift through central
isogenies); the Lean proofs are the ones described above.
