# Lifting a power map through a central quotient

Module `Langlands.GroupScheme.CentralIsogeny.PowerLift`, namespace
`Langlands.GroupScheme.CentralPowerLift`.

This is an internal helper of the proof that maximal split tori lift under central
isogenies (`Langlands.GroupScheme.CentralIsogenyMaximalSplitTorusLiftStatement`). It is
not a literature statement. The literature proof takes another route. In Borel–Tits,
*Compléments à l'article « Groupes réductifs »* (1972, source
`borel-tits-1972-complements-groupes-reductifs`), the proof of Théorème 2.20(ii) (printed
p.260, PDF p.9) proceeds as follows. It chooses a maximal `k`-torus `T'` of the target
containing the given maximal split torus. By Proposition 2.11(iv) (printed pp.256–257, PDF
pp.5–6) the inverse image of `T'` is a maximal torus of the source. The proof then takes its
maximal `k`-split subtorus, whose image is the given split torus. Proposition 2.11(iv) is not
in the Library. This helper instead supplies an explicit power map, as follows.

## Setting

`B` is an arbitrary base scheme. `π : G ⟶ H` is a homomorphism of group schemes over `B`
(objects of `Grp (Over B)`). `i : S ⟶ H` is a homomorphism from a group scheme `S` whose
underlying object is commutative (`[IsCommMonObj S.X]`). `N : ℕ` is arbitrary. The
hypotheses on the kernel are stated pointwise on the `T`-points `x : T ⟶ G.X`, for all
`T : Over B`:

* `hc`: if `x ≫ π = 1`, then `x` lies in the centre `center G` (`Rational/Characters`);
* `hN`: if `x ≫ π = 1`, then `x ^ N = 1` in the group of `T`-points.

## Declarations

* `mul_pow_two_mul_eq` is a group lemma. Let `a, b` be elements of a group and
  `c = b⁻¹ a⁻¹ b a`. If `c` commutes with `a` and with `b`, and `c ^ N = 1`, then
  `(a b) ^ (2N) = a ^ (2N) b ^ (2N)`. Two private induction lemmas give
  `b ^ n a = a b ^ n c ^ n` and `(a b) ^ n = a ^ n b ^ n c ^ (n choose 2)`. For `n = 2N` the
  exponent `(2N choose 2) = N (2N - 1)` is a multiple of `N`.
* `powerMap π i N` is the `2N`-th power, in the group of points, of the projection
  `subgroupIntersectionFst π i` from the fibre product `E = G ×_H S`
  (`subgroupIntersection π i`) to `G`.
* `quasiCompact_snd`, `flat_snd`, `surjective_snd`: the projection `E ⟶ S` is
  quasi-compact, flat and surjective on underlying schemes when `π` is. Each is a base change
  along the scheme pullback square `subgroupIntersection_isPullback_scheme`.
* `isMonHom_powerMap` (under `hc`, `hN`): `powerMap` is a monoid homomorphism. Let `x, y` be
  points of `E` and `a, b` their images in `G`. Their images in `H` come from the commuting
  points of `S`, so the commutator `c` of `a, b` maps to `1` in `H`. Hence `c` is central and
  `c ^ N = 1`, and `mul_pow_two_mul_eq` applies. The criterion used is
  `Semidirect.isMonHom_of_mul_comp`.
* `powerHom π i hc hN : subgroupIntersection π i ⟶ G` is the resulting homomorphism.
  `powerHom_hom` records its underlying map.
* `kernelι_comp_powerHom`: `powerHom` kills the kernel of `E ⟶ S`. A point of that kernel
  maps to `1` in `H`, so its image in `G` is killed by `N`, and hence by `2N`.
* `exists_comp_eq_multiplication_comp` (with `π` quasi-compact, flat and surjective, and
  `hc`, `hN`): there is `Φ : S ⟶ G` with `Φ ≫ π = multiplication S (2 * N) ≫ i`. Here `Φ`
  is the fpqc descent `FpqcHomDescent.hom` of `powerHom` along `E ⟶ S`
  (`Langlands.GroupScheme.HomDescent`). The equation is checked after precomposing with
  the epimorphism `E ⟶ S`. It reduces to `(fst ^ (2N)) ≫ π = (snd ≫ i) ^ (2N)`, which uses
  `points_multiplication` and the pullback square.
* `Langlands.GroupScheme.IsCentralIsogeny.exists_comp_eq_multiplication_comp`: the same
  conclusion for a central isogeny `π` (`hπ : IsCentralIsogeny π`). Here `hN` is stated for
  the points of the actual scheme-theoretic kernel `kernel π`: every
  `x : T ⟶ (kernel π).X` has `x ^ N = 1`. Flatness, surjectivity and quasi-compactness
  (from finiteness) come from `hπ`. Centrality is `IsCentralIsogeny.mem_center_of_comp_eq_one`.
  The kernel hypothesis is transported along `kernelPointsEquiv`.

`N = 0` is allowed. The conclusion is then trivial in content, since `multiplication S 0`
is the trivial homomorphism. The consumer uses `N > 0`.
