# Central rigidity over a locally noetherian base

This module proves case a) of SGA 3, Exposé IX, Théorème 5.1 (`S` locally noetherian).
The source is the registered Gille–Polo 2009 recomposed edition
(`sga3-expose-ix-gille-polo-2009`), p.48 (PDF page 18). The proof there reduces to
`A = 𝒪_{S,s}` with maximal ideal `m` by EGA IV₃ 8.8.2.4. By 3.4, the reductions `u_n` and
`v_n` of `u` and `v` modulo `m^{n+1}` agree for every `n`. For each `m > 0`, the
`m`-torsion subgroup `ₘH` is finite over `S` (IX 2.2). Lemme 5.0 then shows that `u` and `v`
agree on `ₘH`, and the density theorem IX 4.7 gives `u = v`. The declarations below
implement this route. The intermediate statements are internal helpers derived for it.

All declarations are in the namespace `Langlands.GroupScheme.CentralRigidityLocal`. The
inputs all come from the Library:

- the torsion subgroup `torsion H n` with inclusion `torsionι H n` and
  `existsUnique_torsion_lift_iff` (module `AbelianScheme.Torsion`);
- `IsMultiplicativeType.torsion_geometry` (module
  `GroupScheme.Torus.RelativeMultiplicativeTypeTorsion`), which says that the torsion
  subgroup of a group of multiplicative type is finite over the base;
- `IsMultiplicativeType.isCommMonObj`, `.isSeparated`, `.quasiCompact` and
  `.locallyOfFinitePresentation`, and `IsMultiplicativeType.baseChange`;
- Lemme 5.0 as the theorem
  `Langlands.AlgebraicGeometry.AdicDetection.adicImmersionIsIso`, which proves
  `AdicImmersionIsIsoStatement` (module `AlgebraicGeometry.AdicDetectionProof`);
- the torsion-determination theorem `multiplicativeTypeTorsionDetermination` (module
  `GroupScheme.Torus.MultiplicativeTypeTorsionDeterminationProof`), part one of which is
  the form of IX 4.7 used here;
- the spreading theorem
  `Langlands.AlgebraicGeometry.specStalkFactorizationSpreading`, which proves
  `SpecStalkFactorizationSpreadingStatement` (EGA IV₃ 8.8.2 (i); module
  `AlgebraicGeometry.SpecStalkFactorizationSpreadingProof`);
- central infinitesimal uniqueness,
  `CentralInfinitesimalRigidity.centralInfinitesimalUniqueness` (module
  `GroupScheme.Torus.CentralInfinitesimalRigidityReduction`). For a commutative ring `A`,
  a nilpotent ideal `J ⊆ A`, group schemes `G` and `H` over `Spec A` with `H` of
  multiplicative type, and `f, g : H ⟶ G`, it says: if the base changes of `f` and `g`
  along `Spec(A/J) ⟶ Spec A` are equal and the base change of `f` is central, then
  `f = g`. This is the form of SGA 3, IX, 3.4 used in the proof of 5.1, with centrality
  only on the reduction and with `G` arbitrary;
- `MultiplicativeTypeAffineInfinitesimalCentrality.isCentral_baseChange_comp_iff`
  (module `GroupScheme.Torus.MultiplicativeTypeAffineInfinitesimalCentrality`). It says
  that centrality of a base change along a composite `c ≫ b` is equivalent to centrality
  of the iterated base change;
- the helper modules [`CentralRigiditySpreading`](CentralRigiditySpreading.md) and
  [`CentralRigidityTransport`](CentralRigidityTransport.md).

## Declarations

- `exists_finite_torsion hH n hn`: for `H` of multiplicative type over a scheme `S` and
  `n > 0`, there are a group scheme `K` and a homomorphism `i : K ⟶ H` such that `K` is
  finite over `S` and every point `x : T ⟶ H.X` with `x ^ n = 1` factors as
  `y ≫ i.hom.hom`. The proof takes `K = torsion H n` and `i = torsionι H n`, using the
  commutative group structure of `H`. Finiteness is the first component of
  `IsMultiplicativeType.torsion_geometry`, and the factorization is
  `existsUnique_torsion_lift_iff` applied to the integer power `n`.

In the remaining declarations, `A` is a noetherian local ring with maximal ideal `m`. Group
schemes are over `Spec A`.

- `comp_eq_of_adic hK i u v hk`: let `K` be finite over `Spec A`, let `i : K ⟶ H`, and let
  `u, v : H ⟶ G`. Suppose that for every `k`, the base changes of `u` and `v` along
  `Spec(A/m^{k+1}) ⟶ Spec A` are equal. Then `i ≫ u` and `i ≫ v` have equal underlying
  morphisms. Proof: Lemme 5.0 is applied to the finite morphism `K → Spec A` and to the
  kernel immersion `e = eqIncl (i ≫ u) (i ≫ v)`. For each `n`, the base change `e_n` of
  `e` along `Spec(A/m^{n+1}) ⟶ Spec A` must be an isomorphism. The base changes of `i ≫ u`
  and `i ≫ v` along this map are equal by `hk n`. By `baseChange_map_eq_iff` and
  `exists_factor_iff`, the projection from the base change of `K` to `K` factors through
  `e`, and this factorization gives a section `σ` with `σ ≫ e_n = 𝟙`. Also, `e_n` is a
  monomorphism, because `e` is one and morphisms into a pullback are determined by their
  projections. So `e_n` is a split epimorphism and a monomorphism, hence an isomorphism.
  Lemme 5.0 then makes `e` an isomorphism. The identity of `K` factors through `e`, and
  `exists_factor_iff` gives the equality.
- `eq_of_adic hH u v hk`: if `H` is of multiplicative type and the base changes of `u` and
  `v` along `Spec(A/m^{k+1}) ⟶ Spec A` are equal for every `k`, then `u = v`. By part one
  of `multiplicativeTypeTorsionDetermination`, it suffices to check that `x ≫ u = x ≫ v`
  for every point `x` of `H` with `x ^ n = 1` and `n > 0`. Such an `x` factors through the
  finite torsion subgroup of `exists_finite_torsion`, on which `u` and `v` agree by
  `comp_eq_of_adic`.
- `eq_mod_pow_of_residue hH u v hs hc k`: let `A` be a local ring, not necessarily
  noetherian. If the base changes of `u` and `v` along the residue map
  `Spec(A/m) ⟶ Spec A` are equal and the base change of `u` is central, then for every `k`
  the base changes along `Spec(A/m^{k+1}) ⟶ Spec A` are equal. Proof: put
  `B = A/m^{k+1}` and `J = mB`. Then `J^{k+1} = 0`. The composite
  `Spec(B/J) ⟶ Spec B ⟶ Spec A` equals `Spec(B/J) ⟶ Spec(A/m) ⟶ Spec A`, where the first
  map is induced by the lift `A/m → B/J` of the quotient map. Hence equality and centrality
  pass from the residue field to `B/J` (`baseChange_eq_and_central_of_factor`), and are
  rewritten as statements about the base changes of `u_B` and `v_B` along
  `Spec(B/J) ⟶ Spec B`. `centralInfinitesimalUniqueness`, applied to `B`, `J` and the
  base changes of `u` and `v` to `Spec B` (the source stays of multiplicative type),
  gives `u_B = v_B`.
- `eq_of_residue hH u v hs hc`: under the same hypotheses on the closed fibre, with
  `A` noetherian, `u = v`. This combines `eq_mod_pow_of_residue` and `eq_of_adic`.
- `exists_open_eq_of_locallyNoetherian S H G hH u v s hs hc`: let `S` be locally
  noetherian, let `H` be of multiplicative type over `S`, and let `u, v : H ⟶ G`. If
  `u_s = v_s` and `u_s` is central at a point `s`, both as base changes along
  `S.fromSpecResidueField s`, then there is an open `U ∋ s` with `u_U = v_U` (base change
  along `U.ι`). This is clause 5.1 of the statement for locally noetherian `S`. Proof: `H` is quasi-compact, separated and locally of finite presentation over
  `S`, so `H` is locally noetherian and `eqIncl u v` is locally of finite presentation.
  `exists_open_baseChange_eq` with `specStalkFactorizationSpreading` therefore reduces the
  claim to the equality of the base changes of `u` and `v` to `Spec 𝒪_{S,s}`. The morphism
  `S.fromSpecResidueField s` is the residue map of the stalk followed by
  `S.fromSpecStalk s`. The transport lemmas rewrite `hs` and `hc` as statements about the
  base changes along this residue map, and `eq_of_residue` applies with `A = 𝒪_{S,s}`.

This module adds no axioms and has no hypotheses beyond those stated in each theorem.
