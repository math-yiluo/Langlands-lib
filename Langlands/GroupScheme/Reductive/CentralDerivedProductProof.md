# Central torus and derived subgroup generation: the proof

Author: Worker 4015.

`Langlands.GroupScheme.reductiveCentralDerivedProduct` proves exactly the
published proposition
`Langlands.GroupScheme.ReductiveCentralDerivedProductStatement.{u}` (module
[`CentralDerivedProductStatement`](CentralDerivedProductStatement.md)). It
holds at every universe `u` and takes no hypotheses.

Take any field `k : Type u` and any group scheme `G` over `Spec k` with
`IsConnectedReductive G`. The theorem gives a commutative group scheme `Z`, a
group scheme `D`, and homomorphisms `i : Z.toGrp ⟶ G` and `d : D ⟶ G`. They
satisfy all seven conjuncts of the target:

- the structure morphism of `Z` is affine and locally of finite type;
- `IsTorus Z.toGrp` holds;
- `i` is a closed subgroup (`IsClosedSubgroup i`) and central (`IsCentral i`);
- `IsDerivedSubgroup d` holds: `d` is a closed immersion whose range functor is
  the full `derivedSubgroup G`;
- the imported map `subgroupProductMap i d : Z.toGrp.X ⊗ D.X ⟶ G.X` is an
  epimorphism in `Over (Spec k)`.

The field may be imperfect and of any characteristic. No splitting,
character or product-generation hypothesis is added.

## Implemented proof

The Lean proof is one application of two published Library declarations, both
at universe `u`:

- `reductiveCentralDerivedProduct_of_torusSurjectivity`, from
  [`CentralDerivedProductReduction`](CentralDerivedProductReduction.md), has
  type
  `ReductiveCentralTorusSurjectivityStatement.{u} → ReductiveCentralDerivedProductStatement.{u}`.
  It is a proof-producing `def` (with `linter.defProp` disabled) and is used
  here like a theorem.
- `reductiveCentralTorusSurjectivity`, from
  [`CentralTorusSurjectivityProof`](CentralTorusSurjectivityProof.md), is an
  unconditional proof of
  `ReductiveCentralTorusSurjectivityStatement.{u}`. That statement says the
  following. For every connected reductive `G` over a field and every actual
  `d : D ⟶ G` with `IsDerivedSubgroup d`, some closed central torus
  `i : Z.toGrp ⟶ G` exists, affine and locally of finite type, such that the
  underlying function of `(subgroupProductMap i d).left` is surjective.

Applying the first to the second gives the target. The imported declarations
do the work as follows; their own Markdown has the details.

1. The reduction takes the derived subgroup from the published proof
   `derivedSubgroupRepresentability`. This gives an actual closed `d : D ⟶ G`
   with `IsDerivedSubgroup d`. Its premises, that `G` is affine and locally of
   finite type, come from `hG.isAffineHom` and `hG.smooth`.
2. For this `d`, `reductiveCentralTorusSurjectivity` gives `Z` and `i`. It
   also gives the five torus conjuncts and surjectivity of the underlying map
   of `subgroupProductMap i d`. Its proof combines two results:
   `reductiveCentralTorusSemisimpleQuotient` gives a central torus with
   semisimple quotient, and `semisimplePerfect` says semisimple field groups
   are perfect on all test schemes. The actual smooth quotient
   `q : G ⟶ Q` by the torus is formed. Perfectness of `Q` makes `d ≫ q`
   surjective. A section argument on a fibre product then gives surjectivity
   of the multiplication map.
3. The reduction turns surjectivity into `Epi` with
   `IsConnectedReductive.epi_subgroupProductMap_of_surjective`, from
   `Langlands.AlgebraicGeometry.SurjectiveReducedEpi`. A smooth group over a
   field is reduced. A morphism that is surjective onto a reduced scheme is an
   epimorphism in the category of all schemes, with any target scheme. The
   faithful forgetful functor then gives epimorphy in `Over (Spec k)`.
4. The reduction packages `Z, D, i, d` and the seven conjuncts in the order
   the target requires.

`lean_check` compiles the module with no errors or warnings. It reports only
the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Comparison with the original source

The task cites J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (printed page `p` is PDF page `p + 16`). There,
Proposition 21.61 (printed p.443) works over arbitrary fields. Its step from (b)
to (c) reuses 21.60(b) to (c) (printed p.442): the radical is a central torus
whose quotient is semisimple, hence perfect by Corollary 21.50 (printed p.440).
Proposition 12.46(b) (printed pp.245–246) then makes multiplication from that
torus times the derived subgroup a quotient map onto `G`.

The imported chain follows this route, with two differences.

- Milne shows `G/(T · D(G))` is commutative and perfect. The Lean route
  instead shows that `D(G)` maps onto the semisimple quotient `G/T`, then uses
  a fibre-product section argument to get surjectivity of the multiplication
  map.
- Milne's quotient maps are faithfully flat (5.5/5.7, printed p.99). The Lean
  route reaches the scheme-category epimorphism through reducedness of the
  smooth group `G`, so surjectivity alone suffices. It does not use faithful
  flatness of the multiplication map.

This final composition adds no structural assertion or source citation beyond
those recorded in the linked modules.
