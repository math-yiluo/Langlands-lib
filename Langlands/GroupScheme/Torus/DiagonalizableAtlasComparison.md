# Comparison isomorphisms between diagonalizable charts and their free lifts

All schemes lie in an arbitrary universe `u`.

## Bridge lemmas for iterated base change

These lemmas concern the published comparisons
`pullbackComparison p q r h G : q*(p*G) ≅ r*G` (for `q ≫ p = r`) and the
restriction `pullHom` of homomorphisms between base changes.

- `pullbackComparison_tower'` and `pullbackComparison_tower_inv`: for a
  three-step tower `V ⟶ U ⟶ T ⟶ S` the two composites of comparisons
  `c*(q*(p*G)) ⟶ a*G` agree. This is checked on the projection to `G`.
- `pullHom_conj_pullbackComparison`: restricting a homomorphism conjugated by
  comparisons for `t : S ⟶ B` gives the conjugate, by the restricted
  comparisons, of the restricted homomorphism.
- `dpull_conj`: the same statement with the comparisons
  `diagonalizableBaseChangeIso` and the restriction `dpull` of module
  `DiagonalizableIsoLift`.
- `pullHom_inv`: restricting the inverse of an isomorphism gives the inverse of
  its restriction `pullIso`.

## Diagonalizable atlases

`DiagonalizableAtlas H` for a group scheme `H` over `S` records:

- an index type `I : Type u`;
- schemes `Z i` with maps `f i : Z i ⟶ S`;
- abelian groups `Λ i` that are finitely generated (`AddGroup.FG`);
- isomorphisms `e i : (f i)*H ≅ D_{Z i}(Λ i)`.

The structure does not require the `f i` to be flat or jointly surjective;
those hypotheses are added where they are used. For an atlas `A`:

- `triv i : (f i)*H ≅ (f i)*D_S(Λ i)` is `e i` followed by the inverse of
  `diagonalizableBaseChangeIso`.
- `chartTriv i x l hx : l*H ≅ D_V(Λ i)` for a chart coordinate
  `x : V ⟶ Z i` of `l : V ⟶ S` (`x ≫ f i = l`). It is the restriction of
  `triv i` along `x`, followed by `diagonalizableBaseChangeIso l`.
- `comparison i j x y l hx hy : D_V(Λ i) ≅ D_V(Λ j)` is
  `(chartTriv i x l hx).symm ≪≫ chartTriv j y l hy`. It satisfies
  `comparison_self` and `comparison_trans`. `comparison_hom_eq` is an explicit
  formula, and `dpullIso_comparison` says that it commutes with pullback along
  any `q : W ⟶ V`.
- `lift i j x y l hx hy : D_V(F(Λ i)) ≅ D_V(F(Λ j))` is
  `liftIso (comparison …)` from module `DiagonalizableIsoLift`. The laws of
  `liftIso` give `lift_self`, `lift_trans` and `dpullIso_lift`. `lift_comm`
  says that `D(proj)` intertwines `comparison` and `lift`:
  `comparison.hom ≫ D(proj (Λ j)) = D(proj (Λ i)) ≫ lift.hom`.

Provenance: internal. The atlas packages the data in the definition of
`IsMultiplicativeType` (an fppf cover with diagonalizable pieces;
Conrad, *Reductive group schemes* (2014), Definition B.1.1), with chosen
character groups and trivializations.
