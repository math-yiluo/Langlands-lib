# Point-parahoric root intersections from local opposite factor pairs

Worker 1302, using Worker 1612's direct valuation and normalizer argument.
This internal construction defines
`ParahoricBuildingData.rootGroupParahoricAtEquivFiltrationOfFactorPairs`, the
identity multiplicative equivalence between
`P.rootGroup a ⊓ P.parahoricAt x` and `P.filtration x a 0`.
The supporting theorem
`rootGroup_inf_parahoricAt_eq_filtration_of_factorPairs` proves the subgroup
equality for any actual relative root and any apartment point.

The data are the existing parahoric data over a nonarchimedean local field in
arbitrary universe `u`. The premises are the original apartment axioms and
`RelativeRoot.HasOppositeFactorPairs P.i` for this particular torus inclusion.
The existing existence-only assembly supplies the full rank-one predicate
used by the published point-parahoric normalizer fixing theorem. No global
rank-one, ray-decomposition or ordered-product proposition is a premise.
In particular, this construction does not require the local ordered-root
embedding or the global `DynamicRootOrderedProductStatement`.

For a nonidentity point `g` in the actual root-group intersection, its
valuation at `x` is a finite real number `t`. Suppose it is negative. An
opposite factor pair `(p₁,p₂)` makes `m = p₁ g p₂` a normalizer point. V5,
including its published second-factor consequence, gives valuation `-t`
to each opposite factor. Both therefore lie in the opposite depth-zero
filtration and hence in the point parahoric. Since `g` also belongs to that
subgroup, so does `m`. The published
`normalizer_smul_eq_self_of_mem_parahoricAt` makes `m` fix `x`.

The actual Weyl action of the pair negates the root. The existing computation
`KPApartmentData.eval_translation_eq_of_factor` evaluates the displacement
of this normalizer point on that root as `-2t`. Because it fixes `x`, its
displacement on the valuation family can be taken to be the zero vector.
Thus `0 = -2t`, contradicting negativity. This uses the translation
computation directly; it does not assume a converse to the forward
fixed-hyperplane law in `HasRootReflections`.

Consequently `g` lies in its own depth-zero filtration. The identity case
follows from subgroup membership. The reverse inclusion follows from the
filtration's containment in the root group and in the singleton sharp fixer,
which is contained in the full point parahoric. `MulEquiv.subgroupCongr`
packages the equality, and the application formula is definitional.

The provenance is the internal argument above, composed with the existing
actual-group rank-one assembly, V5 consequences, normalizer fixing and
translation computation. It proves neither opposite factor-pair existence
nor the exact apartment-only `RootGroupParahoricFiltrationStatement`.
That unchanged target still requires discharging local pair existence
independently. No new external source assertion is introduced.
