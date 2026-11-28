# Constructions for the depth-zero step of BK93 (8.1.5)

This internal module proves the constructions in the proof of Bushnell–Kutzko, *The admissible
dual of GL(N) via compact open subgroups* (1993), (8.1.5), case `m = 0`, printed pp. 268–269
(PDF pp. 280–281). Literature ID `bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`. The module
`Langlands.BushnellKutzko.ZeroDepthCharacterStepReduction` assembles them into the step.

There, `π` is an irreducible smooth representation of `GL_N(F)` containing a simple character
`θ ∈ C(𝔄, 0, β)` of a simple stratum `[𝔄, n, 0, β]`. BK93 observe that `π` contains the
representation `η` of `J^1 = J^1(β, 𝔄)` over `θ` (5.1.1), hence an irreducible representation
`ϑ` of `J = J(β, 𝔄)` containing `η`, and deduce from (5.2.2) that `ϑ = κ ⊗ ξ` with `κ` a
`β`-extension of `η` and `ξ` irreducible and trivial on `J^1`; then `ξ` is inflated from `J / J^1 ≅ U(𝔅) / U^1(𝔅) ≅ ∏_i GL(m_i, k_E)` and is
a tensor product `ξ_1 ⊗ … ⊗ ξ_e` of irreducible representations of the factors. The lemmas below
prove these steps in Lean. The representation `π` of `GL_N(F)` is restricted to a subgroup `J`
of `Aut_F(F^N)` along the inclusion of `J` into `Aut_F(F^N)` followed by
`Matrix.GeneralLinearGroup.toLin.symm`, which sends an automorphism to its matrix
(`autRestrict π J`, an abbreviation). Unlike BK93, the Lean
construction of `η` does not use (5.1.1): `η` is found inside `π` directly (see
`exists_heisenberg_constituent`). Of (5.2.2) it uses only the existence of a `β`-extension `κ`;
the factor `ξ` comes from Clifford theory over `J^1`
(`Clifford.exists_irreducible_tensor_intertwining`).

Notation: `simpleJ S.chain S.n S.b q.tail` is `J(β, 𝔄)`, `simpleJGroup … 1` is `J^1(β, 𝔄)`, and
`simpleHGroup … 1` is `H^1(β, 𝔄)`.

## Generic lemmas

- `exists_comp_eq_of_surjective`: a representation of `H` trivial on the kernel of a surjective
  homomorphism `φ : H →* P` is `ρ' ∘ φ` for a representation `ρ'` of `P`. It is the lift through
  `H / ker φ` composed with the inverse of `QuotientGroup.quotientKerEquivOfSurjective`.
- `classTensor a`: for a finite family of finite groups `G_i` and irreducible classes `a i` of
  `G_i` (`FiniteRep.IrreducibleClass`), the external tensor product of the chosen representatives
  `FiniteRep.VirtualCharacter.rep (a i)`, each realized on a coordinate space `Fin d_i → ℂ` by
  `Clifford.coordinateRep`, as a representation of `∏_i G_i`.
- `isIrreducible_coordinateRep_rep`: the coordinate realization of the representative of an
  irreducible class is irreducible (`FiniteRep.VirtualCharacter.isIrreducible_rep`, transported
  along `Clifford.coordinateEquiv`).
- `classTensor_const`: for a constant family `(c, …, c)` indexed by `Fin e`, `classTensor` is,
  by definition, the tensor power `tensorPowerRepresentation` of the coordinate realization of
  `c`.
- `nonempty_equiv_tensorPower_comp`: from an equivalence `ξ ∘ ι ≅ classTensor (c, …, c) ∘ φ`
  and an isomorphism `ε : H ≃* U` with `ι ∘ ε⁻¹ = ι'`, it gives an equivalence of `ξ ∘ ι'` with
  the tensor power of the coordinate realization of `c` inflated along `φ ∘ ε⁻¹`. The proof
  pulls the equivalence back along `ε⁻¹` (`Cohomology.HyperextAbutment.equivComp`) and rewrites
  with `classTensor_const`.
- `exists_equiv_classTensor`: an irreducible representation of a finite product `∏_i G_i` of
  finite groups on `Fin d → ℂ` is equivalent to `classTensor a` for some family of classes `a`.
  Library `FiniteRep.exists_externalRep_equiv` gives an equivalence with the external tensor
  product of the representatives, and the coordinate isomorphisms of the factors
  (`Module.finBasis`) are assembled by `PiTensorProduct.congr`; the action is compared on pure
  tensors.
- `exists_equiv_classTensor_comp` (layer decomposition): let `ξ` be an irreducible
  representation of `K` on `Fin d → ℂ`, `ι' : H →* K` a homomorphism such that every operator
  `ξ g` equals some `ξ (ι' x)`, and `φ : H →* ∏_i G_i` a surjection onto a finite product of
  finite groups with `ξ ∘ ι'` trivial on `ker φ`. Then `ξ ∘ ι' ≅ classTensor a ∘ φ` for some `a`.
  The representation `ξ ∘ ι'` is irreducible (`Clifford.isIrreducible_comp_iff`), factors as
  `ξ' ∘ φ` (`exists_comp_eq_of_surjective`), `ξ'` is irreducible
  (`FiniteRepresentation.SplitDegree.isIrreducible_of_comp`), and `exists_equiv_classTensor`
  applies to `ξ'`.
- `LatticeChain.relIndex_eq_of_bases`: if every layer `L_i / L_{i+1}`, `0 ≤ i < e`, of a lattice
  chain over a discrete valuation ring has a residue-field basis indexed by `Fin r`, then every
  index `(L_j : L_{j+1})`, `j ∈ ℤ`, equals the cardinality of `(Fin r → k)` for the residue field
  `k`. Each layer `L_j / L_{j+1}` is isomorphic to one of the layers `L_s / L_{s+1}` with
  `0 ≤ s < e` (`LatticeChain.exists_layer_linearEquiv`), and the index is the cardinality of the
  layer (`LatticeChain.natCard_interval_eq_relIndex`).
- `IsPairIsomorphic.isIrreducible`: a pair isomorphic (`IsPairIsomorphic`) to an irreducible pair
  is irreducible.

## Transport to matrix groups

Here `Aut` is `Aut_F(F^N)` and `toAut` the isomorphism `Matrix.GeneralLinearGroup.toLin` from
`GL_N(F)`.

- `matrixSubgroup J`: the subgroup of `GL_N(F)` that `toAut` maps onto a subgroup `J` of `Aut`;
  `glSubgroupToAut_matrixSubgroup` says that `glSubgroupToAut` recovers `J`, and
  `matrixSubgroupHom J` is the induced isomorphism onto `J`, with `matrixSubgroupHom_symm`
  relating it to `glSubgroupToAutEquiv`.
- `liftedRep ρ`: a representation `ρ` of `J` on `W : Type`, transported to `matrixSubgroup J`
  on `ULift W` (to reach the universe of the target statement).
- `isSmooth_liftedRep`, `matrixSmoothRep ρ hρ`: if `ρ` is smooth (`IsSmoothRepresentation`:
  trivial on `J ∩ U^m(𝔄)` for some `𝔬_F`-lattice chain with hereditary order `𝔄` and some `m`),
  then `liftedRep ρ` is smooth (every vector is fixed by the elements of `matrixSubgroup J`
  that `toAut` maps into `U^m(𝔄)`, an open subgroup by `isOpen_unitFiltration` and continuity of
  `toLin`), and so defines a `SmoothRep` of `matrixSubgroup J`.
- `isPairIsomorphic_matrixSmoothRep`: `glRepresentationToAut (matrixSmoothRep ρ hρ)` is pair
  isomorphic to `ρ` (equivalence `ULift.moduleEquiv`).
- `containsType_matrixSmoothRep`: a nonzero `J`-intertwining map from `ρ` to `autRestrict π J`
  shows that `π` contains the type `matrixSmoothRep ρ hρ` (`ContainsType`).

## Heisenberg representation and `κ ⊗ ξ`

- `unitFiltration_subgroupOf_normal`: for a subgroup `H ≤ U(𝔄)`, `U^m(𝔄) ∩ H` is normal in `H`
  (`LatticeChain.inv_mul_mul_mem_unitFiltration`).
- `exists_heisenberg_constituent` (BK93 p. 268, first sentences of the proof for `m = 0`): if
  `π` contains the character `θ` of `H^1(β, 𝔄)` (`ContainsAutCharacter π θ`), then there are a
  finite-dimensional `J`-subrepresentation `X` of `autRestrict π J`, a representation `η` of
  `J^1` on `Fin dη → ℂ` with `IsHeisenbergRepresentation … θ η` (finite-dimensional, smooth,
  irreducible and containing `θ`), and a nonzero `J^1`-intertwining map `η → X`.
  Proof: let `v ≠ 0` be a `θ`-eigenvector. It is fixed by an open subgroup of `GL_N(F)`
  (smoothness of `π`), hence by some `U^m(𝔄)` (`exists_unitFiltration_subset_nhds`). The group
  `U^m(𝔄) ∩ J` is normal of finite index in `J`
  (`finiteIndex_unitFiltration_subgroupOf_simpleJGroup`), so the `J`-orbit span `X` of `v` is
  finite-dimensional and `U^m(𝔄) ∩ J` acts trivially on it
  (`Clifford.finiteDimensional_orbitSpan_of_fixed`, `Clifford.apply_eq_of_mem_orbitSpan`). The
  restriction of `X` to `J^1` is trivial on the normal finite-index subgroup `U^m(𝔄) ∩ J^1`,
  hence semisimple (`Clifford.isSemisimpleRepresentation_of_trivial_on_normal`), and
  `Clifford.exists_isAtom_eigen` gives an irreducible `J^1`-subrepresentation `Y` of `X`
  containing a `θ`-eigenvector `w`. Then `η` is `Y` in coordinates (`Clifford.coordinateRep`):
  it is trivial on `U^m(𝔄) ∩ J^1`, hence smooth, it is irreducible because `Y` is an atom
  (`FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom`), and the line through the
  coordinates of `w` gives the nonzero map from the character `θ` into `η`. The map `η → X` is
  the inclusion of `Y`.
- `exists_beta_tensor_intertwining` (BK93 p. 268): assume `BetaExtensionStatement` (BK93
  (5.2.2)(i)–(ii); only the existence part (i) is used) at the universes `uF, uF, 0, 0, 0`. If `S = [𝔄, n, 0, β]` is simple, `θ ∈ C(𝔄, 0, β)` and
  `π` contains `θ`, then there are `η` with `IsHeisenbergRepresentation … θ η`, a `β`-extension
  `κ` of `η` (`IsBetaExtension`), an irreducible representation `ξ` of `J` on `Fin dξ → ℂ`
  trivial on `J^1`, and a nonzero `J`-intertwining map `κ ⊗ ξ → autRestrict π J`.
  Proof: take `X`, `η` and `P : η → X` from `exists_heisenberg_constituent`, and `κ` from the
  premise. The restriction of `κ` to `J^1` is equivalent to `η`, and `J^1` is normal in `J`
  (`simpleJGroup_one_subgroupOf_normal`), so `P` gives a nonzero `J^1`-map from the restriction
  of `κ` to the finite-dimensional representation `X`. `Clifford.exists_irreducible_tensor_intertwining`
  then gives an irreducible `ξ`, trivial on `J^1`, and a nonzero `J`-map `κ ⊗ ξ → X`; composing
  with the inclusion of `X` gives the map into `π`.

## Layer data and smoothness

- `LatticeChain.finite_layer`: each layer `L_i / L_{i+1}` of a lattice chain over a local ring
  is finite-dimensional over the residue field, because the lattices are finitely generated
  (`LatticeChain.fg_lattice`).
- `LatticeChain.classCuspidalData b a hcusp`: the `CuspidalLayerData` of a lattice chain with
  layer bases `b` and factors the coordinate realizations of the cuspidal irreducible classes
  `a i`; `LatticeChain.classCuspidalData_inflation` says that its inflation is, by definition,
  `classTensor a` composed with the layer reduction `LatticeChain.layerReduction b`.
- `LatticeChain.isLayerReduction_comp`: let `U` be a group of `F`-linear automorphisms of `V`
  preserving the lattices of a lattice chain `𝓛` over a discrete valuation ring `O` (in a
  `K`-vector space `V`, for an `O`-algebra `K` that is a field), and `ε : U →* U(𝔄(𝓛))` such that `ε(u)` acts on `V` as `u` does. Then the
  layer reduction composed with `ε` is a layer reduction of `U` in the same bases
  (`IsLayerReduction`). This follows from `LatticeChain.equivFun_layerReduction`.
- `isSmoothRepresentation_tprod`: the tensor product of two smooth representations of a
  subgroup `J` of `Aut_F(F^N)` is smooth. If `ρ₁` is trivial on `J ∩ U^{m₁}(𝓛₁)` and `ρ₂` on
  `J ∩ U^{m₂}(𝓛₂)`, choose `k` with `U^k(𝓛₁) ⊆ U^{m₂}(𝓛₂)`
  (`exists_unitFiltration_le_unitFiltration`); then `ρ₁ ⊗ ρ₂` is trivial on
  `J ∩ U^{max(m₁, k)}(𝓛₁)`.
