# From a level line in a Whittaker model to the conductor clauses

This internal auxiliary shows how the newvector-conductor clause and the
dimension-one clause of the host's `ConductorExponentStatement` follow from
conditions on one Whittaker model. Every fixed vector at a level below `m`
must be zero, and every level-`m` fixed vector must be a multiple of one
level-`m` vector. The unit also proves that Jacquet's essential vector is
never zero. It does not prove the level conditions.

## A line of level-fixed vectors

Let `F` be a field with `ValuativeRel F`. Let `ρ` be a complex representation
of the actual `GeneralLinearGroup (Fin (n + 1)) F` on a carrier `V` of
arbitrary universe. `levelFixedVectors ρ a` is the published submodule of
vectors fixed by the last-row congruence subgroup `levelSubgroup F n a`.

`IsLevelLine ρ m w` is the Prop-valued conjunction of three conditions:
- `w ∈ levelFixedVectors ρ m`;
- every vector of `levelFixedVectors ρ b` with `b < m` is zero;
- every vector of `levelFixedVectors ρ m` is `C • w` for some complex `C`.

It does not require `w ≠ 0`. `isNewvectorConductor_and_finrank_of_line`
assumes `w ≠ 0` and `IsLevelLine ρ m w`. It proves the published
`IsNewvectorConductor ρ m` and `Module.finrank ℂ (levelFixedVectors ρ m) = 1`.
The level-`m` space equals the span of `w`, so its dimension is one because
`w ≠ 0`. The same `w` shows that this space is nonzero, and the lower spaces
are zero by hypothesis.

`finrank_levelFixedVectors_of_equiv` proves that the dimension of a
level-fixed space is unchanged along a representation equivalence. It uses
the published linear equivalence `fixedVectorsEquiv` of fixed spaces.
`isNewvectorConductor_and_finrank_of_equiv` combines this with the published
`isNewvectorConductor_iff_of_equiv`, so both clauses pass from one
representation to an equivalent one. The two carriers may lie in different
universes.

## From the Whittaker model to the representation

Now let `F` also carry a topology. Let `π` be an irreducible representation of
`GeneralLinear (n + 1) F` and `ℓ` a nonzero standard Whittaker functional for
`ψ`. The published `glModelEquiv ψ n π ℓ hℓ` is the representation
equivalence between `π` and the right-translation representation
`modelRepresentation π ℓ` on the coefficient model. Its target carrier lies
in the field's universe. `isNewvectorConductor_and_finrank_of_model_line`
takes a nonzero model vector `w` with
`IsLevelLine (modelRepresentation π ℓ) m w`. It concludes `IsNewvectorConductor π m` and
`Module.finrank ℂ (levelFixedVectors π m) = 1` for `π` itself, on its
original carrier.

## Essential vectors are nonzero

These results assume a nonarchimedean local field and Jacquet's
normalizations `h : IsJacquetNormalization q ψ abv ϖ μ`.

- `IsJacquetNormalization.one_lt_q` proves `1 < q`. The field
  `h.residueCardinality` identifies `q` with the cardinality of the actual
  residue field, which is finite and nontrivial.
- `corankOneIntegral_zero_left` proves that the published corank-one integral
  vanishes when its Whittaker function is zero. The integrand vanishes at
  every coset representative.
- `essentialFactor_ne_zero` proves that the published rational function
  `essentialFactor P x = ∏ i, (P(x_i X))⁻¹` is nonzero when `P` has constant
  term one. Each `P(x_i X)` has constant term `P(0) = 1`, so it is a nonzero
  polynomial. Its image in the fraction field and the inverse of that image
  are therefore nonzero.

`IsEssentialVector.ne_zero` proves that an essential vector `w` of the host's
published `IsEssentialVector h π ℓ w` is not zero. Suppose `w = 0`. Evaluate
the essential identity at the parameter `x = (1, ..., 1)`. Its integral is
then the zero function. That function has the zero rational continuation.
The published uniqueness `HasRationalContinuation.unique`, which needs
`1 < q`, would force `essentialFactor P x = 0`. Here `P` is the standard
L-polynomial witnessed in the essential predicate. Its constant term is one
by the published `IsNormalizedGenerator`. This contradicts
`essentialFactor_ne_zero`. The argument uses no genericity and no
nonvanishing of `ℓ`.

`isNewvectorConductor_and_finrank_of_essential` packages these results for
the host's setting. Here `π` is a generic representation of
`GeneralLinear ((n + 1) + 1) F`, `ℓ` is nonzero, `w` is essential and
`IsLevelLine (modelRepresentation π ℓ) m w` holds. The conclusion is `IsNewvectorConductor π m` together with
`Module.finrank ℂ (levelFixedVectors π m) = 1`. Irreducibility comes from the
first clause of `IsGeneric`.

## Provenance and remaining obligations

The unit has internal provenance. Its steps are elementary linear algebra,
the published fixed-space and conductor transport under representation
equivalences, the published model equivalence, finiteness of the residue
field, evaluation of polynomials at zero, and the published uniqueness of
rational continuation. The conditions of `IsLevelLine` correspond to the
conclusions of Jacquet, Piatetski-Shapiro and Shalika, *Conducteur des
représentations du groupe linéaire*, Math. Ann. 256 (1981), proof of
Theorem (5.1), printed pages 213–214. That proof shows that a nonzero vector of
`𝒲(π; ψ)` fixed by `K(u)` forces `u ≥ m`, and that for `u = m` it is a
multiple of the essential vector. No result of that source is asserted here.

The unit does not prove `IsLevelLine` for any vector. In particular it
proves neither the level-`m` fixedness of the essential vector nor the
vanishing at lower levels nor the line condition. It also proves neither the existence of the essential
vector nor that of the epsilon factor, and it does not identify `m` with an
epsilon exponent. The rank-one case of `ConductorExponentStatement` is not
treated here. The unit is a conditional component of the conductor argument
and does not prove `EssentialConductorStatement`.
