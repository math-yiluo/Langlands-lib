# Admissibility of the actual native stabilizer coefficient quotient

This internal unit proves admissibility of the native stabilizer coefficient quotient attached to each supplied actual `GeometricLemmaIntersectionDatum D`. It combines the constructed proper-source vanishing and surviving-section admissibility with the published native coefficient quotient transport. It does not assume admissibility of the quotient.

For source and target parabolics `p` and `q`, with target Levi `lQ`, write

- `H = orbitStabilizer (pointImage p) (pointImage q) z⁻¹` for the full original orbit stabilizer;
- `dQ` for the original represented target semidirect decomposition;
- `NQH = dQ.projection.ker.comap H.subtype` for its kernel intersection inside `H`;
- `T = pointImage (lQ ≫ q) ⊓ (pointImage p).map (MulAut.conj z⁻¹).toMonoidHom` for the target-intersection parabolic on its original ambient point carrier.

The kernel `NQH` is normal in `H` because it is the preimage of a homomorphism kernel. For an arbitrary native `B`-linear representation `ρ` of `H`, `D.targetStabilizerCoinvariantRepresentation ρ` is exactly

`(ρ.toCoinvariants NQH).comp D.targetParabolicPointsToStabilizer`.

Thus the quotient carrier is the original native `Jacquet.Coinvariants ρ NQH`, and `T` acts through the original target-intersection section into the same stabilizer. No new quotient action or abstract replacement module is supplied. `targetStabilizerCoinvariantMap` is the original canonical quotient map, regarded as an intertwiner from the section restriction of `ρ`. Its representative formula is definitional, and its surjectivity follows from the canonical quotient's surjectivity.

`isClosed_targetIntersectionPoints` derives closedness of `T` from the datum's actual represented target-parabolic identity. The composite `D.q' ≫ lQ ≫ q` is a closed subgroup, and its literal rational-point image is exactly `T`. Hence `T`, with its inherited topology, is locally compact. It inherits the ambient nonarchimedean group structure, so the compact-open subgroup basis proves `targetIntersection_compactOpenCofinal` for every open subgroup of `T`. This cofinality is derived, rather than inserted as an auxiliary hypothesis.

Over a Noetherian commutative complex algebra `B`, `targetStabilizerCoinvariantRepresentation_isAdmissible` applies the published `Langlands.isAdmissible_of_surjective_coefficients` to this exact quotient intertwiner. Consequently, admissibility of the original section coefficient descends to the native stabilizer-kernel quotient. The imported transport theorem uses complex compact invariant lifts after restriction of scalars; its construction and conclusion remain native and linear over `B`. Callers install no extra complex module or scalar-tower structure.

The actual universal specialization retains the complete original `RegularAlgebra r` and uses

`ρ = (inducingRepresentation r h hU σ).comp (stabilizerToInducing (pointImage p) (pointImage q) z⁻¹)`.

This is the original fully positively normalized inducing covariance on the original stabilizer, with no change of coefficient algebra or norm family. The composite of the stabilizer inclusion with the target-intersection section is definitionally the existing `D.targetParabolicPointsToSource`. The preceding theorem `universalTargetIntersectionCoefficient_isAdmissible` therefore supplies the actual source admissibility in the full-source branch. The Noetherian property of `RegularAlgebra r` is already proved. This yields `universalTargetStabilizerCoinvariant_isAdmissible_of_full`.

`universalTargetStabilizerCoinvariant_isAdmissible` handles every supplied intersection datum. If the source intersection parabolic has full all-test range, it uses the surviving-branch theorem. Otherwise it is proper, and `universalStabilizerCoinvariants_subsingleton` makes this same original native quotient zero using supercuspidality of the original complex representation. Every vector in the zero module is fixed by the open full group, and each fixed module is finite. The resulting conclusion requires original complex admissibility and supercuspidality; it does not need irreducibility.

The generic coefficient algebra, field and group schemes, and coefficient carrier use independent universes `uR`, `u` and `uV`. The universal specialization preserves the independent original field/group and inducing-carrier universes `u` and `uV`. The vector-class and surjectivity formulas omit unused ambient topology hypotheses; closedness omits unused ambient local compactness and nonarchimedean assumptions.

The provenance is internal. The new construction consists of the original native kernel quotient and section restriction; its proof uses actual closedness and compact-open cofinality, the published native quotient transport, and the separately implemented proper and surviving coefficient results. Adapted intersection-datum existence, finite ordered rational orbit geometry, identifying the compact orbit-induction Jacquet quotient through induction in stages, the associated measure hypotheses and the final global fixed-module finiteness proof remain separate obligations.
