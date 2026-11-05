# Integer lattice coordinate independence of actual orbit forms

Author: Worker 200.

This derived comparison combines Waldspurger, *La formule de Plancherel
pour les groupes p-adiques (d'après Harish-Chandra)* (2003), V.2
(printed p.293, PDF p.59), VI.1 (printed pp.295–296, PDF pp.61–62),
and VI.3 (printed p.302, PDF p.68). Those passages supply the
inverse-formal-degree fiber form, coherent smooth sections on actual
inducing representatives, and the locally preserved orbit measure.
Coordinate independence of the implemented integral form is an internal
comparison, rather than a separate theorem asserted in the source.

The coordinate changes are exactly the finite integer lattice basis
changes covered by `ProductInducedOrbitCoordinates`. The input
`e : unitaryUnramifiedCharacters ν ≃* (J → Circle)` is replaced by
`e' = T_bc ∘ e`, where `b : Basis J ℤ L` and `c : Basis J' ℤ L`
are finite bases of the same integer module and
`T_bc = finiteTorusBasisChange b c` reconstructs the same lattice
character in the other basis. The imported
`productInducedSmoothOrbitRebaseEquiv` goes from the space defined using
`e'` to the space defined using `e`. It fixes the value at every actual
inducing representative. The two coordinate-index universes, the lattice
universe, and the group, character-index and inducing-carrier universes
are independent.

`continuous_rebaseUnitaryTorusCoordinates` composes continuity of the
integer monomial basis change with continuity of the forward coordinate
map `e`. It adds no inverse-continuity assumption.

For `map_finiteTorusBasisChange_unitaryOrbitParameterMeasure`, fix one
canonical irreducible admissible smooth complex inducing representation
`π` of the actual Levi subgroup `M`, a normal central subgroup `C`,
and a quotient Haar measure `μ` for which `π` is square integrable.
The theorem proves

\[
 (T_{bc})_*\bigl(|S|^{-1}e_*\eta\bigr)
   = |S|^{-1}e'_*\eta ,
\]

where `S` is the same actual discrete-series class stabilizer and `η`
is the supplied unitary character measure. The proof commutes
pushforward with scalar multiplication and composes the two measurable
maps. It needs continuity of `e`; it needs no finiteness, invariance,
finite mass or probability normalization of `η`. The displayed formula
uses the existing `ENNReal` inverse-cardinality definition, and has its
finite-fiber interpretation when the actual stabilizer is finite.

The pairing and core comparisons retain all hypotheses of
`ProductInducedOrbitForm`: local compactness, second countability and
Borel structures; the actual semidirect decomposition `P = M U` with
closed `P` and `U`; compact open `K` and `G = P K`; ambient
unimodularity and the full parabolic modulus identity; compact-open
cofinality in `M`; inversion invariance of the same quotient Haar
measure `μ`; and continuity of the positive characters and Levi
projection. No inducing positive form, coefficient topology or
irreducibility of parabolic induction is supplied.

`unitaryOrbitProductPairing_rebase` identifies the descended scalar
pairing at every actual discrete-series class. The auxiliary actual
representative chosen in the definition is independent of coordinates.
Both sections have the same values there, and the same canonical
inverse-degree form evaluates those values. The equality is
definitional. This pointwise theorem needs no finite central quotient,
coordinate continuity or character measure.

The remaining theorems assume the displayed finite central norm quotient
`Finite (M / (commonNormKernel ν ⊔ C))`. The imported stabilizer
finiteness theorem gives the actual finite stabilizer used by
`discreteSeriesOrbitMeasure`.
`integral_unitaryOrbitProductPairing_rebase` integrates the pointwise
identity against this same actual orbit measure. The equality itself
needs no finite mass or coordinate continuity. For finite `η` and
continuous `e`, actual Bochner convergence on both sides follows from
the imported `integrable_unitaryOrbitProductPairing` and the proved
continuity of `e'`.

Finally, `productInducedSmoothOrbitRebaseEquiv_inner` assumes continuous
`e`, finite `η` and positivity of `η` on nonempty open sets. It
expresses each entire positive core as its convergent actual orbit
integral and uses the preceding integral identity. Thus the existing
linear equivalence preserves the full Hermitian form. Character
invariance is unnecessary for this comparison: the underlying actual
orbit and its measure are identical. If `η` is invariant, the imported
orbit-measure theory also gives the source's local measure convention.
Its original scale and the inverse actual stabilizer-cardinality factor
are retained throughout.

`productInducedSmoothOrbitRebaseIsometry` packages this comparison as a
linear isometric equivalence. Its two norms are constructed from the
respective actual orbit-integral cores, with no preexisting coefficient
norm supplied. Norm preservation applies the full inner-product identity
to a section paired with itself and takes the square root of its real
part. The application lemma confirms that its underlying map still fixes
the value at every actual inducing representative.

This comparison covers finite integer lattice basis changes of the
supplied character coordinates. Arbitrary abstract torus equivalences,
actual rational-point realization of the source character measure,
density-weighted global forms, spectral density, action invariance,
wave packets, completions and Plancherel inversion remain separate
obligations. No whole-task completion condition is claimed.
