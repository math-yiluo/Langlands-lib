# Three signs for characters on actual Levi-central torus points

This internal derivation combines the existing actual Levi-central torus
subgroup, its compact norm-kernel estimate and its uniformizer-lattice
logarithm. It introduces no additional literature assertion. The field has
arbitrary universe `u` and is a nonarchimedean local field with its given
valuation and topology. Characters take values in complex units and are
defined on the full abstract center of the literal rational-point Levi.

`simpleRootOrder_eq_zero_of_sq_eq_one` applies the integral order homomorphism
to the square-one identity for a simple-root value. Its order is an integer
killed by two and hence zero. For a split torus,
`exists_leviCentralLatticeRepresentative` uses the published common-uniformizer
section to represent any torus point modulo the common rational-character norm
kernel. Square-one values on the selected simple roots make the representative
belong to the integral selected-root annihilator. The resulting lattice
pairings equal all the original rational-character orders.

For the complement of one simple root `α`,
`exists_leviCentralCocharacter_omittedRoot_pos` extracts a cocharacter in this
annihilator with strictly positive `α` pairing from the explicitly supplied
standard-cocharacter existence premise. `leviCentralOmittedRootLogSlope` chooses
such a cocharacter and divides its character logarithm by its positive
omitted-root pairing. The logarithm uses the normalization
`-log ‖χ‖ / log q`, where `q` is the residue cardinality. No sign or nonvanishing
condition is imposed on this real slope.

The topological arguments use the canonical rational-point topology on the
affine torus and the canonical ambient point topology, with explicit Hausdorff
topological-group assumptions on the latter.
`exists_leviCentralLatticeCharacterLog_eq` assumes an open character kernel.
The quotient of a Levi-central torus point by its uniformizer representative
lies both in the Levi-central subgroup and in the torus common norm kernel.
The existing compact-kernel estimate gives modulus one on that quotient, so
its logarithm is zero. Multiplicativity therefore identifies the logarithm
at the original point with the lattice logarithm.

`exists_leviCentralTorusCharacterLog_factor` also assumes square-one values
on all selected roots, full-index standard-cocharacter existence, equality of
the full-index Levi with the ambient group, containment of the full ambient
center in the selected Levi, and unit modulus on that ambient center. It
combines the transfer with the existing corank-one lattice factorization.
At every Levi-central torus point, the logarithm equals one real slope times
the integral order of the omitted-root value.

`simpleRootOrder_pos_iff_valuation_lt_one` identifies positive source-order
with the original strict negative valuation chamber. Given any such
factorization, `leviCentralTorusCharacter_norm_trichotomy_of_factor` splits
on the sign of the slope. A positive slope gives character modulus strictly
less than one at every point with omitted-root valuation less than one; a
negative slope gives modulus strictly greater than one there; a zero slope
gives modulus one on every Levi-central torus point. The conversion uses
`‖χ‖ = q ^ (-logarithm)` and `q > 1`. These alternatives are a disjunction;
the theorem does not assert that the strict test set is nonempty.

The two `_of_rationalData` wrappers retain the original normalizer and
centralizer comparisons, actual Coxeter system, standard-cocharacter
statement, connected reductivity, maximal split torus, relative root system,
generic cocharacter, root-length comparison and actual Levi Weyl
identification. These premises supply the preceding square-one, full-index
and cocharacter hypotheses. The character's open kernel and unit modulus on
the ambient center remain explicit inputs. The last theorem expresses the
three alternatives using an original torus point `t` and a full Levi-center
point `z` with the same literal ambient point. Its strict tests are exactly
`IsNoncentralNegativeTorusPoint i ν t`.

The zero alternative proves modulus one only at full Levi-center points that
come from torus points. This module does not identify those points with the
whole abstract Levi center, establish full inducing unitarity, construct
Jacquet factors, prove a square-integrability criterion, or prove
`RationalRankOneSelfAssociationStatement`.
