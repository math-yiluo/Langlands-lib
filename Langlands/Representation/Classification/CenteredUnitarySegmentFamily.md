# Centered unitary segment parameters for Hermitian block families

This internal adapter retains each supplied square-integrable block and its
original strong segment-head description. It combines the centered-unitary
parametrization with published special-parameter uniqueness and the Hermitian
involution construction. The field and carrier universes are independent;
actual block carriers remain in `Type (max uF uV)` with the supplied topology.

The imported `SquareIntegrableSegmentParameter F T n π` stores an original segment, the
explicit equality of its degree with `n`, an actual unitarizable supercuspidal
representative of its midpoint-twisted base, and the strong head relation on
`π` transported by that same degree equality. The imported choice
`squareIntegrableSegmentParameter` obtains these fields from the centered
parametrization on the supplied irreducible square-integrable action. It
neither replaces that action nor chooses a representative of its class.

`segment_eq_of_iso` starts with two such data and an actual isomorphism of the
supplied blocks after a rank equality. Equality elimination transports that
isomorphism to the two original segment degrees. The published
`segmentSpecialParameterUniqueness` then identifies the complete segments.
This includes their base cuspidal classes, ranks and positive lengths.
`centeredHead` applies actual real-twist compatibility to the stored head,
so the positive midpoint twist is a strong head of the midpoint-twisted
segment with the stored actual unitarizable base.

`IsUnitarySquareIntegrableBlockFamily.segmentParameters` applies the choice to
every actual block using the positive ranks in the block shape. The final
`IsUnitaryGenericDatum.exists_symmetricSegmentParameters` works for any such
chosen parameters. The existing Hermitian symmetry supplies an involutive
rank-preserving matching and actual isomorphisms between matched blocks.
Parameter uniqueness identifies each matched pair of original segments.
Applying `length - 1` to that equality proves length preservation. Together
with the same involution, opposite real exponents and the original strict
bounds, these facts give the exact numerical `SymmetricBlockData` used by
the Appendix pole argument. The block isomorphisms are retained explicitly.

The provenance is an internal derivation from the named published
parameter-uniqueness, twist-compatibility and Hermitian-involution results,
together with the supplied centered-parametrization adapter. No additional
classification theorem or factor identity is assumed. This contribution
supplies actual segment choices and numerical symmetry; it does not discharge
the analytic base-factor, epsilon-unit or arithmetic gamma-zero hypotheses,
and it does not prove the associated-pair induction theorem.
