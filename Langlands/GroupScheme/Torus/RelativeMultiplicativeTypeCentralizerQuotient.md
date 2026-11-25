# Smooth quasi-affine quotients by multiplicative-type centralizers

For a smooth affine group scheme `G` over any scheme `S` and a closed subgroup
`i : H → G` of multiplicative type, every supplied representative `z : Z → G`
of its all-test centralizer has an actual homogeneous quotient. The quotient
is smooth over `S`, and its preimage over every affine open of `S` is
quasi-affine. `relativeMultiplicativeTypeCentralizerQuotient` chooses such a
quotient. Multiplicative type uses the published fppf-local diagonalizability
condition for finitely generated character groups, including nonsmooth finite
diagonalizable groups.

These are derived constructions from the published ring-level centralizer
quotient and the general sheaf descent machinery. Over a spectrum, a supplied
diagonalizable group is identified with its actual group-algebra model. Source
isomorphism preserves the subgroup range and therefore the centralizer. The
ring-level `diagonalizableCentralizer_exists_quasiAffine_quotient_overRing`
supplies a quotient. Its conclusion on the top affine base open, followed by
the canonical top-open isomorphism, proves quasi-affineness of the whole model.

Over an affine base, the multiplicative-type splitting fppf cover is open on
underlying spaces. Compactness of the base and
`QuasiCompactCover.exists_hom` refine it by a finite affine fppf cover whose
members are actual spectra. The standard comparison of iterated group-scheme
base changes preserves diagonalizability on these charts. Base change of the
supplied centralizer represents each local centralizer. Thus the spectrum
construction gives actual quasi-affine local homogeneous quotients.
`quotientOfFiniteAffineCover` descends these to the affine base. Smoothness of
`Z` is supplied by `relativeMultiplicativeTypeCentralizer_smooth`, and its
monomorphism follows from the representing property.

For general `S`, the affine construction applies after each affine open base
change. `HomogeneousQuotientSheaf.exists_quotient_of_affine_local_models` glues
them as full representations of the canonical coset fppf sheaf and recovers the
actual quotient data, with exact right-coset fibers on all scheme tests. It also
supplies smoothness and the asserted preimage condition for every affine base
open. This proves the centralizer-quotient clause of
`RelativeMultiplicativeTypeQuotientStatement`, the statement this module serves;
normalizer quotients and the Weyl-group quotient are separate obligations.
