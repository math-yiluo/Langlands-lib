# Integral opposite factors exclude radical reduction

`IntegralOppositeNecessityStatement` and its proof
`integralOppositeNecessity` give the necessity implication for integral
opposite factors at arbitrary universe `u`. The pointwise interface is
`IntegralTorusData.not_mem_positivePoints_of_integral_oppositeFactors`.

Let `R` be a commutative local domain with specified fraction field `K`,
let `G` be a connected reductive group over `K`, and let `i : S → G`
be a maximal split torus. Supply relative-component model data `D`, an
integral split torus `T` with its specified generic identification, and an
actual special-fibre quotient `Q` satisfying `Q.IsReductiveQuotient`.
For a nonzero character `a` and a nonidentity point `g ∈ U_a(K)`, suppose
`g', g'' ∈ U_{-a}(K)` and `g' * g * g''` normalizes `S`. If both opposite
factors belong to `D.neutral.integralPoints`, then `g ∉ Q.positivePoints`.
Here `Q.positivePoints` is the actual preimage of the supplied unipotent
radical under reduction of integral sections.

The model, torus and quotient are supplied data. The conclusion requires
neither a separate integrality assumption on `g` nor closedness of the
integral torus inclusion: assuming membership in `Q.positivePoints`
provides an integral section with the necessary radical reduction.
No Henselianity, completeness, residue-field perfectness or algebraic
closedness assumption occurs.

The proof assumes such radical membership and chooses integral sections
for all three factors. It chooses a generic cocharacter `ν` of `S` with
positive integer pairing against `a` and lifts it to an actual integral
cocharacter using `exists_integralCocharacter_compatible`. That lemma
preserves both the specified ambient generic morphism and all canonical
special-fibre character pairings. Thus the reductions of the two opposite
factors lie in the opposite dynamic unipotent of the quotient.

The middle section maps to the identity in the quotient, because the
quotient kernel is the supplied radical. The quotient reduction of the
triple product consequently lies in that same opposite dynamic
unipotent. The theorem
`SpecialFibreQuotientData.generic_oppositeCell_of_quotient_unipotent`
then gives an opposite-unipotent/parabolic factorization of its actual
generic image. This step uses the reduction of the specified section;
it requires no surjectivity on arbitrary rational points of the quotient.

Genericity of `ν` identifies its dynamic centralizer with the centralizer
of the whole torus. Applying
`normalizer_mem_centralizer_of_generic_oppositeCell` to the normalizing
triple product forces it to centralize `S`, so its Weyl action is the
identity. On the other hand, the actual opposite-pair theorem
`RelativeRoot.IsOppositeFactorPair.weylAction_eq_neg` says that this
product sends `a` to `-a`. Pairing with `ν` contradicts the strictly
positive integer pairing of `a`.

This is an internal composition of the Library's generic cocharacter,
root reduction, quotient-cell, centralizer and opposite-pair interfaces.
It supplies one direction of `IntegralOppositeFactorsStatement`; it
does not assert the converse or the final unramified facet root datum.
