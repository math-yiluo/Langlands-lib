# Sections of smooth schemes over local nil thickenings

Worker 869.

This internal consequence of smooth algebra lifting uses no group scheme
classification. `SectionLiftingProperty` expresses exact extension of a
specified point over an algebra to a section over the original base.

For a smooth morphism `X → Spec R`, a surjective algebra map `R → C` with
nil kernel, and a local target ring `C`, `exists_lift_of_nil_kernel` lifts
every `C`-point over the base to an `R`-section, preserving its reduction.
The original ring `R` need not be local in this version.

The proof chooses an affine open of `X` containing the image of the
closed point of `Spec C`. Locality ensures that the entire point factors
through this open. Its coordinate ring is a smooth `R`-algebra. The
algebraic nil-kernel lifting lemma supplies a map from that coordinate
ring to `R`; taking spectra produces the required section. The two
equalities in the conclusion follow from the algebra-map identities.

`exists_lift_of_nil_ideal` applies this to `R/I` for any ideal contained
in the nilradical of a local ring `R`. Such an ideal is proper, so the
quotient is again a local ring. There is no noetherian, henselian,
characteristic or uniform nilpotence assumption.
