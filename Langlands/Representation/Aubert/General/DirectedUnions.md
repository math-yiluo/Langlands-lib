# Actual normalized functors and directed unions

This internal derived helper develops the passage from a directed covering family
of actual invariant images to individual smooth induced functions. It does not
assert support compatibility or prove the rational support-stability target.

`Induction.smoothInducedLiftOfEvalMemRange` selects an actual lifted function;
`smoothInducedMap_liftOfEvalMemRange` proves its postcomposition is the original
function. The underlying injective coefficient-map lemma chooses a preimage for each function value.
Injectivity transfers covariance and the original open right stabilizer to these
preimages. Compactness of the left quotient gives finitely many double coset
representatives for that stabilizer. Directedness puts their finitely many values
in one coefficient image. Covariance, right invariance and image stability put all
other values in that same image, and the lifting lemma applies.

The normalized functor statement uses the actual inflated and half-modulus-twisted
coefficient map. The compact-quotient hypothesis is explicit in this intermediate
result and is not discharged for the rational-point target here. There is no
finite length, admissibility or finite dimensionality assumption.

Dependencies are `Induction.smoothFunctionOf`, `smoothInduced_smooth`,
`eval_covariant`, `eval_mul_of_mem_fixedVectors` and
`exists_finset_doubleCoset_cover`, and the actual normalized functors of
`Aubert.General.Parabolic`. The construction is derived from these definitions;
no separate literature assertion is imported as a proof.

The actual normalized Jacquet functor sends a covering family of coefficient
images to a covering family: each coinvariant class has a vector representative.
Containment of original images gives containment of their Jacquet images by the
same representative argument. These two observations do not use compactness,
directedness or injectivity. With `IsLimitOfCompactSubgroups U`,
`Jacquet.Localization.map_injective_of_smooth` proves injectivity of the Jacquet
maps. The normalized twists leave the underlying quotient maps unchanged.
Applying the induction lemma to this family proves that each vector of the actual
composite `inductionJacquetFunctor` comes from one original stage. The composite
uses the existing saturated carrier universe, with independent group, carrier and
index universes. The additional dependencies are the actual localization quotient
map `mk`, `mk_surjective`, and the cited injectivity theorem. No classification,
character independence, geometric lemma or adjointness result is used.

These theorems justify passage along directed covers once support compatibility
on the stages is known. They do not supply that compatibility, reduce arbitrary
finitely generated supported objects to irreducibles, or prove compactness or
compact-limit properties for the actual rational-point families.
