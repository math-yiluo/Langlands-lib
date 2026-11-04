# Proof of detection through actual rational Levi points

`Langlands.rationalLeviJacquetFixedVectorDetection` proves the internal supporting statement of the same name. It retains every structural and coefficient premise and the independent field and carrier universes.

The normalized Jacquet bridge gives generation of `JA` by vectors fixed by `K ∩ M`, actual occurrence of `JD` as a subquotient of `JA`, and lifting of a nonzero fixed vector from `JD` to `D`. Actual subquotient transitivity puts the given irreducible `E` inside `JA`. None of these steps changes the normalized Jacquet action.

Pull back `JA` and `E` through the canonical group homeomorphism from the actual Levi scheme's rational points to the literal Levi subgroup `M`. Pullback preserves actual subquotients and irreducibility. The group-equivalence generation theorem transports generation to the inverse image of `K ∩ M`; pulling this subgroup back along the inverse equivalence recovers exactly `K ∩ M`. Closedness of `M` makes `K ∩ M` compact, and the point homeomorphism preserves this compactness.

The rational norm-kernel detector applies to those pulled-back representations, the assumed finite-restriction proposition, and the supplied compact coefficients on the intrinsic actual norm kernel. It returns a nonzero vector fixed by that inverse-image subgroup. The same-carrier fixed-space identity makes this a nonzero `K ∩ M`-fixed vector of the original `E`. Compact-open exactness lifts it to `JD`, and the original normalized Jacquet bridge lifts it to a nonzero `K`-fixed vector of `D`.

This is an internal assembly proof. Group-equivalence generation is implemented by Worker 1210; the present rational and normalized Jacquet assembly is implemented by Worker 189. The finite-restriction, cuspidal compactness and geometric premises remain unproved by this unit, so it does not complete the Howe task.
