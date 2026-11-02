# Etale local surjectivity of an actual smooth Picard atlas

This internal consequence concerns actual schemes `X → S`, an actual family
of line bundles `L` on the pullback to `U`, and
`IsSmoothSurjectivePresentation f L`. It proves local surjectivity on the
full big etale site of `S`, in every universe `u`.

`classFamilyMap_isLocallySurjective` covers every section of the unsheafified
isomorphism-class presheaf. Quotient induction supplies an actual line bundle
representative `M`. The presentation represents the actual point fibre above
`M` by a smooth surjective scheme `P` over the test scheme `T`. Evaluating its
representing isomorphism on the identity of `P` gives a map to `U` and an
actual isomorphism from the pulled-back family to the pullback of `M`.
Consequently the restricted classes coincide over `P`.

The published smooth-surjection local-sections construction, applied through
`isLocallySurjective_smooth_schemeYoneda_map`, makes the image sieve of
`P → T` covering. For each arrow lifting through `P`, the proof pulls back
the actual bundle isomorphism along its lift, using the pseudofunctor's
composition comparisons. Its isomorphism class puts the arrow inside the
image sieve of the class of `M`. Closure under enlargement therefore proves
the required local surjectivity.

`etaleFamilyMap_isLocallySurjective` composes this map with the etale
sheafification unit, which is locally surjective by Mathlib. It thus covers
every section of the etale class sheaf: its argument does not choose a global
line bundle representative of a sheaf section.
`ordinaryEtaleFamilyMap_isLocallySurjective` then uses the published natural
comparison isomorphism to obtain the same assertion for ordinary etale
Picard classes.

`locallySurjectiveEtaleFamilyMap` constructs the actual etale family map
bundled with its proved local-surjectivity property. Its value is the pair
of `etaleFamilyMap f L` and `etaleFamilyMap_isLocallySurjective f L hL`.
The first projection is therefore definitionally the original family map.
This construction requires precisely the same smooth surjective presentation
hypothesis and retains the full site and every sheaf section.

The provenance is internal: the result follows from the published actual
point-fibre presentation, quotient-class maps, their sheaf comparisons, and
Worker 766's smooth-surjective etale local-sections construction. No new
literature assertion is introduced. The result supplies the local-surjectivity
input for the smooth-automorphism quotient construction; it does not assert
representability of that quotient or prove the final quotient theorem.
