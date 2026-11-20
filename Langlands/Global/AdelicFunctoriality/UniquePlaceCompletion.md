# Galois comparison at a unique finite place

These lemmas supply the arithmetic comparison for the prime-degree step of Harris (1998), Proposition 4.8. The two number fields may have independent universes. No cyclicity or prime-degree hypothesis is needed for the comparison.

`finitePlaceEquiv_eq_of_unique` applies the preservation of lying over under a relative automorphism. The unique-place assumption identifies the pullback finite place with the original finite place. `localDegree_eq_global_of_unique` applies the sum formula for ramification indices times inertia degrees to the singleton of finite places above the base place. The summand agrees with the local degree by `localDegree_eq`.

`uniquePlaceCompletionAutEquiv` uses the normal restriction of local automorphisms to the global upstairs field. This is the construction of `Langlands.ClassField.Global.FundamentalClass.decompositionHom` with independent field universes. The equalizer of two automorphisms with the same restriction contains the image of the global field, so it is the whole completed field by `subalgebra_eq_top_of_algebraMap_mem`. Both extensions are Galois and their degrees agree, so the injective restriction is bijective. The inverse yields extension to the completion, and `uniquePlaceCompletionAutEquiv_algebraMap` verifies the action on every element of the global field.

`exists_pow_of_completionAut_ne_one` pulls a nonidentity automorphism back through this equivalence and writes it as a power of the supplied global generator. The order of the generator is the cardinality of the global Galois group, hence the global degree. The bounded-power description of the generated subgroup gives an exponent below that degree, and exponent zero would give the identity.
