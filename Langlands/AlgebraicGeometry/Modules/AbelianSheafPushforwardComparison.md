# Actual module/sheaf comparison across a closed-immersion pushforward

Let `h : X ⟶ Y` be a morphism of actual schemes in arbitrary universe `u`.
`pushforwardForgetIso h` is the canonical natural isomorphism

`Scheme.Modules.pushforward h ⋙ toAbSheaf Y ≅ toAbSheaf X ⋙ TopCat.Sheaf.pushforward AddCommGrpCat h.base`.

Its components are identities on the actual underlying abelian sheaves.
`abelianPushforwardSectionsIso h` similarly identifies actual global
sections of an abelian-sheaf pushforward with actual global sections on `X`.
`underlyingPushforwardSectionsIso h` gives the corresponding isomorphism for
actual module global sections after forgetting their different scalar rings.
All three have identity components on the underlying global sections and
require no closed-immersion or topological-isomorphism assumption.

For the remaining results assume `IsClosedImmersion h` and `IsIso h.base`.
The latter says that the actual underlying map of topological spaces is an
isomorphism. Pushforward of actual abelian sheaves along this map is an
equivalence, obtained from `UnitSheafPushforward.sheafPushforwardEquivalence`
for `asIso h.base`. Hence it preserves homology.
`isZero_rightDerived_abelianPushforward` applies the existing vanishing
result for homology-preserving functors. This lemma needs only the
topological-isomorphism assumption, and omits the closed-immersion assumption.

`twoStepComparison_pushforward` proves equality of the following two
canonical degree-`n` comparison routes for every actual module `M` on `X`:

1. Start with right-derived underlying module global sections on `X`,
   compare with right-derived underlying module global sections of `h_*M`
   on `Y`, then forget module scalars on `Y` and apply right-derived abelian
   global sections. Finally apply the derived image of
   `pushforwardForgetIso h` at `M`.
2. First forget module scalars on `X`, then use abelian-sheaf pushforward
   and its actual sections comparison to reach the same right-derived
   abelian global sections object on `Y`.

The statement uses the existing canonical `compComparison` maps, packaged
by `twoStepComparison`. It retains the specified forgetting isomorphism
on the final object. For module pushforward, the required higher-direct-image
vanishing is the published closed-immersion theorem. For module forgetting,
it is the published exact-forgetting vanishing theorem. For abelian-sheaf
pushforward, it is the vanishing lemma just described.

The proof uses the existing preservation of epimorphisms and kernels by
closed-immersion module pushforward to obtain preservation of homology.
The two forgetting functors and the abelian-sheaf equivalence also preserve
homology. Apply `twoStepComparison_factorization` to these actual functors.
Its compatibility condition is identity on actual global sections, so
componentwise reflexivity proves it. No quasi-coherence, flatness,
properness, or module-injective preservation assumption is made.

The provenance is internal: the isomorphisms are identity comparisons of
the actual underlying constructions, and the cohomology identity specializes
the degreewise resolution-comparison factorization theorem. The result
applies to nilpotent closed immersions once their actual underlying
homeomorphism supplies `IsIso h.base`. Identification with Mathlib's
Ext-defined abelian-sheaf cohomology pushforward equivalence, compatibility
with the relative scalar-ring comparisons, actual Picard obstruction
naturality, and the exact field Picard-stack atlas remain further obligations.
