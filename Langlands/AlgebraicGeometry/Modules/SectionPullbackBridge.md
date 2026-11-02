# Actual section pullback and the linear sections maps

This internal derived module identifies the two existing actual pullback-section
constructions. The adjunction-unit semilinear map on the top open agrees with
`SchemeModule.pullbackSection`, which evaluates the pulled-back section morphism
using the inverse structure-module comparison. The proof uses the published
unit-adjunction characterization and naturality with respect to the section
morphism. Consequently the canonical relative linear map on global sections is
this same actual section pullback. No cohomology comparison, compactness or
separatedness is assumed.

The comparison between pushforwards along equal scheme morphisms is proved to
act as the identity on top sections, by eliminating the equality and applying
the identity law for the sheaf. This gives the relative comparison without any
extra compatibility data.

`sectionsVanishingAlong h M` is the kernel of that canonical relative linear
map. Its membership lemma identifies this kernel exactly with global sections
whose actual pullback along `h.left` is zero. This supplies the linear submodule
used for support-preserving coefficient extraction. The construction and all
comparisons are internal consequences of the imported published definitions;
there is no claim here of a new literature theorem or of ampleness reflection.
