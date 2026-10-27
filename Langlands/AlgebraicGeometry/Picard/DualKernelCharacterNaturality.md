# Test-scheme naturality of the actual dual-kernel character

This internal adapter derives naturality of the constructed beta on actual
dual-kernel points from the generic intrinsic-character naturality. It imports
the existing Poincaré representative, its trivial homomorphism pullback and the
choice-independent class character. It introduces no new geometric hypothesis
and supplies no character or naturality law as input.

For a homomorphism `f : A → B` over `S`, retain the existing
`hA : HasDualScheme A`, `hB : HasDualScheme B` and
`stability : PicardZeroPullbackStatement`. For a test scheme `T/S`, let
`p : T → dualScheme B hB` satisfy the existing equation that its dual image
is the origin. For every `b : U → T` over `S`, the already proved
`dualKernelPoint_restrict` supplies that equation for `b ; p`.

`dualKernelPullbackClass_restrict` identifies restriction of
`dualKernelPullbackClass ... p` with the class for `b ; p`.
The proof uses `dualPointFamilyPullbackIso`, forgets rigidification, and
applies invariance of the trivial-pullback class under an actual line-bundle
isomorphism. It does not identify the separately chosen trivializations.

`dualKernelCharacter_restrict` applies the generic
`trivialHomPullbackClassCharacter_restrict` to this class equation, with
the proved `universalGlobalFunctions A`. Thus beta for the restricted dual
point equals restriction in the existing `Cartier.characters` presheaf.
`dualKernelCharacterHom_restrict` transfers the equality through
`Cartier.characterHomEquiv` and identifies the actual group-scheme
homomorphism with `Cartier.characterHomRestrict`.

For the actual scheme-theoretic kernel of the underlying map of
`dualCommGroupSchemeMapFromEvaluation`, retain its same seven constructor
propositions, two inverse line bundles and their evaluation isomorphisms.
`dualKernelPointCharacter_restrict` specializes the preceding equation to
each actual dual-kernel point. Its proof uses associativity and proof
irrelevance for the two proofs of the same origin equation.
`dualKernelPointCharacterNatTrans` packages these particular maps as a
natural transformation from the representable point functor of the actual
dual kernel to the underlying sets of the existing relative character
functor. Its components are precisely `dualKernelPointCharacter`.

The provenance is the internal composition of the two imported modules and
their stated representative and class-character laws. The orientation is
inherited from the actual beta without inversion. No isogeny, finiteness,
characteristic or quasi-separated-base assumption is added. This unit
asserts naturality in the test scheme only. Tensor compatibility, dual-variable
additivity, bijectivity, Cartier duality, finite Weil pairings and perfectness
remain separate obligations.
