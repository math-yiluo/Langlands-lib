# Test-scheme naturality of the intrinsic kernel character

This is a derived compatibility unit for the actual intrinsic kernel character
in `IntrinsicKernelCharacter` and its choice-free class map in
`KernelCharacterIndependence`. It uses the canonical square comparison from
`SquarePullbackComparison`; no new literature-dependent assertion or geometric
global-functions theorem is introduced.

Let `f : A ⟶ B` be an actual abelian-scheme homomorphism over `S`, let
`b : U ⟶ T` be a map of test schemes over `S`, and let `M` be a module sheaf
on the actual relative space `T ×_S B`. Write `p_T = f_T` and let
`alpha : p_T^* M ≅ O_(T ×_S A)` be an actual trivialization.

`kernelCharacterPullbackTrivialization` constructs a trivialization of
`p_U^*(b_B^* M)` by composing the canonical comparison around the actual
commutative family square with `b_A^* alpha` and the canonical pullback
isomorphism for the structure module. The definition uses the actual module
pullback functors and their composition and equality isomorphisms.

`kernelShear_map` identifies a kernel translation followed by change of test
scheme with the translation over the composite parameter. Applying the generic
square-coherence theorem gives `kernelTranslationAut_pullback`: for a further
test scheme `V`, a map `a : V ⟶ U`, and an actual kernel point `k` over `V`,
the normalized automorphism for the pulled-back bundle and trivialization at
`(a,k)` equals the original normalized automorphism at `(a ≫ b,k)`.
`kernelTranslationScalar_pullback` gives the same equality for the actual global
unit extracted from the structure-module automorphism.

The remaining character statements assume `h : UniversalGlobalFunctions A`.
This is the existing explicit proposition that the actual structure-morphism
map on global functions is bijective after every test-scheme base change.
`kernelTranslationUnit_pullback` applies the same unique descent of units to
the scalar equality. In particular the transported-action orientation is
inherited unchanged from `kernelTranslationAut`; there is no inversion in
this change-of-test-scheme formula.

The generic helper `Cartier.characterHomRestrict_points` states that evaluating
a restricted actual character on any point gives the same global unit as
evaluating the original character on the point identified by
`Cartier.restrictPointsEquiv`. Its proof uses the first projection of
`baseChangeCompIso`, the natural point equivalence for base change, and the
actual base-change isomorphism for the multiplicative group.

`intrinsicKernelCharacterHom_pullback` identifies the character constructed from
the pulled-back data with `Cartier.characterHomRestrict` of the original
character. The proof checks all test-scheme points, uses the descended-unit
formula, and applies precomposition naturality through `restrictOverIso`, whose
underlying scheme map is the identity. `intrinsicKernelCharacter_pullback`
transfers this equality through `Cartier.characterHomEquiv` to the existing
`Cartier.characters` presheaf.

`trivialHomPullbackCharacter_pullback` removes the trivialization choice by
computing the pulled-back line-bundle character using the specific
trivialization constructed above. Quotient induction then proves
`trivialHomPullbackClassCharacter_restrict` on actual line-bundle isomorphism
classes. These equalities are assembled into
`trivialHomPullbackCharacterNatTrans`, from
`trivialHomPullbackClassPresheaf f` to the underlying sets of
`Cartier.characters (kernelCommGroupScheme f)`. The target carriers are wrapped
in `ULift` to match the universe of the line-bundle quotient; this wrapping
adds no mathematical data. The simp lemma
`trivialHomPullbackCharacterNatTrans_classOf` computes its value on every
actual representative after removing that wrapper.

This unit proves test-scheme naturality only. The tensor compatibility and
additive packaging are subsequent obligations. It proves no effective descent,
representability, perfectness, or Cartier duality.
