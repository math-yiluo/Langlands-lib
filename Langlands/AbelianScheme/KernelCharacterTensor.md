# Tensor compatibility of the intrinsic kernel character

This derived unit proves the tensor law for the actual intrinsic character
constructed in `IntrinsicKernelCharacter`, together with its choice-independent
line-bundle version from `KernelCharacterIndependence`. It applies to an actual
abelian-scheme homomorphism `f : A → B`, any test scheme `T` over the base, and
actual module sheaves `M,N` on `T ×_S B` with trivializations of their `f_T`
pullbacks. In particular it applies to actual line bundles.

The input `preservation : pullbackTensorComparisonIsIsoStatement` retains the
existing explicit assertion that the canonical module-sheaf pullback tensor
comparison is invertible. Tensoring the two trivializations uses precisely
`tensorPullbackTrivialization preservation f_T α β`: the canonical tensor
comparison, the tensor of the two actual trivializations, and the contraction
`O ⊗ O ≅ O`. No action or character is supplied as an assumption.

`kernelTranslationAut_tensor` specializes `equalCompositeUnitAut_tensor` to
the ordinary family map and its actual kernel shear. Thus the normalized
automorphism for the tensor trivialization is the composite of the two
normalized automorphisms, in the same ordinary-to-translated direction as the
original construction. `kernelTranslationScalar_tensor` extracts value at one
from this equation, using `structureAutScalar_trans`; the scalar of the tensor
is the product of the two scalars. These two assertions need no universal
constant-functions hypothesis.

`kernelTranslationUnit_tensor` assumes `UniversalGlobalFunctions A`, the Prop
asserting that every actual projection `U ×_S A → U` induces an isomorphism on
global functions. The inverse of its induced map on global units is a monoid
homomorphism, so the units descended from the two action scalars multiply.
This is the evaluation formula behind the tensor law; there is no inversion
of either component character.

`intrinsicKernelCharacterHom_tensor` proves equality of actual group-scheme
homomorphisms `ker(f)_T → Gm_T`. The multiplicative character group is written
additively in `Cartier.CharacterHom`. Its proof tests the homomorphisms on all
schemes over `T`, applies the actual Gm-points equivalence with global units,
uses the pointwise multiplication of group-scheme homomorphisms and the
intrinsic character evaluation formula, and finishes with
`kernelTranslationUnit_tensor`.

`intrinsicKernelCharacter_tensor` transfers the result across the existing
additive equivalence `Cartier.characterHomEquiv`. Its target is the existing
Cartier characters presheaf:

```
character(tensorPullbackTrivialization preservation f_T α β)
  = character(α) + character(β).
```

`hasTrivialHomPullback_tensor` proves that the actual line-bundle tensor of two
bundles with trivial `f_T` pullback again has trivial pullback, by constructing
the tensor trivialization from witnesses of the two hypotheses.
`trivialHomPullbackTensor` uses this proof to define the tensor operation on
actual objects of `TrivialHomPullbackFamily f T`.
`trivialHomPullbackCharacter_tensor` then proves the same additive formula for
the character defined without a trivialization choice. It computes that
character using the constructed tensor trivialization, invokes the tensor law,
and uses the original definitions on the two factors. Established independence
of trivialization justifies using this concrete witness instead of the one
chosen by the choice-independent constructor.

The provenance is derivation from published canonical module-sheaf pullbacks,
the module-sheaf tensor, `EqualCompositeTensor`, intrinsic character evaluation,
and its established independence. This unit proves tensor compatibility and
closure under tensor of the actual families. It does not put a group structure
on their isomorphism classes, prove effective descent, or assert kernel duality.
