# Character-restriction bridges for relative Weyl faithfulness

Author: Worker 37. This internal construction imports the published canonical
full-lattice actions and rational character restriction from
`RelativeCentralDirections` and `RelativeRank`, together with the published
full-character faithfulness and root-kernel comparison.

The new construction and proofs are internal consequences of the actual
published character, quotient and tensor constructions. They work for an
arbitrary field in universe `u`. The structural root/character complement and
the exact `RelativeRootSystemStatement` remain open.

`rationalCharacterRestrictRat_range` identifies the range of rationalized
restriction with the rational span of restrictions of integral group characters.
Tensor induction proves that every image lies in that span: addition uses
submodule closure, and a pure tensor is a rational multiple of the vector
`1 ⊗` the restricted character. The pure-tensor case also covers zero. Conversely each such generator is the image of
the corresponding vector `1 ⊗` the original character.

`relativeRootSpan_sup_restrictionRange` expresses the sum of the actual root span
and that restriction range as the joint span of both sets of integral
characters. It uses the range identification, images of unions and the span of a
union. Consequently an intrinsic `IsCompl` assertion supplies the joint-spanning
premise of the existing root-kernel comparison. Only its sum-equals-top component
is needed; this argument makes no claim to establish the complement itself.

The two quotient action names are definitionally equal. Faithfulness of the
canonical integral action follows from split-torus character separation and the
exact centralizer kernel. Faithfulness survives rationalization because the map
from the character lattice of a split torus to its rationalization is injective.
Neither result needs reductivity, maximality or an affine ambient group.

Quotient induction shows that the full integral action fixes every restriction
of an actual group character. Tensor induction then proves pointwise fixedness
of the rational-character restriction range under the full rational action.
The underlying argument is that group characters are invariant under inner
conjugation.

For affine ambient groups, `relativeWeylAction_injective_of_span` uses the
identity-kernel criterion, chooses a normalizing representative and applies the
existing root-span/full-character kernel comparison. The exact full-character
kernel then places that representative in the centralizer. The final
`relativeWeylAction_injective_of_isCompl` supplies this joint span from the
intrinsic complement. Both are explicitly conditional supporting results:
the complement for arbitrary connected reductive groups remains a separate
structural proof obligation, and root-pairing construction and Weyl-image
identification remain separate obligations even after faithfulness is obtained.
All these arguments retain empty relative-root sets.

`IsSplitTorus.relativeWeylEquivRootActionRange` constructs a group isomorphism
from the actual rational-point quotient to the range of its action on the actual
root span, under precisely the same intrinsic complement premise. It applies
Mathlib's `MonoidHom.ofInjective` to the preceding faithfulness proof. Its forward
map is the existing `relativeWeylAction`, with codomain restricted to its range;
the inverse maps an image element back to its unique quotient class. The two
displayed compatibility lemmas identify the coerced forward map and the action
of the inverse. No finiteness or nonempty-root premise is introduced. This
isomorphism does not identify that range with the Weyl group of a root pairing:
constructing that pairing and proving the image equality are separate tasks.
