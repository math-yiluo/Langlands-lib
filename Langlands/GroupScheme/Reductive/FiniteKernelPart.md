# Removing a supplied finite closed-fibre kernel part

This internal construction works in every universe over any local commutative
ring `R`. Its input is a homomorphism `f : G → H` and a supplied open subset
`U` of the actual scheme-theoretic kernel, satisfying
`IsFiniteClosedFibrePart (kernel f).X.hom U`: the subset is closed, its structure
morphism is finite, and it contains the whole closed fibre. The input does
not include a proof that such a subset exists.

`FiniteKernelPart.group` is the actual group scheme on this exact open
subscheme, using `FiniteClosedFibrePart.group`.
`FiniteKernelPart.inclusion` is its open inclusion into the kernel followed
by the original kernel inclusion into `G`. It is monomorphic, and
`inclusion_comp` proves that its composite with `f` is the zero
homomorphism. Its structure morphism is finite; flatness and local finite
presentation are inherited from the kernel through the open inclusion.

The helper `FiniteClosedFibrePart.isIso_baseChange_inclusion` proves that
base change of the open subgroup inclusion is an isomorphism along any
scheme map whose topological image is the closed point. The proof identifies
the underlying map with the actual pullback map. The pullback range formula
and the closed-fibre containment hypothesis show that this open immersion
is surjective. The resulting scheme isomorphism lifts through the over,
monoid-object and group-object forgetful functors. In particular,
`isIso_closedFibre_inclusion` applies to the canonical residue-field point.
`FiniteKernelPart.closedFibre_range` then identifies the full subgroup-functor
range of the base-changed inclusion with the full kernel range of the
base-changed `f`, using the actual kernel base-change comparison.

`FiniteKernelPart.normal` proves normality on every scheme test whenever
`G` has geometrically connected fibres. The full kernel range is normal by
the homomorphism identities. The constructed inclusion is open and closed
inside this kernel, so `ClopenNormalSubgroup.isNormal_range_comp` applies.
The existing `IsReductive.geometricallyConnected` theorem, imported from
`RelativeParabolicNormalizerReduction`, supplies geometric connectedness
by reductive base change to each field-valued fibre.

The principal construction `FiniteKernelPart.reductiveQuotient` additionally
takes reductivity of `G` and `H` and the fibrewise-isogeny hypothesis on `f`.
It returns `ReductiveKernelQuotientFactorization` for the constructed
inclusion and the canonical closed residue-field point. This packages an
actual reductive quotient `Q`, its finite fppf projection `q : G → Q`, and
an actual remaining homomorphism `g : Q → H`, together with `q ≫ g = f`,
fibrewise isogeny of `g`, and invertibility of its specified closed fibre.
The construction supplies all prerequisites of
`reductiveKernelQuotientFactorization`: fibral flatness gives flatness of
`f`; smoothness of the two structure maps gives local finite presentation
of `f`; the actual kernel square transfers both properties to the kernel;
the supplied part inherits them; and the preceding normality, killing and
closed-fibre range lemmas give the remaining hypotheses.

This is a derived composition of the named constructions and elementary
pullback, connectedness and kernel arguments. No identification with a new
literature theorem is asserted. The existence of the finite clopen part
from a Henselian hypothesis, and the unconditional host
`ReductiveFibrewiseIsogenyStatement`, remain separate proof obligations.
