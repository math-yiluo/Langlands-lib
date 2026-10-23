# Associativity of tensor for rigidified line bundles

This module constructs an associator between the two iterated tensor products
of rigidified line bundles and proves associativity on their isomorphism classes
and on the geometric Picard-zero subtype. It is a derived construction by
Worker 144 using the Library's fixed sheaf tensor and its associator.

## Source and scope

Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary draft,
Chapter VI, paragraph (6.2), printed p.88 (PDF p.92), defines a rigidification
as an isomorphism from the structure sheaf to the section pullback, requires
morphisms to commute with it, and defines the tensor product of rigidified
classes. The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The source motivates the operation; the categorical calculations here are an
internal derivation for the Library's actual maps.

The associator construction assumes three published propositions explicitly:

- `pullbackTensorComparisonIsIsoStatement`: the fixed comparison from pullback
  of tensor to tensor of pullbacks is invertible.
- `ExplicitPullbackTensorAssociativityStatement`: this same comparison commutes
  with the fixed explicit sheaf associator, in the equation declared in
  `Modules.PullbackTensorAssociativityStatements`.
- `TensorMonoidalLeftUnitorComparisonStatement`: the fixed explicit left unitor
  agrees, through `localizedTensorIso`, with the localized monoidal left unitor.

These are hypotheses, not claims proved in this module. No arbitrary coherence
maps or compatibility witnesses are substituted for the fixed maps. The result
applies to any scheme map used for rigidification; at the family level it
applies to any structure map with a section. No hypotheses identifying rigidified
classes with the fppf Picard sheaf are needed for this conditional calculation.

## Sheaf tensor calculations

`localizedTensorNatIso_hom_app` identifies the components of the natural tensor
comparison with `localizedTensorIso`. Its naturality gives
`localizedTensorIso_hom_naturality` and, by cancellation of an isomorphism,
`localizedTensorIso_inv_naturality`. The `_assoc` variant postcomposes the latter
identity by another morphism.

`tensorAssociator_naturality` proves naturality of the actual explicit
associator by unfolding its construction, applying those comparison identities,
and using naturality of the localized monoidal associator.

`tensorAssociator_leftUnitor` uses the left-unitor comparison hypothesis to
transfer the localized equation
`alpha(unit,M,N); lambda(M tensor N) = lambda(M) tensor id(N)` to the explicit
tensor. Here a semicolon means composition in the displayed order.
`tensorUnit_split_assoc` then proves the corresponding equation for the two
ways to split the unit into three factors: split, split the left factor, and
associate equals split and split the right factor. Its proof cancels the
invertible left unitor, applies the preceding equation, and uses naturality and
inverse identities of the explicit left unitor.

## Compatibility with rigidification

For rigidified modules `L`, `M`, `N` along `epsilon : S -> X`,
`tensorTriple_left_rigidification_comp` computes the rigidification of
`(L tensor M) tensor N` after composing with the two fixed pullback comparisons.
It is the two left splits of the structure sheaf followed by the triple tensor
of the original rigidifications. `tensorTriple_right_rigidification_comp`
gives the corresponding right-split formula for `L tensor (M tensor N)`.
Both follow by applying `tensorObj_rigidification_comp` twice and composing
tensor maps.

`RigidifiedModule.tensorAssociator_compatibility` proves that pulling back the
fixed sheaf associator carries the first rigidification to the second. The
proof cancels the right outer comparison followed by the tensor of the identity
and the right inner comparison. It uses the explicit pullback-associativity
hypothesis, the two triple-rigidification formulas, associator naturality on the
three rigidification morphisms, and `tensorUnit_split_assoc`.

`RigidifiedLineBundle.tensorAssociator` applies `isoMk` to that fixed sheaf
associator and the compatibility proof. Its source is
`tensor preservation (tensor preservation L M) N` and its target is
`tensor preservation L (tensor preservation M N)`. The underlying modules and
the tensor operation are the existing locally free rank-one constructions.

## Equality of classes

`RigidifiedLineBundle.classesTensor_assoc` descends this compatible isomorphism
using induction on three quotient classes. For every test scheme `T` over the
base, it proves `(q tensor r) tensor s = q tensor (r tensor s)` for the existing
class tensor operation. The quotient relation uses isomorphisms that preserve
rigidification, so the assertion retains that condition.

`AbelianScheme.picardZeroClassesTensor_assoc` proves the same equation on
`PicardZeroClasses A T` by subtype extensionality and the class equation. Tensor
closure of this subtype is supplied by the existing tensor construction; no new
geometric preservation hypothesis is introduced here.

This module supplies associativity, not tensor inverses, a complete group
structure, representability, or a dual abelian-scheme structure. The three
explicit fixed-map hypotheses remain in the construction and its class laws.
