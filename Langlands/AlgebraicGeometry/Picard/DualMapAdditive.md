# Conditional additive dualization over a base scheme

This module bundles the actual dual pullback maps as additive homomorphisms
on integral Hom groups over an arbitrary scheme `S`. The input is an
explicit proof of `DualSchemeMapAdditivity` for the specified endpoints.
No additivity theorem over an arbitrary base is proved or assumed
implicitly.

## Inputs and constructions

Fix abelian schemes `A`, `B` over `S`, with actual universal-family
existence witnesses `hA : HasDualScheme A`, `hB : HasDualScheme B`.
The constructed group schemes have the actual parameter schemes
`dualScheme A hA`, `dualScheme B hB`.

The seven fixed-map inputs are:

- `pullbackTensorComparisonIsIsoStatement`;
- `PullbackTensorCompositionStatement`;
- `PullbackTensorUnitCoherenceStatement`;
- `ExplicitPullbackTensorAssociativityStatement`;
- `TensorMonoidalLeftUnitorComparisonStatement`;
- `PullbackTensorSymmetryStatement`;
- `PicardZeroPullbackStatement`.

For each endpoint, the construction also takes an ordinary line bundle
on its universal family space, and a module-sheaf isomorphism from its
tensor with the Poincare family to the structure sheaf. These are the
explicit inverse and evaluation inputs of the existing group-scheme
construction. They do not store a desired dual map or group law.

The additional proof
`additivity : DualSchemeMapAdditivity preservation stability A B hA hB`
asserts the equation for these fixed endpoints: the actual dual map
of `f + g` is the pair of the actual dual maps of `f` and `g` followed
by `dualTensor`. This differs from each fixed dual map preserving tensor
multiplication.

`dualGroupSchemeMapAddHom` has type

`(A ⟶ B) →+ (dualGroup B ⟶ dualGroup A)`.

Here `dualGroup` abbreviates the existing
`dualCommGroupSchemeFromEvaluation`, with the displayed inputs. The
function is exactly `dualCommGroupSchemeMapFromEvaluation`. Its
application lemma is reflexivity. Thus the construction packages the
actual Poincare-pullback maps, rather than choosing an arbitrary additive
map.

For pointwise geometry proofs `geometryA : DualSchemeGeometry A hA` and
`geometryB : DualSchemeGeometry B hB`,
`dualAbelianSchemeMapAddHom` gives

`(A ⟶ B) →+ (dualAbelian B ⟶ dualAbelian A)`.

The endpoint objects are the published `dualAbelianSchemeFromEvaluation`
constructions. Their Hom groups inherit the underlying commutative
group-scheme Hom groups, so the additive map is the same definition.
Its application formula identifies it by reflexivity with
`dualAbelianSchemeMapFromEvaluation`.

## Implemented proof

`dualGroupSchemeMap_add` proves the bundled-map addition equation from
the endpoint-specific scheme-map equation. First it removes the
`Additive` wrapper and applies extensionality of group-object
homomorphisms. The underlying sum uses the Cartesian monoidal product.
The constructed group multiplication is expressed using `Limits.prod`.
Rewriting by the supplied equation and the two product projection
identities reconciles these products and finishes the equality.

`AddMonoidHom.mk'` then bundles the function and this addition proof.
It derives the zero law in the additive group; the zero law is not an
extra hypothesis. Both application lemmas are definitional equalities.
No geometric additivity theorem, inverse existence, or tensor coherence
input is proved in this module.

## Provenance and scope

This is a derived algebraic construction from the existing Library
dual maps, group schemes and pointwise proposition. It generalizes the
same algebraic argument in `FieldDualMapAdditive` by using fixed
endpoint additivity and geometry proofs over `S`. Existing field
declarations are unchanged.

The mathematical convention for relative dual maps is Kai-Wen Lan,
*Arithmetic compactifications of PEL-type Shimura varieties*, thesis
revision March 14, 2021, Definition 1.3.2.9, printed p.75 (PDF p.103):
dual maps act by pullback on rigidified Picard-zero classes.
Theorem 1.3.2.3 and Definition 1.3.2.5, printed p.74 (PDF p.102), give
the dual and universal family. Registered source
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.

Lan's scheme convention is quasi-separatedness (printed p.xxvi,
PDF p.26). The separate `RelativeDualSchemeMapAdditivityStatement`
retains that hypothesis for its global theorem target and explains
the derived provenance and remaining family comparison obligations.
The construction here uses an explicit proof of the pointwise equation,
so it makes sense over any base. No source theorem is extended beyond
its hypotheses.

This module provides the integral additive map needed for extension to
the existing rational Hom groups. That rational extension and the
polarization constructions are subsequent work.
