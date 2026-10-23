# Base restriction of class-indexed idele-class extensions

This internal construction joins the published class-indexed extension,
explicit cocycle base restriction, and actual second-cohomology restriction.
For a scalar tower `K → K' → E` of fields in one universe, with `E` a number
field, it embeds the class extension associated to the restriction of any
class `x ∈ H²(Gal(E/K), C_E)` into the extension associated to `x`. Here
`Gal` denotes the actual relative automorphism group; Galoisness is not assumed.
The coefficient action is the published arithmetic idele-class action and the
relative automorphism groups retain their published discrete topology.

`RelativeIdeleCocycle.cohomologyClass_restrictBase` proves that the explicitly
restricted cocycle represents actual cohomological restriction. Apply the
published cochain criterion with the constant-one cochain.

`ClassExtension.restrictedClass` is actual restriction in degree two.
`cohomologyClass_restrictedRepresentative` applies the preceding equality to
the chosen representative of `x`. The continuous equivalence
`restrictionEquiv` compares the chosen representative of the restricted class
with the literal restriction of the representative of `x`, using the inverse
of `equivOfRepresentative`.

`restrictionInclusion` composes this equivalence with the published explicit
cocycle restriction inclusion. It fixes every idele-class coefficient and
projects to scalar restriction of automorphisms. Its injectivity and open
embedding property follow by composition with an equivalence. Its range is
exactly the inverse image of the range of `AlgEquiv.restrictScalarsHom K`
under the extension projection. The range proof transports witnesses along
the equivalence and uses the published cocycle-level range theorem.

The representative comparison uses a chosen cochain and is not canonical.
No equality of independently chosen maps through a longer tower is asserted.
No arithmetic fundamental class is selected, and no relative or absolute Weil
group, norm transition, inverse limit or local-global homomorphism is claimed.
The module proves intrinsic base restriction for every actual cohomology class.
It uses the existing constructions rather than assuming an extension carrier
or a restriction homomorphism.

Provenance is internal and derived from the published modules
`ClassExtension`, `CocycleRestriction`, and `CohomologyMaps`. The underlying
factor-set and cochain conventions are those documented there from Artin--Tate,
*Class Field Theory* (2009), Chapter XIII section 1, printed pp.127--130.
This module introduces no additional literature theorem.
