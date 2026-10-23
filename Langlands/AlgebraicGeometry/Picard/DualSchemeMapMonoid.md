# Monoid homomorphisms induced by dual maps

This module packages the existing homomorphism pullback on geometric
Picard-zero classes and postcomposition by the existing dual map as monoid
homomorphisms. The multiplicative Poincare classification equivalences
identify these two homomorphisms.

## Provenance and hypotheses

Edixhoven–van der Geer–Moonen, *Abelian Varieties*, Chapter VI, paragraph
(6.2), printed p.88 (PDF p.92), defines the tensor law on rigidified classes
and classification by a universal rigidified family. The registered source
is `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The present module is an internal derivation from those operations and the
existing `DualSchemeMapTensor`, `DualSchemeOrigin`, `PicardZeroMonoid`
and `DualSchemeMonoid` results. It asserts no new geometric theorem.

The inputs are the six fixed-map propositions for comparison invertibility,
composition, both unitors, explicit associativity, left-unitor comparison,
and symmetry used by `dualPointCommMonoid`.
For dual points, `PicardZeroPullbackStatement` and actual universal-family
existence `HasDualScheme A` and `HasDualScheme B` are also retained.

Preservation of the geometric Picard-zero condition under an abelian-scheme
homomorphism uses the published theorem `homPicardZeroPullback` directly.
It is not an additional assumption of these constructions.

## Implementation

For `f : A ⟶ B` and any test scheme `T`,
`homPicardZeroPullbackMonoidHom` has underlying function exactly
`homPicardZeroClassesPullback homPicardZeroPullback f T`, from the classes
for `B` to those for `A`. The existing trivial-class and tensor-preservation
lemmas prove its two homomorphism laws.

`dualSchemeMapMonoidHom` maps a point `p : T ⟶ B∨` to
`p ≫ dualSchemeMap homPicardZeroPullback f hA hB`.
Its unit equation is the existing origin-preservation equation composed
with the structural map from `T`.
For multiplication, injectivity of classification reduces the equation
to homomorphism pullback of a tensor product. The proof rewrites using
`dualPointClass_dualSchemeMap`, `dualTensor_points`, and
`homPicardZeroClassesPullback_tensor`.

`dualSchemeMapMonoidHom_classification` says that applying multiplicative
classification after this point homomorphism equals applying the class
pullback homomorphism after classification. Its proof is exactly the
existing actual-pullback classification equation.

The result concerns the monoid homomorphism induced by each fixed `f`.
It does not prove additivity with respect to `f`, a rational extension,
inverses, or an abelian-scheme structure on the dual parameter schemes.
