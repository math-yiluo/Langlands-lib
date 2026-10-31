# The joint CM action class underlying the Harris Weil tower

This internal construction connects the existing actual fixed-base
`HarrisCMWeilLevel.isoClassTower` with
`CentralSimpleUnitaryData.HarrisTaylorCMActionClass`. It retains the same
actual representative, normalized determinant, and prescribed geometric
dimension when forgetting its polarization and Weil level.

The fields, algebra and base schemes have universe zero; the class
functors take values in `Type 1`. The base is an actual map
`p : S ⟶ Spec F`. The totally real `E`, CM extension `F/E`, imaginary
quadratic `L`, compatible algebra structures, signature charts `C`,
geometric point, finite-fibre hypotheses, torsion hypotheses and
coefficient comparison are exactly those of the imported tower.

The representative equivalence is the previously proved
`harrisTaylorCMDeterminantDimensionCondition_iff`: the normalized determinant
implies the full central trace, so the tower's determinant-and-numerical
condition agrees with determinant and dimension on that same object.
The dimension is the actual prescribed relative dimension
`[E : ℚ] * n ^ 2`, not the dimension of a selected linear representation.
`forgetCMAction` refines the existing numerical forgetful map using an
actual satisfying representative furnished by `classOf_surjective`.
Its underlying rational action class is unchanged.

The representative formula is definitional. Equality along every original
Harris level arrow follows from the existing numerical forgetful map's
transition law and subtype extensionality. These maps form
`forgetCMActionNatTrans` to the constant functor of joint action classes.
The compact-open inclusion and both actual Hecke legs specialize this
transition law. Projection back to the numerical image is precisely the
existing numerical forgetful map.

The target consists of actual equivariant rational-isomorphism classes
admitting one jointly satisfying representative. This construction does
not assert that dimension is invariant on every representative, that the
forgetful map is injective or surjective, or that the target has any
element. In particular `classOf_surjective` is used only to extract a
representative from an already given tower class.

The last theorem computes pullback of the forgotten class in the joint
action presheaf: it is the class of the actual pulled-back abelian scheme
with its composed rational algebra action. The named family of integral
Lie base-change naturality hypotheses remains explicit. This theorem does
not construct pullback of the original polarized Weil-level object.

All arithmetic, signature, Picard, tensor, torsion, pairing and finite-adele
comparison parameters of the input tower remain explicit. The positive
auxiliary left involution, normalized CM-to-reflex map and original Harris
level group are those already constructed in the imported modules.
No new literature assertion, satisfying-object existence, faithful-action
pullback, polarization stability, varying-base polarized tower,
representability or scheme level is claimed.

The provenance is internal: all constructions and proofs combine the
imported tower, its representative image and numerical projection with the
joint action-class construction. The Hecke statements use the original
finite-adelic group and its actual compact-open intersection. Their
rational finite-dimensionality instance is derived from
`hodgeRationalPELConditions D C`; it is not added as an arbitrary input.
