# Base-change comparison for actual diagonalizable groups

For any morphism `b : Spec B → Spec A` between spectra of commutative local
rings, this module constructs the Hom-set equivalence induced by the actual
group-scheme base-change functor, for two diagonalizable groups over `A`.
The ring map need not be local, injective, or surjective. No completeness,
noetherianity, or smoothness assumption is required.

`diagonalizable_baseChange_hom_bijective` chooses diagonalizable presentations
of the source and target. The published `Diagonalizable.relativeModelIso`
identifies their relative models with the affine group-algebra models.
Conjugating the Hom sets by these isomorphisms and their actual base changes
makes the original base-change map commute with the split-model map.
`baseChange_hom_bijective` from `LocalDiagonalizableHom` proves the latter
bijective, so conjugation transfers bijectivity to the original groups.

`diagonalizableHomBaseChangeEquiv` packages the result as an equivalence whose
forward map is base change. `diagonalizable_existsUnique_lift` gives the
corresponding unique-lifting assertion for every homomorphism after base
change.

`diagonalizable_isIso_of_baseChange` reflects isomorphisms between these
groups. Lift the inverse of the base-changed map by surjectivity of the Hom
comparison in the reverse direction. Injectivity of the two endomorphism
comparisons shows that its composites with the original map are the identity.
Thus the lifted inverse gives an actual isomorphism over `A`.

This is internal derived content from the split character classification and
isomorphism transport. It supplies the split-group Hom comparison used in
Conrad (2014), Theorem B.3.2(2), p.289. Both groups must already be
diagonalizable over `A`; a multiplicative-type special fibre alone does not
satisfy that hypothesis. The module proves no deformation or adic-effectivity
result.
