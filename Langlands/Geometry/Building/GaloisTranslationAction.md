# Actual Galois actions on reduced translations

For fields `k` and `K` of the same universe and an algebra structure, this
internal unit extends the published ordinary Galois action on the
cocharacter lattice of a scalar-extended commutative group scheme `T`.
The original `T` need not be split, and the coefficient extension need
not be finite or Galois.

`RealTorusSpace.galoisCocharacterAction` is a homomorphism from the actual
group `K ≃ₐ[k] K` to real linear automorphisms of the existing real
cocharacter space of `T_K`. On a pure tensor it sends `r ⊗ ν` to
`r ⊗ σν`, using the published scheme-theoretic lattice transport.
Tensor extensionality and the existing integral representation laws
prove the homomorphism laws. The simultaneous character and real
cocharacter transports preserve evaluation, by the published
Galois-invariance of the integral lattice pairing. The second evaluation
formula moves transport to the character with the inverse automorphism.

For a descended map `i : T.toGrp ⟶ G` with affine structure morphism
for `G`, `galoisRootAction` constructs actual permutations of the
upstairs relative-root set. The published theorem that ordinary
Galois character transport preserves the nonzero adjoint weights
proves that each permutation has the required root type; the integral
representation laws prove their group laws.

The inverse evaluation formula shows that real cocharacter transport
preserves the full common annihilator of these roots. Applying the
inverse automorphism proves that its image is the entire annihilator.
`galoisTranslationAction` therefore descends the action to the existing
`TranslationSpace i_K`, with its actual common root kernel. Quotient
induction proves the homomorphism laws and the covariance of the
existing `rootForm` under the constructed root and translation actions.

This is derived linear and quotient algebra from the named published
lattice pairing and actual-root transport results. No external
existence theorem is claimed. In particular, the unit chooses no
stable maximal torus, origin, root-function valuation class or
apartment. It constructs no normalizer transport, root-subgroup
transport, metric, model fixed point or descent preimage. Those remain
separate obligations for the supplied-model building comparison.
