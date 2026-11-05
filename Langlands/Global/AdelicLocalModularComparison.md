# Local restriction and assembly of actual adelic modular characters

This internal unit compares the existing actual adelic group with its actual
local factors over a number field in arbitrary universe `u`. The topology,
group laws, and normalized character norms are the existing Library ones.

For an affine group scheme, `ofPlaceEquiv` identifies the actual local
point group continuously and multiplicatively with the range of `ofPlace`.
Its inverse is the existing local projection. `characterNorm_ofPlace` proves
that an actual rational character's adelic norm on this insertion equals
its normalized local norm. The proof uses the existing product formula
for the character norm: every other local value is one, so the product over
infinite places and the finitary product over finite places reduce to the
one chosen coordinate. The complex-place multiplicity is retained by the
existing local norm.

With the locally finite type hypothesis, both actual point groups are
locally compact. `modularCharacter_ofPlace` proves that the ambient
intrinsic modular character at the insertion equals the intrinsic modular
character of the original local point. It applies the proved modular
restriction theorem to the closed normal range of `ofPlace`, using
`ofPlaceEquiv` to transport back to the local group. No Haar right
invariance or analytic determinant identity is assumed for this step.

`modularCharacter_eq_characterNorm_of_local` assumes a pointwise local
comparison with a given rational character at every place and concludes
the analogous comparison on every actual adelic point. Both sides are
continuous homomorphisms to the nonnegative reals: the left side uses the
proved continuity of the intrinsic modular character, and the right side
uses the continuous units value map and the existing character norm.
The two insertion formulas make them agree on each local factor.
`continuousMonoidHom_ext_ofPlace`, proved using convergence of finite
local truncations in the actual adelic topology, gives their equality.

The final theorem
`adelicModularCharacterAdjointDeterminantStatement_of_local` applies this
argument to the actual full adjoint determinant character. Its hypothesis
is exactly the existing universal
`PlaceGroupPoints.LocalModularCharacterAdjointDeterminantStatement`, and
its conclusion is the existing universal
`AdelicModularCharacterAdjointDeterminantStatement`, at the same arbitrary
universe. The general assembly helper needs neither smoothness nor
connectedness; the final theorem retains those conditions from the
existing adelic statement.

The provenance is internal: the proofs derive from actual local gluing,
closed-normal modular restriction, continuous multiplicative equivalence
transport, normalized local character norms, modular continuity, and
finite-truncation convergence. This unit proves the local-to-adelic
implication. The local analytic adjoint-determinant comparison and
reductive determinant triviality remain separate proof obligations.
