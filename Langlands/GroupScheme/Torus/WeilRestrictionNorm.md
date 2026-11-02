# Scalar and norm morphisms of the Weil-restricted multiplicative group

This derived construction equips the published actual Weil restriction with
its scalar and determinant norm morphisms. The base `A` is a commutative ring,
and all types lie in one universe. Scalar maps require `B/A` finite projective;
norm maps and their composite formula require `B/A` finite free.

For every test scheme `T → Spec A`, including nonaffine and nonreduced tests,
the existing point model identifies `Res_{B/A} G_m(T)` with
`(B ⊗_A Γ(T))ˣ`. The scalar map sends a unit `r` to `1 ⊗ r`.
The norm sends a tensor unit to its determinant norm over `Γ(T)`,
after swapping the factors to regard `Γ(T) ⊗_A B` as a `Γ(T)`-algebra.
These formulas define actual morphisms in the existing category of group
schemes, and also morphisms of commutative group schemes.

Naturality is proved for arbitrary changes of test algebra, with no
injectivity or reducedness assumption. The companion `TensorNorm` module
proves the determinant compatibility by comparing finite tensor-basis
multiplication matrices. The scalar/norm composite is proved on all tests
to send `r` to `r^[B:A]`, and hence equals multiplication by the finite free
rank as an actual endomorphism of `G_m`.

This is internal derived content from the published Weil restriction,
its all-test unit model, Mathlib's determinant norm, and the Yoneda
construction of group-scheme morphisms. It does not assert a norm
construction for arbitrary finite projective algebras. Splitting and
Galois-lattice comparisons and properties of the norm kernel remain
separate obligations.

The construction API consists of `scalarUnits`, `scalarPoints`, and `scalar`,
with `scalarHom` its commutative-category form, and `normPoints`, `norm`,
and `normHom`. The lemmas `scalarPoints_naturality` and
`normPoints_naturality` justify application of `homOfPoints` to those
families. The final point formulas are `scalar_points` and `norm_points`;
`scalar_norm_points` and `scalarHom_comp_normHom` are the two forms of the
composite identity. No field, separability, or nonzero-ring hypothesis is
needed for these constructions. In particular finite field extensions
satisfy the finite free norm hypotheses, whether separable or inseparable.

Author: Worker 207.
