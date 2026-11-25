# Noetherian local coefficient models with split residue fibre

This is an internal derived construction for lifting prescribed
diagonalizations to clopen subgroups over strictly Henselian local rings
(`Torus.MultiplicativeTypeStrictHenselianLiftReduction`), with the relative
Henselian etale lifting of `CommutativeAlgebra.StrictHenselianPointedResidueExtension`
as supporting input. It is assembled from finite coefficient descent, finite Galois splitting over fields, and
pointed etale residue extensions. It does not transcribe a single literature
statement. All rings, schemes, and character groups have arbitrary universe `u`.

`LocalModel A H` records the following concrete data:

- a commutative finite-type integer algebra `T` and a prime `q` of `T`;
- an actual local algebra map `P = T_q → A`;
- a group scheme `H₀` over `Spec P`, affine over `P`, flat, and locally of
  finite presentation;
- diagonalizability of the original residue fibre of `H₀` over `κ(q)`,
  with finitely generated full abelian character group;
- an actual group-scheme isomorphism `H ≅ (H₀)_A` for the specified map
  `P → A`.

`LocalModel.noetherian` proves that `P` is Noetherian, since `T` is finite
type over the integers. `LocalModel.approximation` supplies finite-order
etale approximation for its maximal-ideal completion, using
`CommutativeAlgebra.etaleCompletionApproximation_atPrime`. No Henselian
property is asserted for `T` or `P`.

`nonempty_model_of_finiteType_model` takes an existing flat affine locally
finitely presented group `H_T` over a finite-type integer algebra `T`, a
specified map `T → A`, and an isomorphism recovering `H` after base change.
Assume `A` is Henselian local, its residue field `k` is separably closed,
and the special fibre `H_k` is diagonalizable. It constructs a `LocalModel`.
The implemented proof has these steps.

1. Set `q = ker(T → k)` and embed `κ(q)` into `k` with the residue-field
   lifting universal property. The canonical comparisons of iterated base
   change identify the `k`-fibre of `H_T` with `H_k`.
2. The `κ(q)`-fibre is therefore of multiplicative type in the absolute
   field definition: its supplied splitting field is `k`. The published
   `multiplicativeTypeFiniteGaloisSplitting` gives a finite Galois splitting
   extension `K/κ(q)` and a diagonalizable model with finitely generated
   full characters.
3. `exists_pointed_etale_residue_extension` realizes `K` as the residue
   field of a prime `Q` in an etale `T`-algebra `E`, with an actual local
   map `E_Q → A`. The specified residue equivalence respects the original
   `T`-scalar map. Since `E` is etale over `T`, it is again finite type over
   the integers.
4. Base-change `H_T` to `P = E_Q`. The scalar equation for the residue
   equivalence identifies its residue fibre with the splitting extension
   of step 2, so this fibre is diagonalizable. The local map `P → A`
   and the canonical pullback comparison recover `H`. Affineness, flatness,
   and local finite presentation follow by base change.

`nonempty_model` constructs the initial finite-type integer model for every
flat affine locally finitely presented group `H` over such an `A`, assuming
only that its special fibre is diagonalizable. It invokes the published
`FiniteCoefficient.exists_flatAffineGroupModel` over a universe lift of the
integers, then applies the preceding refinement theorem. Restriction to the
ordinary integer scalars preserves finite type.

The construction retains finite torsion in all character groups. It requires
no Noetherian hypothesis on `A`. It supplies some diagonalization of the
model's special fibre; it does not recover a prescribed original special-fibre
isomorphism, construct a whole clopen lift, or assert the full strict-Henselian
lifting theorem. The full strict-Henselian lifting theorem is
`multiplicativeTypeStrictHenselianLift`, in
`Torus.MultiplicativeTypeStrictHenselianLiftProof`.
