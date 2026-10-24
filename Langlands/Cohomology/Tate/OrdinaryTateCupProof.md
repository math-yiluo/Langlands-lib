# Ordinary and Tate cup comparison

Authors: Worker 45 (proof draft); Worker 210 (author audit and submission documentation).

This is the implementation of `Langlands.Tate.OrdinaryTateCupLaws`. The main
lemma `ordinaryToTate_cup` compares the published explicit ordinary cochain cup
with the published dimension-shifted Tate cup in every natural bidegree. The
final theorem packages exactly that target, in arbitrary universe `u`, for a
commutative ring and finite group and every equivariant bilinear pairing.
There are no additional flatness or compatibility assumptions.
The comparison includes both zero degrees and carries its output forward from
the integer cast of `p+q` to the sum of the integer casts of `p` and `q`.

The proof is an internal derivation from actual cohomology operations. In
`Langlands.Tate.OrdinaryTateCup`, `comparison` composes `ordinaryToTate` with
an explicit integer degree transport. `comparison_refl` removes a reflexive
transport. `comparison_delta` combines the published compatibility with actual
connecting maps and equality elimination in both the natural and integer
degrees. It accounts for the natural successor transport on the ordinary side
and the integer successor transport on the Tate side. `comparison_naturality`
similarly combines ordinary-to-Tate coefficient naturality with equality
elimination.

`tensor_zero` uses ordinary invariant normalization, the degree-zero comparison
to the actual norm quotient, and the Tate invariant normalization. It does
not use a degree-zero comparison isomorphism.

`tensor_left` propagates the comparison through a first-variable boundary
for any short exact sequence whose right tensor image is short exact. The
ordinary tensor boundary identity, `comparison_delta`, and the induction
hypothesis identify its left side with the boundary of the Tate tensor cup.
The published Tate first-variable boundary identity supplies the other side.
`tensor_right` uses the same steps for a second-variable boundary. The scalar
factor from the ordinary identity is moved through the linear comparison.
`sign_smul` identifies the scalar `(-1 : R)^p` with the integer action of
`Int.negOnePow p`, using the natural-exponent formula and integer scalar
compatibility. This is exactly the sign in the Tate boundary identity.

`tensor` applies the published `ordinaryClasses_shift_induction`. The base
case is `tensor_zero`. The first step uses `tensor_left` with the canonical
coinduced embedding sequence and second degree zero; the second step uses
`tensor_right` with arbitrary first natural degree. The published scalar
splitting of each shift sequence supplies right or left tensor short
exactness. Thus the proof requires no blanket tensor-flatness assumption.

For a general pairing, `ordinary_tensorHom` specializes ordinary coefficient
naturality to identity input maps and the actual output map `φ.tensorHom`.
Its pairing compatibility is the formula for the tensor lift on pure tensors.
`ordinaryToTate_cup` replaces the ordinary cup by this postcomposition, applies
`comparison_naturality`, and uses `tensor`. The result is the definition of
the Tate `cup`, which postcomposes its tensor cup by the same coefficient map.
`ordinaryTateCupLaws` packages this main lemma without strengthening its
premises.

The provenance is the dimension-shifting uniqueness argument in Serre,
*Local Fields* (1979), VIII §3, Proposition 5, printed p.131 (PDF p.137),
with the equivariant-pairing convention on printed p.132 (PDF p.138).
Those pages concern integral finite-group Tate cohomology. They provide the
normalization and boundary-sign conventions, rather than literally stating
this comparison of Lean constructions over an arbitrary commutative ring.
The implemented proof derives that comparison internally from the published
normalization, naturality, boundary and ordinary-class induction theorems.
Its use of scalar-split shift sequences explains why the broader ring
generality requires no additional tensor-exactness premise.

The file imports the independently published `OrdinaryCupLawsProof` and
`OrdinaryCupBoundaryProof` modules unchanged, together with the published
comparison, shift and Tate-cup infrastructure. Only this new proof pair is
part of the contribution. The theorem concerns every natural bidegree; it
makes no assertion about negative ordinary degrees.
