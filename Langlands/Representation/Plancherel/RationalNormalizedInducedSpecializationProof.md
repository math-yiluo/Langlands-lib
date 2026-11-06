# Canonical specialization of actual rational normalized induction

Worker 1635, with Worker 1679 contributing the actual parabolic rational-point
closedness argument.

The public theorem `Langlands.Plancherel.RationalNormalized.rationalNormalizedInducedSpecialization`
proves exactly the existing
`RationalNormalizedInducedSpecializationStatement.{u, uCarrier}`. The field and
representation-carrier universes are independent. Its conclusion is bijectivity
of the already constructed `inducedScalarExtension r h hU π χ`, whose source is
`ℂ ⊗[RegularAlgebra r] Induced r h hU π.representation` with scalar action through
`evaluation r χ`. Its target is the published full `complexInduced r h hU π χ`.
The theorem retains every hypothesis and the all-rational-character coefficient
algebra in that statement.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026 version, VI.8.2: the base-change proposition and (VI.8.2.2), printed
p.190 / PDF p.196, and the specialization corollary, printed p.191 / PDF p.197.
Registered source: `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The implementation follows its finite compact-open double-coset route. The
private helpers give the elementary coefficient and tensor details of that
argument; they are derived proof infrastructure, with no additional public
statement or assumption.

First let B be a complex algebra and let ρ act on `B ⊗[ℂ] V`. Suppose that its
restriction to a subgroup J is scalar extension of a complex representation τ.
The map `fixedTensorMap` sends `B ⊗[ℂ] V^J` into `(B ⊗[ℂ] V)^J` by the tensor
extension of the fixed-subspace inclusion. To prove injectivity, choose a
complex-linear complementary projection onto `V^J` and tensor that projection;
it is a left inverse. For surjectivity choose a complex basis of B and expand a
fixed tensor into its finitely many nonzero coordinates in V. The equality
expressing invariance implies that each coordinate is τ-fixed, so the expansion
lifts to `B ⊗[ℂ] V^J`. This uses neither finite dimension nor admissibility of V.

Now let B act on ℂ by evaluation and let T be coefficient evaluation, with
`T(b ⊗ v) = b(χ) • v`, equivariant for ρ and τ. Restrict T to the fixed spaces.
Tensoring the preceding isomorphism with ℂ and applying tensor cancellation
identifies the scalar extension of this restriction with the isomorphism
`ℂ ⊗[B] (B ⊗[ℂ] V^J) ≃ V^J`. The proof checks this identity on pure tensors.
This proves `fixedCoefficientFiber_bijective` without a flatness premise.

For a compact open subgroup K of G, compactness of the literal left quotient
P\G supplies a finite distinct transversal for P\G/K via
`exists_finset_doubleCoset_representatives`. The published
`Induction.fixedEvaluationEquiv` identifies the K-fixed induced functions with
the finite product, over representatives x, of coefficient vectors fixed by
`P ∩ x K x⁻¹`, represented as `conjOpenSubgroup P K x`. The coefficient
isomorphisms above and `TensorProduct.piRight` therefore give bijectivity at
this fixed level. The commuting identity is again checked on pure tensors:
evaluating a specialized function at x is exactly applying T to its original
value at x. Thus this is the fixed-level canonical specialization map.

To pass to the full spaces, `exists_tensor_compact_level` proves by tensor
induction that every element of the source fiber lies in the range of the
tensor extension of the inclusion of one compact-open fixed subspace. A pure
tensor uses a compact open subgroup inside the open stabilizer of its induced
function. For a sum, intersect the two compact open subgroups and use the
inclusions of their fixed spaces. For injectivity, lift a kernel element to
such a level. The commuting square with the full evaluation map and injectivity
of the target fixed-space inclusion show that its fixed-level image is zero.
Fixed-level bijectivity makes the lift zero, hence also the original tensor.
For surjectivity, a target smooth function has an open stabilizer; choose a
compact open subgroup inside it, lift the function using the fixed-level
surjection, and then apply the tensor extension of the inclusion. The same
commuting square gives the required full-space preimage. Injectivity of the
tensor extension of an inclusion is never assumed.

For the normalized parabolic representations, the published compact-stabilizer
triviality theorem applies because P is closed, every norm character is
continuous, and the supplied Levi projection is continuous. Every actual
unramified character is therefore one on the projection of
`P ∩ x K x⁻¹`. Consequently the universal regular evaluation factor is the
constant one on this stabilizer. The positive full-parabolic half-modulus
remains the same scalar in the universal and complex actions: it is carried
into B by the constant algebra map. Tensor scalar compatibility proves
`compact_inducing_baseChange` for the complete normalized actions. The helper
`parabolic_inducedFiber_bijective` then applies the full-space argument to the
existing tensor evaluation and function-value evaluation, with their published
equivariance identities.

Finally, the supplied `ParabolicRootPresentation` makes p a closed subgroup
immersion. Its range functor is represented by p, so the existing rational-point
closedness theorem gives closedness of the literal `ParabolicPoints p` in the
canonical rational-point topology; the local field supplies the Hausdorff
property. The published continuity theorem applies to every actual Levi
rational norm character. Together with the target's explicit projection
continuity and literal quotient compactness, these facts instantiate the
normalized-parabolic argument. The resulting map is definitionally the
published `inducedScalarExtension`. In particular the formula remains
`z ⊗ f ↦ z • inducedEvaluation r h hU π χ f`; the existing pure-tensor law and
pointwise evaluation law determine its actual-function specialization.

No new hypotheses are added. All functions retain the published covariance
and one uniform open right stabilizer. The proof does not require coefficient
flatness, finite projectivity, finite-dimensional carriers or admissibility,
and does not assert Jacquet base change or the family finiteness of VI.8.3.
