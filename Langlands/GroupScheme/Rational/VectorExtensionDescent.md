# Descent of sections of extensions by linear vector groups

For arbitrary fields `k` and `K` in universe `u` with `Algebra k K`,
`VectorExtensionDescent.extensionSectionOfBaseChange` constructs an actual
homomorphism `H ⟶ E` over `k`. Its companion
`extensionSectionOfBaseChange_comp` proves that its composite with the given
quotient homomorphism `q : E ⟶ H` is the identity.

The inputs are group schemes `H`, `E`, and `V` over `Spec k`, a homomorphism
`n : V ⟶ E` monic on relative schemes, and equality of its all-test
subgroup-functor range with the full kernel range of `q`. Both `H` and `V`
are affine over `k`. An original scheme morphism `s : H.X ⟶ E.X` is supplied
with `s ≫ q.hom.hom = 𝟙 H.X`; no homomorphism property is assumed for `s`.
The vector presentation is a finite family of group equivalences `e` from
`V`-points on every relative test scheme to additive vectors of global
functions, together with `IsLinearVectorCoordinates` for the actual conjugation
action of `E` on this kernel. This includes naturality under every test-scheme
morphism and scalar-linearity of conjugation. Finally a group-scheme section
`σ : H_K ⟶ E_K` of the base-changed quotient is supplied.

The result requires no torus hypothesis, finite extension, separability,
perfectness, restriction on characteristic, or finiteness or smoothness
assumption on the group schemes. It does not assert that the scalar extension
of the constructed section equals the supplied section `σ`.

The construction and proof are internal deductions from the existing
coefficient contraction and vector-action interfaces. First `kernelDefect`
factors the actual scheme morphism
`s(t) s(r) s(tr)⁻¹` through `n`; the all-test kernel equality supplies the
factorization. Its evaluation `defect` commutes with precomposition. The
monomorphism `n` identifies conjugation with the existing normalized-conjugation
action `QuotientHomCocycle.action n q hn (𝟙 E)`.

`IsExtensionCorrection` records the linear cochain equation over every
compatible `K`-algebra. In additive vector coordinates, writing `δ(t,r)` for
the kernel defect and `B` for the extension correction, the equation is
`δ(t,r) + B(tr) = s(t)·B(r) + B(t)`. The action on the right is the published
coordinate action induced from the actual linear vector action. The theorem
`contracted_defect_equation` evaluates this equation over `A ⊗[k] K` and applies
the published `A`-linear coefficient contraction coordinate by coordinate. Its
compatibility with the linear action and the fact that contraction fixes the
left copy of `A` produce the same equation over every original `k`-algebra `A`.

The existing `RelativeRoot.contractedMap` realizes the contracted coordinates
as a regular vector-valued map on the affine scheme `H`. The corrected scheme
section is `n(C(t))⁻¹ s(t)`. The contracted cochain equation implies
`C(tr) = δ(t,r)⁻¹ (s(t)·C(r)) C(t)`. Composing with `n` and applying the actual
conjugation and defect identities proves multiplicativity on affine points.
An affine coordinate presentation of `H.X ⊗ H.X` then proves the universal-pair
identity, which pulls back to every relative test scheme. The correction lies
in the kernel, so the quotient remains the identity. `homOfPoints` packages
these identities into `extensionSectionOfCorrection`, an actual group-scheme
section for any regular extension correction satisfying the cochain equation.

To obtain that equation from `σ`, `range_baseChange_kernel` transports the
original full kernel presentation through the genuine pullback-point
equivalence. `extensionCorrection` factors `s_K σ⁻¹` through `n_K` as an
actual regular map. Affine pullback comparison views its values as original
vector points over each compatible extension algebra. Since `σ` is a group
homomorphism, cancellation of the monomorphism `n` proves precisely the
required cochain identity. Natural vector-coordinate comparison under base
change and `IsLinearVectorCoordinates.coordinateAction_eq` give
`extensionCorrection_equation`. Applying the preceding construction yields
`extensionSectionOfBaseChange` and its exact quotient identity.

The section-defect and promotion-to-group-map arguments adapt proof patterns
developed by Worker 1496 in `Rational.SplitTorusVectorExtension`. Affine
extensionality reuses that module's `PointedCoordinateWeights.affine_hom_ext`.
The coefficient-contraction descent and
extension-section comparison are developed here by Worker 1459. The current
module does not prove existence of an original scheme section, of linear
vector coordinates, or of an extension-field group section. It therefore does
not yet establish torus lift existence or the full solvable maximal-torus
conjugacy theorem.
