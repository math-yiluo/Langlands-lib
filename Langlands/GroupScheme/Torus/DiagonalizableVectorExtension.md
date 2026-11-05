# Group sections of diagonalizable extensions by linear vector groups

Worker 1552. This internal construction generalizes the published `Rational.SplitTorusVectorExtension` argument to `Diagonalizable.groupScheme k Λ` for any abelian character group `Λ`, including torsion. It works over any field `k`, with no finite generation assumption on `Λ`.

## Data and scope

Write `D = Diagonalizable.groupScheme (CommRingCat.of k) Λ`. The inputs are group schemes `N` and `E` over `Spec k`, an affine structure map for `N`, and the following data:

- A homomorphism `i : N ⟶ E` that is a monomorphism on underlying schemes, whose range is normalized by every point of `E`.
- A homomorphism `q : E ⟶ D.toGrp` whose kernel on every test scheme is exactly the range of `i` (`hker`).
- A section `s : D.X ⟶ E.X` as schemes, with `s ≫ q.hom.hom = 𝟙`.
- Group isomorphisms `e T : (T ⟶ N.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤))` on all test schemes. The condition `he : RelativeRoot.IsLinearVectorCoordinates (splitTorus.conj i hn) e` requires these coordinates to be natural and the conjugation action to be linear over the ring of global functions.

These are explicit premises of the construction. The module proves no scheme-section existence theorem and does not treat proper closed additive subgroups without vector coordinates. The unrestricted `LinearAdditiveExtensionSplittingStatement` remains a separate obligation.

## Main construction

`diagonalizableVectorExtension.extensionSection` is an actual homomorphism `D.toGrp ⟶ E`. Its companion theorem `extensionSection_comp` proves that its composite with `q` is the identity. The theorem `exists_extensionSection` states the existence form.

`sectionDefect` is the morphism on `D.X × D.X` given on points by `s(t) s(r) s(tr)⁻¹`. The section equation makes this morphism lie in the range of `i`; `kernelDefect` chooses its lift and `defect t r` evaluates that lift on a pair of points. Cancelling the monomorphism `i` proves its defining equation, naturality, and the two-cocycle identity. The conjugation action and its comparison with conjugation in `E` are imported as `splitTorus.conj` and `splitTorus.conj_act_comp`; both are already general in `E` and `N`.

For a coefficient algebra `A`, `coefficientInclusion` maps `A` into `A[Λ]`, and `averagingPoint` is the universal diagonalizable point with coefficients extended from `k` to `A`. The vector `averageVector t` consists of the degree-zero coefficients of `defect t averagingPoint`, with `t` extended as a constant point. The point `averagePoint t` is obtained by applying the inverse vector-coordinate isomorphism.

`averageVector_translate` uses `Torus.DiagonalizableAveraging` to show that translating the averaging variable does not change this vector. The theorem `coeff_zero_act` shows that the linear conjugation action of a constant point commutes with coefficient extraction, using the published `AutomorphicAction.coordinateAction_coeff` from `Rational.SplitTorusVectorCocycle`. Taking degree-zero coefficients of the cocycle identity then proves `defect_add_averageVector`: the original cocycle is the coboundary of the average. In multiplicative notation, `averagePoint_mul` gives the correction identity for `averagePoint`.

The corrected section is `sectionPoint t = i(averagePoint t)⁻¹ * s(t)`. The correction identity proves its multiplicativity. Naturality of the defect, vector coordinates and coefficient extraction proves that this point construction commutes with every algebra map `A →ₐ[k] B`. The affine Yoneda helpers `PointedCoordinateWeights.homOfAffinePoints` and `comp_homOfAffinePoints`, imported from `Rational.SplitTorusVectorExtension`, give the actual morphism `sectionHom`. Affineness of `D` comes from `Diagonalizable.isAffineHom`. Multiplicativity is checked on affine points of the universal product, then transported to every test scheme. Finally `homOfPoints` produces `extensionSection`, and the original scheme-section equation proves `extensionSection_comp`.

## Provenance

This is an internal generalization of the existing split-torus construction, preserving its defect convention, correction formula and scheme-valued Yoneda argument. The new averaging variable is the group algebra of the entire character group, and its translation invariance is supplied by `Diagonalizable.Averaging`. Coefficient-zero projection uses no division by an order and applies unchanged to torsion characters in positive characteristic. The implementation invokes no external cohomology-vanishing theorem.
