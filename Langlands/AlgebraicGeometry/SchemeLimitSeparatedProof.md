# Actual diagonal comparison for separatedness descent

Worker 105 authored the Lean proof, reused unchanged here by Worker 148.

`relativeSeparatednessDescent` proves exactly the published proposition
`Langlands.AlgebraicGeometry.AffineLimit.RelativeSeparatednessDescent`.
It retains an arbitrary universe `u`, an actual small cofiltered category
`I`, a diagram `D : I ⥤ Scheme` of affine schemes, an affine base `S`,
and a natural transformation `t` from `D` to the constant diagram at `S`.
The relative maps `a : X ⟶ S`, `b : Y ⟶ S` and `f : X ⟶ Y` satisfy
`f ≫ b = a`. The hypotheses are precisely quasi-compactness and
quasi-separatedness of `f` and quasi-compactness of `a`. Given a cone `c`,
its actual `IsLimit` witness, and `p : c.pt ⟶ S` with
`c.π.app i ≫ t.app i = p` for every `i`, the theorem states that
`baseChangeMap a b f w p` is separated if and only if
`baseChangeMap a b f w (t.app i)` is separated for some `i`.
The models `X` and `Y` may be nonaffine and nonseparated; no finite-type
hypothesis on `f` or injectivity hypothesis on transitions is imposed.

The proof constructs `baseChangeDiagonalObjIso` by applying
`baseChangeMap_square_isPullback` to the actual self-pullback square
of the relative morphism. The two projections carry the original
source structure map to the same base, as proved in
`selfPullback_structure`. The resulting `isoPullback` identifies the
base change of the original diagonal object with the actual diagonal
object of the base-changed map. Its two projection identities are
recorded explicitly.

`baseChange_diagonal_comp_iso` checks both projections, then the two
projections of each base change, to show that the actual base-changed
diagonal followed by this isomorphism is the actual diagonal of the
base-changed map. `isSeparated_baseChangeMap_iff` uses the definition
of separatedness and invariance of closed immersion under an
isomorphism of the target.

The final theorem applies the imported `relativeClosedImmersionDescent`
to `pullback.diagonal f`, whose target structure map is
`pullback.fst f f ≫ a`. The diagonal is an immersion, so is locally of
finite type, and is a monomorphism, so is quasi-separated.
Quasi-separatedness of `f` makes its diagonal quasi-compact.
Quasi-compactness of `f` and `a` makes the target structure map
quasi-compact. The comparison lemma rewrites both the limiting
closed-immersion predicate and every stage predicate as separatedness.
The predecessor theorem supplies both directions of the equivalence.

This is a derived relative form of the separatedness clause of Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
printed pp. 5–6, Theorem 3.4(2); the paired statement gives the exact
source formulation with finitely presented models. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The weaker relative hypotheses follow from the diagonal argument above.
The proof uses actual pullbacks, their projection identities and the
given actual limit cone. The original filtered-ring specialization and
the other source clauses remain obligations of the parent task.
Only this new proof pair is submitted; the predecessor proof and target
are imported from the published Library without modification.
