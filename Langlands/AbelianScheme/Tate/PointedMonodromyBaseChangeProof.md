# Pointed Tate monodromy commutes with base change

This module proves `Langlands.AbelianScheme.Tate.PointedMonodromyBaseChange` by the theorem `Langlands.AbelianScheme.Tate.pointedMonodromyBaseChange`. It imports the separate statement module and preserves all its hypotheses. The implementation is a derived proof using the published finite étale pullback comparison and actual torsion, inverse-limit, and rational Tate constructions.

## Finite group-scheme points

`GroupScheme.baseChangePointsEquiv_act` proves that the pullback adjunction on points of a finite étale group scheme intertwines the action at the new point with the action restricted along `fundamentalGroupMap`. The proof applies `fundamentalGroupMap_smul_left_of_comp` to the first projection of the actual scheme pullback. Equality of the resulting over-category morphisms follows from equality of their underlying morphisms. Finite étaleness of the pullback is obtained from base-change stability.

`GroupScheme.Tate.levelBaseChange_kernel` is the existing point formula for `torsionBaseChangeIso`, expressed through `kernelLevelEquiv`. To prove `levelBaseChange_finiteLevelMonodromy`, represent a finite torsion element by a point of the actual kernel, and use the inverse of `torsionBaseChangeIso` to express that point in the pullback of the old kernel. Naturality of the finite étale action moves the action across this kernel isomorphism. The preceding adjunction equivariance then moves it across the base-change point equivalence. Finally `finiteLevelMonodromy_kernel` returns the identity to the torsion-element coordinates. Both old and new kernels are explicitly required to be finite étale in this general group-scheme lemma.

## Abelian torsion, inverse limits, and rationalization

`levelBaseChange_monodromy` specializes the group-scheme lemma to an abelian scheme. It applies the supplied proposition `htor : TorsionFiniteEtaleStatement` to the abelian scheme and its pullback, using positivity of the order and its invertibility on each base. This proof does not establish `htor`.

`integralBaseChange_monodromy` compares the selected inverse-limit elements by subtype extensionality and equality at every retained positive order. Each coordinate is exactly the finite-level result. The predicate selecting orders remains arbitrary, so the full and prime-to-modulus cases are included without a new construction.

`rationalBaseChange_monodromy` uses tensor-product induction on `ℚ ⊗[ℤ] Integral`. On a pure tensor the equality reduces to integral equivariance; on sums it follows from additivity. The final theorem assembles these three universally quantified results in the order required by `PointedMonodromyBaseChange`.

## Direction, hypotheses, and scope

For `b : S' ⟶ S` and `t : Spec Ω ⟶ S'`, each comparison goes from the carrier over `S'` at `t` to the carrier over `S` at `t ≫ b`. Equivariance on the latter side uses the homomorphism from the fundamental group at `t` to that at `t ≫ b`. The field, fibre-finiteness, torsion finite-étaleness, and invertibility hypotheses are exactly those in the statement. No algebraic closedness or connectedness is added to this formal compatibility result.

The source and provenance of the statement are documented in its paired Markdown: Edixhoven–van der Geer–Moonen, *Abelian Varieties*, Chapter X (10.30), printed pp.151–152 / PDF pp.155–156. The proof here follows the imported categorical pullback formulas rather than a separate argument from the literature. It proves algebraic equivariance only. It supplies no surjectivity of the fundamental-group homomorphism, bijection of fixed-orbit sets under arbitrary base change, rational topology result, Weil-pairing compatibility, or scalar-witness independence.
