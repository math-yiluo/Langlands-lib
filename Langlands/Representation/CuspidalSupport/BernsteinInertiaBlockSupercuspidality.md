# Same-Levi inertia blocks of a Bernstein datum are supercuspidal

Author: Worker 5313, Task 5313 (`03088b22-a403-46ae-a6ed-6dea22f5472a`).

This is a derived supporting result for the proof of Renard VI.7.2
(David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, printed
pp.181–184 / PDF pp.187–190). In that proof the inducing representations
`τ` of the Levi `M` lie in the inertia block `M(M)_{[M,ρ]_M}` of a
supercuspidal `ρ`, and they are used as cuspidal representations of `M`.
Their cuspidality comes from the decomposition of VI.3.5 (printed
pp.146–147 / PDF pp.152–153) of `M(M)` into a cuspidal part and a part
without cuspidal subquotients. This module proves that step. It is
conditional on the VI.3.5 whole-category statement
`RationalWholeCuspidalCategoryDecompositionStatement.{uF, max uF uV}`,
which is a hypothesis here and is not proved.

## Declarations

- `bernsteinLeviRep_isSupercuspidal_of_isLeviCuspidal`: for an actual
  standard Levi `bernsteinLeviScheme i ν I` of a Bernstein standard family
  and any smooth representation `τ` of its rational points, literal
  inside-Levi cuspidality of `bernsteinLiteralLeviRep i ν I τ` implies
  `RepresentedParabolic.IsSupercuspidal τ`, that is, vanishing of the
  normalized Jacquet module along every proper actual represented parabolic
  of the Levi. The proof is the published proof of
  `BernsteinCuspidalDatum.isSupercuspidal` with the datum's cuspidality
  replaced by the hypothesis: `rationalLeviCuspidalityTransport` moves the
  literal cuspidality to the Levi's own standard family, and
  `RepresentedParabolic.isSupercuspidal_of_isCuspidal` passes to all proper
  represented parabolics.
- `isLeviCuspidal_of_rationalInertiaBlockProperty`: for a Bernstein datum
  `a` and `τ` with `rationalInertiaBlockProperty (bernsteinLeviScheme i ν
  a.roots) a.representation τ` (every irreducible subquotient of `τ` is
  inertia-related to `a.representation`), the literal representation
  `bernsteinLiteralLeviRep i ν a.roots τ` is cuspidal for the literal
  proper standard parabolics of the Levi.
- `isSupercuspidal_of_rationalInertiaBlockProperty`: under the same
  hypotheses, `RepresentedParabolic.IsSupercuspidal τ`. It composes the two
  results above.

## Proof of `isLeviCuspidal_of_rationalInertiaBlockProperty`

The published `bernsteinLeviCuspidalSplitting_of_wholeStatement` turns the
VI.3.5 hypothesis into a cuspidal/remainder splitting of the literal
representation `A`: a coproduct cofan `A = Y true ⊔ Y false` with
`Y true` cuspidal and no nonzero subquotient of `Y false` cuspidal.

1. The cofan's descent of `(𝟙, 0)` is a retraction of the injection of
   `Y false`, so this injection is injective and `Y false` is a subquotient
   of `A`.
2. `Y false` is zero. Otherwise it has an irreducible subquotient `D`
   (`SmoothRep.exists_isIrreducible_isSubquotient_of_nontrivial`), which is
   a subquotient of `A`. Its pullback `D'` to the Levi scheme's points is
   irreducible and a subquotient of `τ`, so it is inertia-related to
   `a.representation`. The published
   `isLeviCuspidal_bernsteinLiteralLeviRep_of_inertia` makes the literal
   form of `D'` cuspidal. That form is isomorphic to `D` by
   `SmoothRep.pullbackSymmIso`, so `D` is cuspidal and nonzero. This
   contradicts the remainder condition.
3. Since `Y false` is zero, the injection of `Y false` is zero. The
   cofan's descent of `(0, 𝟙)` is then a two-sided inverse of the
   injection of `Y true`, so `A ≅ Y true`.
4. Each proper standard Jacquet functor carries this isomorphism to a
   linear equivalence, so every proper Jacquet module of `A` is a
   subsingleton because that of `Y true` is.

No admissibility, finite-length or finite-generation hypothesis is used.
The field and carrier universes are those of the Bernstein targets: the
datum and `τ` have carriers in `Type (max uF uV)`.
