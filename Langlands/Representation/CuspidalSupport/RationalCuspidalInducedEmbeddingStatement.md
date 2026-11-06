# Finite induced-cuspidal embedding on actual rational points

Worker 1751. This unit states an existential consequence of Renard VI.7.2's
I/R unit embedding. It supplies no proof, chosen projector, adjunction, or
category decomposition. The underlying normalized induction and finite direct
sum are the existing actual constructions.

The registered original is David Renard, *Représentations des groupes réductifs
p-adiques*, version dated 9 July 2026,
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
VI.7.2, printed pp.182–183 / PDF pp.188–189, defines Cusp(G), I and R and proves
that the adjunction unit V → IR(V) is injective. The paragraph immediately
after the Lemma concludes that every smooth representation embeds in a direct
sum over the standard parabolics of induced cuspidal representations. The
standard parabolic family is finite. This consequence, rather than the entire
I/R functor construction or Bernstein decomposition theorem, is the target here.

`FiniteCuspidalInducedEmbeddingTarget` is a proposition for a finite standard
family P,M,U with actual semidirect decompositions, closed radicals and Levis,
and actual standard parabolics inside each Levi. For every smooth complex
representation E it asks for one smooth cuspidal representation τ(I) of each
standard Levi M(I), together with an injective actual intertwining linear map
from E to the actual algebraic direct sum of the normalized induced τ(I).
Cuspidality is exactly the published `IsLeviCuspidal`, which tests vanishing of
normalized Jacquet modules for every proper standard parabolic of that Levi.
The inducing representations may be zero. They need not be irreducible,
admissible, finitely generated or of finite length.

The target's index is `Finset κ`, where κ is finite. The direct sum is therefore
finite, even when the inducing carriers are infinite dimensional. Its summands
are the existing `normalizedInductionFunctor` objects and its action is the
existing `SmoothRep.directSum` action. No arbitrary representation or alternative
induction space replaces these constructions. An actual intertwining map is
used so the source carrier universe can remain independent of the larger full
function-space target universe. The source is in `Type uV`; inducing and target
carriers are in `Type (max uI uG uV)`.

`RationalCuspidalInducedEmbeddingStatement.{u,v}` applies this proposition to the
actual standard rational-point family of a maximal split torus and a generic
cocharacter of an arbitrary connected reductive group scheme over a
nonarchimedean local field. It retains the actual standard cocharacter and
standard Levi-intersection assertions, the relative-root assertion, closedness
of the actual Levis and radicals, and the canonical point topology's local
compactness, nonarchimedean group and Hausdorff hypotheses. These are structural
comparisons; no representation-theoretic decomposition, adjunction faithfulness
or embedding is assumed. The source carrier universe v is independent of the
field/group universe u. The inducing and target carriers are in `Type (max u v)` because the actual
simple-root index is in the field/group universe u.

The adaptation to the actual standard-family and full function models, the
explicit universe enlargement, and the formulation by existence of an injective
intertwiner are internal. The source proves the stronger statement via its
specific I/R unit. This target neither chooses that unit nor asserts that an
arbitrary finite family has the embedding property. Its proof remains a
separate obligation. The intended compression application additionally needs
actual cuspidal inertia decomposition, compact-level visibility and generator
stability; none follows from this statement alone.
