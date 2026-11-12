# Normal quotients, Hecke induction and adjunction

Source: Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, III.2.10, (III.2.10.1)–(III.2.10.2), Proposition
and Corollary, printed pp.80–82 / PDF pp.86–88.

`NormalQuotientStatements` is a closed proposition containing three targets.
It supplies no proof or comparison instance. Groups are Hausdorff, locally
compact and nonarchimedean; `N` is an actual closed normal subgroup and
`M = P/N` carries its quotient topology. Both Haar measures remain explicit
in the Hecke comparison, with the given Borel measurable structures.

`NormalQuotientHeckeStatement` first asserts a natural isomorphism between
the actual `pseudoF` and `F` for the quotient projection `q : P → M`.
These are precisely the Chapter I functors specialized to the already
constructed Hecke bimodule. It then specifies (III.2.10.1). For a compact
open subgroup `K`, put `KM = q(K)` and let `eP`, `eM` be the normalized
indicators for the respective Haar measures. The assertion is

`T · (eP * l(p)eP) = T * (eM * l(q(p))eM)`.

The product `eP * l(p)eP` is exactly the density of the distribution
`eK * δp * eK`, called `a_{p,K}` in the source: `l(p)eP` is left translation
of the existing normalized indicator. Thus this formula uses the source's
averaged Dirac distributions without constructing an unrelated algebra.
The right action is the actual `rightModule`, encoded with opposite scalars.
Compactness and openness of `KM` are proved in `NormalQuotientModels`.

Next the proposition asserts a natural isomorphism `α` from actual
coinvariants followed by their integrated Hecke action to actual tensor
induction `H(M) ⊗_{H(P)} W`. It prescribes both directions:

- If `K` fixes `w`, then `α([w]) = eKM ⊗ w`, exactly (III.2.10.2), for every
  such compact open `K`. Choice independence is consequently a conclusion.
- The inverse sends each original elementary tensor `T ⊗ w` to `T · [w]`,
  where the action is the actual integrated action on the quotient.

`coinvariantHeckeFunctor` and `quotientTensorHeckeFunctor` are only named
composites of the existing functors. `quotientTensorTmul` exposes the original
`NonUnitalModuleTensor.tmul` with the exact same right and left actions.
Existence, balancing, bijectivity and naturality of the comparison are
conclusions, never supplied certificates. The carrier universe `max uP v`
is stable under the Chapter I tensor construction; the group and carrier
universe parameters remain independent.

`NormalQuotientAdjunctionStatement` is the Proposition's adjunction:
actual `j_N` is left adjoint to continuous pullback along `q`. This target
uses arbitrary carrier universe `v`, since these two functors preserve it.

`NormalQuotientInductionAdjunctionStatement` is the Corollary. For a closed
subgroup `P` of `G`, the left functor is restriction from `G` to `P` followed
by the actual `j_N`; the right functor is quotient pullback followed by the
existing smooth function induction `Ind_P^G`. Restriction on the left makes
explicit the restriction implicit in the source's notation `V ↦ V_N` for a
`G` representation. Its carrier universe `max uG v` is stable under function
induction. Neither an Hecke-equivalence proof nor an adjunction is an input.

These targets include the source's full normal-quotient statements, rather
than only the case of a chosen split semidirect product. Their proofs belong
to separate proof tasks after publication.
