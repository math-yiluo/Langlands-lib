# Discrete-series classes and unramified twist orbits

The source is J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)* (2003), III.1, printed p.263 (PDF p.29), and
III.7, printed p.273 (PDF p.39), source ID `waldspurger-2003-plancherel`.
III.1 integrates square norms on \(A_G\backslash G\). III.7 defines \(E_2(G)\)
as the classes of irreducible admissible square-integrable representations,
the unitary unramified twist action, and its orbit parameterization by a
stabilizer quotient.

## Inputs and class construction

The group and representation-carrier universes remain independent. The
topological group, normal central subgroup \(A\), quotient measurable space,
Haar measure \(\mu\), and indexed positive norm characters \(\nu_i\) are explicit.
For the source application \(A\) must be the actual rational points of the
maximal split central torus and \(\nu_i\) all rational absolute-value characters.
This module does not realize either specialization.

`IsDiscreteSeriesClass` descends
`IsSquareIntegrableModCentralSubgroup A hA ρ μ` to the canonical
`SmoothDualClass`. It uses a quotient lift and the proved invariance under actual
representation equivalence, obtained from an isomorphism in the canonical full
subcategory. `isDiscreteSeriesClass_mk` gives its exact value on an actual object.
`DiscreteSeriesClass` is the subtype of those canonical classes satisfying this
condition. Irreducibility, smoothness and admissibility are retained by the
ambient canonical class; square-integrability includes its existing unitary
full-central-character witness. `discreteSeriesClass` sends an actual object with
the specified square-integrability proof to that subtype.

## Actual twisting and orbits

The action additionally requires `NonarchimedeanGroup G`, an identity-neighborhood
basis of open subgroups including the topological-group laws. Each continuous
complex character then has open kernel by the published continuous-character
theorem, so it acts by the canonical `SmoothDualClass.twist`.
`unramifiedTwistAction` is this action of all the constructed unramified
characters on the entire smooth dual. `unramifiedTwistStabilizer` is its actual
stabilizer subgroup.

`isDiscreteSeriesClass_unitaryTwist` descends the coefficient-norm twist
comparison to classes. It proves that unitary twists preserve the prescribed
square-integrability condition. `unitaryUnramifiedTwistAction` therefore acts on
the discrete-series subtype itself; its laws follow from the canonical
identity- and successive-twist identities. `unitaryUnramified_smul_val` identifies
its underlying class with the actual representation twist.

`discreteSeriesOrbit` is the actual orbit subset, `discreteSeriesStabilizer`
the unitary stabilizer subgroup, and `DiscreteSeriesOrbitClass` the quotient by
the actual orbit relation. `discreteSeriesOrbitEquiv` applies Mathlib's
orbit-stabilizer equivalence to this action. Its formula on a character is the
actual twisted class, as `discreteSeriesOrbitEquiv_mk` states. The two membership
lemmas expose exactly the twist and fixed-class conditions.

The quotient lift, preservation and group-action laws, and orbit-stabilizer
adapter are internal construction laws. Their proofs use the imported
representation-equivalence and twist comparisons; they do not use III.7's
Bernstein-center result or assume any finiteness theorem.

## Remaining source obligations

The source writes the stabilizer inside the full group \(X(G)\) and asserts its
finiteness. This module separately records that full stabilizer and the unitary
stabilizer used in its orbit quotient. It proves neither finiteness nor their
identification. For a generic indexed family these assertions need not hold.
No complex torus, smooth orbit manifold, orbit Haar measure, polynomial family,
formal degree, normalization or spectral finiteness is supplied. The actual
rational-character and split-center comparisons, including comparison with the
Library full-center predicate, remain separate obligations.
