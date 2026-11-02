# Common Hilbert completion for finite and compact automorphic actions

This internal construction supplies a common Hilbert completion for the two
group actions of an `OperatorUnitaryFormCore`. Its carrier, two groups and
infinitesimal index have independent universes. Both groups are groups, the
carrier is a complex module, and a single positive form is supplied. The
infinitesimal skew condition is retained on the original algebraic carrier.

For an actual `S : OperatorRealization F n`, the existing `S.UnitaryForm` is
definitionally this core with `S.finiteRepresentation`,
`S.compactRepresentation` and the actual real infinitesimal generators as its
parameters. Thus all the constructors below apply directly to
`b : S.UnitaryForm`. The alias
`OperatorRealization.UnitaryForm.HilbertCompletion b` exposes this actual
specialization for any number-field universe and any natural rank. The other
constructors and laws are in `OperatorUnitaryFormCore`; there are no duplicated
concrete wrappers for them.

`HilbertCompletion b` is the published uniform completion
`b.finiteForm.HilbertCompletion`. Its norm, complex inner product and
completeness come from that construction and Mathlib.
`OperatorUnitaryFormCore.toHilbert b` embeds the supplied algebraic carrier
complex linearly, injectively and with dense range. Its formulas are

\[
 \langle j(f),j(g)\rangle=B(f,g),\qquad
 \|j(f)\|=\sqrt{\operatorname{Re} B(f,f)}.
\]

The norm is placed on the existing form-dependent copy of the carrier.
There is no identification with an incoming function-space topology.

`completedFiniteOperator b d` extends the first group action to a
complex-linear isometric equivalence. `completedCompactOperator b k`
extends the second action on the **same** Hilbert space.
`compactInvariantForm` retains definitionally the positive Hermitian core of
`b.finiteForm`, using the supplied second-action invariance proof. No second
inner product or comparison choice is introduced. For an actual automorphic
form core these are precisely the finite and standard infinite compact
translations. For general cores the names label the first and second actions
and impose no extra arithmetic interpretation.

The inverse formulas identify each operator's inverse with the extension at
the inverse group element. Every operator preserves norm and inner product
and is continuous by its `LinearIsometryEquiv` structure.
`completedFiniteRepresentation` and `completedCompactRepresentation`
bundle the extensions as representations. The application lemmas identify
them with the isometric operators. On embedded vectors their formulas are

\[
 P(d)j(f)=j(\rho(d)f),\qquad R(k)j(f)=j(\kappa(k)f).
\]

Under the actual automorphic specialization these extend the existing
positive right translations on functions, with their original convention.

`completedFiniteOperator_compactOperator` requires the original two actions
to commute and proves their completed operators commute. The proof extends
equality from the dense embedded carrier using continuity of both
compositions. On an embedded vector the extension formulas reduce the result
to the supplied commutation equation.
`completedFiniteRepresentation_compactRepresentation` gives the same identity
through the representation interface. For `b : S.UnitaryForm`, the
commutation input is the published
`S.finiteRepresentation_compactRepresentation`.

If the first group is a topological group and its algebraic representation
is smooth, `continuous_completedFiniteOrbit` proves continuity of every
completed orbit. It applies the published generic positive-form completion
theorem. `continuous_completedFiniteAction` proves joint continuity in the
group and Hilbert vector by Mathlib's
`continuous_prod_of_continuous_lipschitzWith'`: the orbit maps are continuous
and all vector maps are Lipschitz with constant one, since they are
isometries. For the actual finite adelic action the required smoothness input
is the already proved `S.finiteRepresentation_isSmooth`, and the group
topology is its existing finite adelic topology.

The provenance is internal composition of the published operator form,
finite/compact compatibility and generic positive-form completion
constructions. Their arbitrary-carrier laws specialize to the actual
automorphic inputs without changing the carrier or actions. No new
original-literature identification or general form-existence theorem is
claimed. No extension of differential operators is constructed. Compact
orbit continuity, archimedean globalization, spectral occurrence, invariant
integral formulas, Hilbert irreducibility and recovery of all smooth vectors
remain separate obligations.
