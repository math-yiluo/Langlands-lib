# Geometric reduction for simple connectedness under field extension

Worker 416. This is an internal decomposition of the exact field-extension
statement, using the Library's actual group-scheme base change. It does not
establish either geometric input or the unconditional field-extension theorem.
No additional field hypothesis is imposed on that final theorem.

`IsSimplyConnectedAlgebraicClosureAscentStatement` asks that simple connectedness
ascend from every field to its algebraic closure.
`IsSimplyConnectedAlgClosedFieldExtensionStatement` asks that it ascend along
every extension between algebraically closed fields. Both statements quantify
at the arbitrary universe `u`. Their conjunction is
`SimplyConnectedGeometricInputsStatement`.

`IsSimplyConnected.of_fieldExtension` proves conditional reflection for a group
already known to be semisimple. Its other inputs are the exact global
semisimplicity-preservation and central-isogeny-preservation statements. Given
an incoming semisimple central isogeny over the smaller field, the two inputs
make its actual base change an incoming semisimple central isogeny. Simple
connectedness over the larger field makes that map an isomorphism. The
published `fieldExtension_fpqc` and `isIso_of_baseChange` reflect invertibility
to the original map. This only descends a morphism already defined over the
smaller field.

`isSimplyConnectedFieldExtension_of_geometricInputs` proves the conditional
assembly. For an arbitrary extension `K/k`, `IsAlgClosed.lift` supplies a
`k`-algebra embedding of the algebraic closure of `k` into the algebraic
closure of `K`, where the latter is given the composite `k`-algebra structure.
The embedding's compatibility with the scalar maps identifies the two
composite maps of spectra. The first geometric input gives simple connectedness
over the closure of `k`; the second gives it over the closure of `K`.
`baseChangeCompIso` transports this conclusion to the algebraic-closure base
change of `G_K`. The reflection lemma then gives simple connectedness of
`G_K`, whose semisimplicity is supplied by the preservation input.

The proof uses the full published `IsSimplyConnected` and central-isogeny
predicates, including their scheme-theoretic kernels and all test schemes.
It never assumes that an arbitrary incoming isogeny over `K` descends to `k`.
The geometric inputs and both preservation inputs remain explicit hypotheses;
this module is not an unconditional proof of any of them.

The statements and reduction are derived implementation interfaces, rather
than quotations of a literature theorem. Their justification is the implemented
algebraic-closure square, the existing base-change comparison isomorphism, and
the Library's fpqc reflection lemma, which specializes Mathlib's descent of
scheme isomorphisms. No external structure theorem about reductive groups is
used in these conditional proofs.
