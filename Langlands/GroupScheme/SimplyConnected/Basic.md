# Algebraically simply connected semisimple groups and actual central covers

For every field `k : Type u`, `IsSimplyConnected G` requires the actual group
scheme `G` to be semisimple and requires every central isogeny `H → G` from a
semisimple group `H` over `k` to be an isomorphism. The imported
`IsSemisimple` uses the existing geometric-fibre reductivity predicate and
finiteness of the full scheme-theoretic centre. The imported
`IsCentralIsogeny` uses finite, flat, surjective and locally finitely presented
scheme morphisms with central actual kernel. There is no perfectness,
characteristic or small-universe restriction. This is algebraic simple
connectedness, with no topological condition.

The source definition is the paragraph immediately before CGP,
*Pseudo-reductive groups*, second edition (2015), Corollary A.4.11, printed
p.500 (PDF p.526). That paragraph tests central isogenies from connected
semisimple groups. Corollary A.4.11(1), printed pp.500-501 (PDF pp.526-527),
describes existence, uniqueness and field-extension compatibility of the
simply connected central cover. Milne, *Algebraic Groups* (2017), Proposition
19.15, printed p.401 (PDF p.417), gives the same central-isogeny criterion in
the semisimple case. No retained project errata note for CGP was found. The
registered official Milne errata of 2026-11-02 was read in full; it has no
correction to Proposition 19.15.

`HasCentralCoverUniversalProperty π` says that every incoming central isogeny
`q : H → G` from a semisimple `H` has a unique group-scheme homomorphism
`a : C → H` satisfying `a ≫ q = π`. This is a derived semisimple packaging of
Milne's universal property in Proposition 18.8, printed p.389 (PDF p.405),
with arrow direction as corrected in the registered errata: the factorization
lands in the source of the incoming cover. We explicitly retain this law as
a property; this module does not prove the structure results needed to deduce
it from simple connectedness alone.

`IsSimplyConnectedCover π` requires a semisimple target, a simply connected
source, a central isogeny `π`, and that universal property. It is a proposition
about a supplied actual homomorphism. It chooses no group, proves no cover
exists and asserts no base-change theorem. The existence and base-change
results in CGP remain separate obligations.

The implemented intrinsic lemmas use only these interfaces. Simple
connectedness transports along a group-scheme isomorphism by postcomposing
an incoming central isogeny and cancelling the isomorphism. The helper
`CentralIsogeny.Transport` gives the source and target comparisons for the
central-isogeny predicate. For a supplied cover, `lift` chooses the unique
factorization promised by its universal property; `lift_comp`, `lift_unique`
and `hom_ext` express that law. Applying it to two supplied covers in both
directions gives the isomorphism `IsSimplyConnectedCover.iso`. Uniqueness of
factorizations shows the composites are identities and proves `iso_unique`.
Thus the canonical comparison is constructed from explicit cover data, without
an unproved existence choice.
