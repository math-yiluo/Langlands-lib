# Compact-open containment from a continuous contraction family

This is an internal topological lemma for the dynamic-unipotent compact-open
containment proof. Let `t₀` be a parameter with nontrivial punctured-neighborhood
filter, and let `f : T × H → H` be continuous. Assume `f(t₀,x)=1`, and assume that
for every `t ≠ t₀` the map `f(t,·)` is a topological group automorphism. If `H`
has a compact open subgroup, every compact subset of `H` is contained in a
compact open subgroup.

The implemented proof applies Mathlib's generalized tube lemma to the compact
product `{t₀} × C` inside the open preimage of the given subgroup. It selects a
parameter different from `t₀` in the resulting neighborhood. Pulling the
subgroup back along that parameter's automorphism gives an open subgroup
containing `C`. Its compactness follows by expressing the preimage as the image
under the inverse homeomorphism.

This lemma does not construct the contraction family or a compact open subgroup
for an algebraic group. Those are separate actual-object obligations in the
parent proof. Its proof uses only the stated general topological hypotheses and
Mathlib's tube lemma; no claim of a direct source translation is made.

`Langlands.compactOpenContainingOfContractingFamily` selects such a subgroup
as an element of the subtype of open subgroups that are compact and contain
`C`. The preceding theorem supplies the existence used in this noncomputable
construction. This helper does not itself discharge the actual dynamic-radical
statement; that proof must construct the hypotheses on the canonical objects.
