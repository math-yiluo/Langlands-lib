# Reduction of the relative reductive quotient to existence and annihilation

Worker 596.

This is an internal decomposition of the published proposition
`Langlands.GroupScheme.RelativeParabolicReductiveQuotientStatement.{u}`.
It introduces three `Prop`-valued definitions and proves that the third is
equivalent to the published proposition. It does not prove either geometric
input, and therefore does not prove the unconditional quotient theorem.

`RelativeParabolicReductiveQuotientExistenceStatement` retains all the
quantifiers and hypotheses of the published target and asks for a reductive
group scheme `M` and an actual represented fppf quotient `q : P ⟶ M` with
full kernel range `range r`. It omits the universal property.

`RelativeParabolicRadicalAnnihilationStatement` uses the same arbitrary
scheme `S`, groups `G`, `P`, `U`, maps `i`, `r`, and reductivity, parabolicity
and radical hypotheses. It asserts that for every reductive `H` and every
homomorphism `f : P ⟶ H` surjective on the underlying schemes, `r ≫ f = 0`.
This is an equality of group-scheme homomorphisms over `S`, including a
nonreduced base. Fibrewise vanishing alone is not its conclusion.

`RelativeParabolicReductiveQuotientInputsStatement` is the conjunction of
these two statements. All three are universe-polymorphic in `u`.

## Implemented proof

The auxiliary lemmas in `RelativeRoot.IsFppfQuotient` work over every scheme.
For any `q : P ⟶ M` satisfying
`IsFppfQuotient (SubgroupFunctor.range r) q`, `subgroup_comp_eq_zero`
evaluates the full kernel-range equality at the identity point of `U` to
show `r ≫ q = 0`. If `r ≫ f = 0`, `kernel_comp_eq_zero` evaluates the same
range equality on the actual kernel scheme of `q`. Its inclusion factors
through `r` on that test scheme, so its composite with `f` is zero.
These arguments do not require that `r` is monic.

If `q` is also quasi-compact, `existsUnique_factor` applies the published
`FpqcHomDescent.hom`, `.fac` and `.unique` to the actual full kernel.
It applies to every target group scheme `H` and every `f` killing `r`;
neither reductivity of `H` nor surjectivity of `f` is needed for this
descent lemma. `existsUnique_factor_iff` proves the converse using
`r ≫ q = 0`.

`relativeParabolicReductiveQuotientReduction` takes both geometric inputs.
The existence input gives `M`, `q` and their properties. The structure
maps of `P` and `M` are affine. The composite of `q` with the latter
structure map is the former, and hence is quasi-compact. Since the
structure map of `M` is quasi-separated, `QuasiCompact.of_comp` gives
quasi-compactness of `q`. The annihilation input and the auxiliary descent
lemma then give the exact universal property required by the published
target.

`relativeParabolicReductiveQuotient_iff_inputs` also proves necessity.
Existence follows by dropping the universal-property conjunct. For
annihilation, the universal property writes `f = q ≫ g`; composing
with `r` gives zero.

## Provenance and remaining obligations

The definitions are internal proof interfaces derived directly from the
published target, rather than independent transcriptions of a new source.
The equivalence theorem verifies this provenance in Lean. Its motivation
is the separation between quotient representability and annihilation in
Conrad's Corollary 5.2.5, as documented in the published target's
[Markdown](ReductiveQuotientStatement.md).

The quotient must still be constructed and shown reductive over every
base scheme. Annihilation must still be proved for scheme-surjective maps
over every base. This module assumes each of those results only as the
explicit parameter of a conditional theorem; it adds no axiom and
does not change the target or its imports.
