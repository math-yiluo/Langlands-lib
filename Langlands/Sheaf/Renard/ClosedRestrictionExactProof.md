# Exactness for compact sections and their algebraic duals

Worker 337, Task 5960. Module
`Langlands.Sheaf.Renard.ClosedRestrictionExactProof`, namespace
`Langlands.Sheaf.Renard.ClosedRestriction`.

The theorem `closedRestrictionExact` proves the existing proposition
`ClosedRestrictionExactStatement` with exactly that type and no universe
parameters. It treats every locally profinite `X : Type`, complex vector sheaf
`F`, and open subset `U`, with closed complement `Z`. The six clauses are compact
extension by zero with uniqueness, the kernel description for restriction to
`Z`, surjectivity of restriction, injectivity of its algebraic transpose, the
dual kernel/range description, and extension of every algebraic linear form on
compact sections over `U`. No finite-dimensionality or compactness of `X` is
assumed.

## Source and provenance

The target is Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, II.2.5, Proposition, printed p.42 / PDF p.48. The
registered source is `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
readable at `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The source identifies the compact-section exact sequence and its algebraic dual.
The published [target companion](ClosedRestrictionExactStatements.md) records
the correspondence of its six clauses with that proposition.

All helpers in this module are derived results for the target's existing
constructions. The proof uses the published actual sheaf gluing construction in
[CompactGerms](../CompactGerms.md), the compact-open neighborhood result in
[CompactSectionStalksProof](CompactSectionStalksProof.md), and finite disjoint
compact-open refinement in
[LocallyProfiniteProof](../../Topology/LocallyProfiniteProof.md). Its final
linear algebra uses Mathlib's `LinearAlgebra.Dual.Lemmas`. The target's
Lean/Markdown pair and every pair it imports remain unchanged.

## Implemented proof

1. **Compare the support on the open subspace.** `open_germ_eq_zero_iff` proves
   that a section of the actual open restriction has zero germ at `y : U` if and
   only if the corresponding original-sheaf germ at `y.val` is zero. Both
   directions use the local equality criterion for Mathlib's stalk colimits,
   transporting smaller neighborhoods through the open embedding.
   `open_support_eq` identifies the support with the nonzero original germs.
   `open_support_restrict` then identifies the support of a restricted global
   section with the subtype preimage of its original support.

2. **Extend by zero with compact support.** `germ_compactExtension` and
   `germ_compactExtension_of_notMem` give the germs of the Library's compact
   clopen extension on and off its defining open. For a compact section over
   `U`, map its support into `X` and place this compact set inside a compact
   open `W` contained in `U`. In a Hausdorff space `W` is also closed. Restrict
   the section to `W` and use `CompactGerms.compactExtension`, which is obtained
   by actual sheaf gluing. On `U` outside `W` the original section has zero
   germ, because its support lies in `W`. This proves both conditions of
   `IsZeroExtension`. The extension has compact support by the Library
   construction. `zeroExtension_unique` compares germs on `U` by restriction,
   and off `U` by the zero condition, then uses sheaf separation.
   `exists_zeroExtension` packages this as clause 1.

3. **Describe the restriction kernel.** If a compact global section has zero
   restriction to `Z`, all its germs outside `U` vanish. Its support is thus
   contained in `U`. The support comparison from step 1 and the compactness
   preimage theorem for the subtype embedding show that restriction to `U`
   has compact support. It satisfies `IsZeroExtension` by construction.
   `kernel_zeroExtension` proves clause 2.

4. **Extend a compact family of germs on a closed subset.**
   `restrictToClosed_surjective` works for any closed `Z`. For a family in
   `closedCompactSections F Z`, choose one local representing open and section
   around each `z : Z`. The image in `X` of its support is compact. Apply
   `finiteDisjointRefinement` to these representing opens, obtaining finitely
   many pairwise disjoint compact opens `W_j` covering that support and
   subordinate to the representing opens. Restrict the corresponding
   representatives to `W_j`, extend each by zero using the same clopen gluing
   construction, and sum in `CompactSupport.submodule`. At a point of `Z`
   inside some `W_j`, disjointness leaves exactly that representative germ.
   Outside all the `W_j`, every summand and the original family vanish. This
   proves that restriction of the sum is the given family, and gives clause 3
   on the complement of `U`. Empty supports and empty refinements are included
   in the same finite-sum argument.

5. **Bundle extension by zero as an injective linear map.**
   `compactZeroExtension` chooses the extension from clause 1, and
   `compactZeroExtension_spec` records its defining conditions. Sums and scalar
   multiples satisfy the same restriction and zero-germ conditions. Uniqueness
   therefore proves linearity of `zeroExtensionLinear`. Restriction back to
   `U` proves `zeroExtensionLinear_injective`.

6. **Pass to algebraic duals.** Surjectivity from step 4 gives clause 4 via
   `LinearMap.dualMap_injective_of_surjective`. For clause 5,
   `range_dualMap_eq_dualAnnihilator_ker_of_surjective` reduces factorization
   through the restriction map to vanishing on its kernel. Step 3 supplies
   a compact zero extension for every element of that kernel, so the stated
   vanishing hypothesis applies. Finally,
   `LinearMap.dualMap_surjective_of_injective` applied to the linear map in
   step 5 extends any linear form on compact sections over `U`. Uniqueness
   identifies every section satisfying `IsZeroExtension` with that map's
   value, giving clause 6 in the target's relational formulation.

The theorem concerns the target's actual germ families on `Z` and the actual
open-restriction stalks on `U`. It does not construct the full restriction sheaf
on every open of a locally closed subset; that construction is outside the
statement proved here. All duals are algebraic duals.
