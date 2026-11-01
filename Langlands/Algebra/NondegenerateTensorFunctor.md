# Actual additive tensor functors and Renard's F and P

This module constructs fixed-first-factor tensor functors on the actual original
module categories, proves the output nondegeneracy needed for their codomains,
and specializes them to the tensor formulas for Renard's F and P. The namespace
is `Langlands.Algebra.NondegenerateTensorFunctor`.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Chapter I, printed pp.5–7 / PDF pp.11–13, supplies the original nonunital
action conventions and fixing-idempotent definition of nondegeneracy.
I.2.2–I.2.3, printed pp.15–18 / PDF pp.21–24, supplies the commuting actions,
tensor formulas, formula (I.2.3.1) for F and the definition of P.

Those latter passages work with complex algebras and their coefficient and
unitized tensor constructions. This module is a derived, internal arbitrary-ring
additive construction using the published integer-tensor balancing quotient.
It records the same handed tensor formulas on original additive actions.
Recovering the complex-linear functors and comparing this model with the
coefficient or unitized tensor models remain separate obligations.

For `S : Type uS`, `R : Type uR`, `X : Type uX`, and a varying original module
carrier in `Type v`, all four universes are independent. The named
`NonUnitalRing` structures, additive group on X, and original left S-action and
right R-action on X are parameters. A right R-action means an original left
action of `Rᵐᵒᵖ`, with `op r • x` interpreted as right multiplication by r.
`hX : ActionsCommute S R X` asserts that these two actions commute. No action of
a second ring on the variable factor is introduced. There is no unit-action law,
coefficient module, commutativity, dimension, or nontriviality hypothesis.

`tensorObj hX M` bundles exactly `NonUnitalModuleTensor.Tensor R X M`.
Its additive group is definitionally
`NonUnitalModuleTensor.addCommGroup R X M`, and its original S-action is
definitionally `NonUnitalBimoduleTensor.leftModule hX M`.
`map hX f` is the entire original S-intertwiner
`NonUnitalBimoduleTensor.leftMap hX hX (NonUnitalBimoduleHom.id S R X) f`.
Its entire underlying additive map is
`NonUnitalModuleTensor.map R (NonUnitalModuleHom.id Rᵐᵒᵖ X) f`.
Consequently its value on `tmul R X M x m` is `tmul R X N x (f m)`.
The carrier, group, action, whole-Hom, and additive-map identities are explicit
declarations, rather than only pointwise descriptions of an unspecified map.

`map_id` and `map_comp` identify the entire original maps. Their proofs use
tensor-generator extensionality through `hom_ext`. `map_zero` and `map_add` use
additivity in the second tensor factor; `mapAddHom` packages this action on
original Hom groups. The original source, intermediate and target carriers in
these unbundled constructions may live in distinct universes `v`, `w`, and `z`.
`functor hX` is the actual additive functor from
`NonUnitalModuleCat.{uR,v} R` to
`NonUnitalModuleCat.{uS,max uX v} S`. Its formulas identify all the same
structures and maps, including its additive map on Hom groups.

The intrinsic construction law `isNondegenerate hS hX hnd M` assumes
`hS : IsIdempotented S` and `hnd : IsNondegenerate S X`. It proves
nondegeneracy for exactly the named residual action on the actual tensor.
It assumes neither idempotentedness of R nor nondegeneracy of M or of the
right R-action on X. The implemented proof first uses surjectivity of the
actual projection from `X ⊗[ℤ] M` onto the balancing quotient. It then applies
integer-tensor induction to show that every projected element belongs to the
published `nondegeneratePart hS (Tensor R X M)`. A pure tensor is fixed by an
idempotent fixing its first factor, using the residual-action formula. The
additive induction step uses the additive subgroup of that part. Its published
closure law uses finite common upper bounds for fixing idempotents in S.
Thus the proof is derived from quotient generation and original actions; its
conclusion is never an input certificate.

`nondegenerateFunctor hS hX hnd` has all original left R-modules as its source
and the actual `NondegenerateModuleCat S` full subcategory as its target.
Every underlying object is `tensorObj hX M`, and every subcategory morphism's
ambient original Hom is the same `leftMap` specified above.
`nondegenerateFunctor_comp_inclusion` proves equality of the entire functor
after composition with `nondegenerateInclusion S` and `functor hX`.
`restrictedFunctor hS hX hnd` is the composite with
`nondegenerateInclusion R` on the source. It too is additive and has explicit
carrier, group, action, ambient-Hom, additive-map, and pure-tensor formulas.
Both codomain carrier universes are exactly `max uX v`.

For the source formulas, A and B have independent ring universes `uA` and `uB`,
and the variable carrier universe v remains independent. `F hA hAB hnd` accepts
the specified commuting A–B actions on the actual ring carrier B and the
source's `IsNondegenerateBimodule A B B` hypothesis. It maps an actual
nondegenerate B-module N to `Tensor B B N.obj`, with left A-action on the first
factor. `P hB hBA hnd` accepts specified commuting B–A actions on B and
`IsNondegenerateBimodule B A B`. It maps a nondegenerate A-module M to
`Tensor A B M.obj`, with left B-action on the first factor. Each morphism is
exactly `id_B ⊗ f`, expressed as both the entire original `leftMap` and its
entire underlying additive map. The target carrier universe for both is
`max uB v`, independent of the other ring universe.

`leftNondegenerate_of_bimodule` extracts the precise one-sided input.
`F_eq_restrictedFunctor`, `P_eq_restrictedFunctor`, and the
`_eq_inclusion_comp` formulas identify the entire source functors with the
appropriate restrictions of `nondegenerateFunctor`. The general constructions
above also permit arbitrary first-factor carriers and the weaker one-sided
nondegeneracy assumption. F needs only the idempotentedness of its target A
in this general construction; P needs only that of its target B.

`regularF` selects exactly `NonUnitalModule.rightRegular B` as the right
B-action, while retaining the specified left A-action, commutation, and left
nondegeneracy hypothesis. `regularP` selects exactly
`NonUnitalModule.regular B` as the left B-action, while retaining the specified
commuting right A-action and its right nondegeneracy hypothesis.
`regular_isNondegenerate` and `rightRegular_isNondegenerate` prove the respective
regular-action laws from `IsIdempotented B`: choose an idempotent whose corner
contains b and use the left or right absorption equality. The right proof
transports that idempotent to the opposite ring. These lemmas provide the other
half of each two-sided input to F or P. The regular specializations have their
own full object and map formulas and whole-functor equalities with the
appropriately structured `restrictedFunctor`. No scalar homomorphism is
assumed to supply a nondegenerate bimodule.

The supplementary registered source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp.1–2 and 18–19, was read with the governing edition. Its first page
corrects induction-adjunction directions and warns that a later right corner
action can be degenerate. Neither observation provides an adjunction or tensor
comparison here. Its later complex-vector-space and unitization correction
concerns a different theorem. The author's live book section checked on
1 November 2026 agrees byte-for-byte with registered snapshot
`renard-author-book-links-2026-10-31`, SHA256
`143092e92be11be1b9c5a03bfc1e9e4538edb45f9a67d5fc8cc474b7b6dcd580`:
it separately labels the 2010 errata and links the corrected 2026 French edition,
with no separate 2026 errata link in that section. This is a bounded navigation
check.

The companion `NondegenerateTensorFunctorChecks` pair checks complete unapplied
interfaces, independent and unequal universes, selected competing structures,
and permitted boundary cases. This contribution proves no regular-tensor
contraction (I.2.3.3), scalar-restriction comparison, Hom-based pseudo-forgetful
or I functor, equality of nondegenerate Hom parts, adjunction, or exactness.
Those results and the complex coefficient bridges remain separate successors.
