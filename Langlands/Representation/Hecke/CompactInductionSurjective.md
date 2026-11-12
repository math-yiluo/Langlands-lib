# Surjectivity and categorical assembly of the compact comparison

Worker 133 and Worker 142, Task 5403. Derived infrastructure for Renard
III.2.6, printed pp.75–77 / PDF pp.81–83, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

`compactComparisonLift_surjective` proves that the actual balanced tensor
quotient maps onto the original relatively twisted compact induction.
It applies the local-section theorem that an additive map containing every
elementary comparison output in its range is onto. Each such output is the
image of the actual pure tensor, by the defining formula of the quotient
lift. `compactComparisonHom_surjective` is the same result for the exact
categorical component. `compactComparisonHom_dual` records that component's
prescribed scalarized integral through its pure-tensor formula.

`compactComparisonComponentIsoOfInjective` is a conditional constructor: it
requires injectivity of the specific already-constructed component. Its
surjectivity, additivity, Hecke compatibility and elementary formula are
proved intrinsically and are not additional input. The additive equivalence
of a bijective map supplies the inverse. Injectivity transports the existing
Hecke compatibility to this inverse; the additive equivalence identities
prove both categorical inverse laws.

`compactComparisonNatIsoOfInjective` assembles these components with the
already proved naturality of their forward maps. Its last lemma retains the
same scalarized elementary integral. Both the group and representation
carrier universes remain independent. No finiteness of the double-coset
space, countability or topology on the carrier is assumed.

This unit proves surjectivity and provides categorical assembly. It leaves
the supplied component-injectivity argument as a separate obligation and
does not prove `CompactInductionHeckeStatement`.
