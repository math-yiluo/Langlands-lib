# The exact compact Hecke tensor comparison

Worker 133 and Worker 142, Task 5403. The theorem
`compactInductionHeckeStatement_proof` proves the exact published proposition
`Langlands.Hecke.Homomorphism.CompactInductionHeckeStatement`, including all
its universe parameters. The source is Renard, French version dated 9 July
2026, III.2.6, equations (III.2.6.1)–(III.2.6.2) and Theorem, printed
pp.75–76 / PDF pp.81–82, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The forward comparison is the already constructed natural Hecke-module map
between the actual nonunital tensor-induction functor and compact induction
with relative character ΔH/ΔG. Its elementary output uses the algebraic
integrated action of the subgroup test h ↦ (ΔH/ΔG)(h) T(g⁻¹h). The supporting
construction proves covariance, one uniform open right stabilizer, and
compact support modulo H. Its balancing law descends it through the original
integer-tensor quotient, with the original subgroup Hecke actions. The
ambient group intertwiner and its integrated action prove Hecke linearity;
subgroup intertwiners commuting with the same algebraic integral prove
naturality.

`compactComparisonHom_injective` applies the finite-coset reconstruction
theorem to this precise additive component. Its hypothesis on all pure values
is the component's defining formula, by reflexivity. Reconstruction expands
an arbitrary tensor over finitely many cosets for one common compact open
subgroup. Compact coefficient averaging and original scalar and group
balancing recover each coset tensor from its comparison value at a chosen
double-coset representative. Taking the finite set of representatives
occurring in the expansion makes the reconstruction a left inverse at the
chosen tensor, so a zero image forces the tensor to be zero.

Surjectivity is the supporting local-section result: normalized compact-open
indicators realize the identity-centered double-coset sections, translation
realizes their translates, and the compact-local-section spanning theorem
covers all compact-induced functions. The actual quotient lift has every
elementary value in its image. The compiled categorical constructor then
inverts each bijective additive component. The forward component's Hecke
linearity implies the inverse's Hecke linearity, and the existing naturality
assembles `compactComparisonNatIso`.

The final proof introduces the group, its arbitrary supplied Haar measure,
the closed subgroup and its inherited local compactness, and its arbitrary
Haar measure, exactly as quantified by the published statement. It chooses
this natural isomorphism. The proved right-convolution formula gives the
original right-action clause. On pure tensors its forward map is the
original elementary comparison, whose scalarization followed by weighted
Haar inversion gives the exact displayed integral with ambient modular
factor ΔG(h) and coefficient action ρ(h⁻¹).

The proof retains independent group and representation-carrier universes.
It assumes neither a finite double-coset space, second countability,
unimodularity nor a topology on the representation carrier. No extra
injectivity or comparison hypothesis remains in the final theorem.
