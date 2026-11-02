# Renard B.II for the original nonunital action

This file states the original-action Schur theorem and its comparison and
countability auxiliaries as nine proposition targets. It proves none of them.
The complete entry is `Langlands.Renard.NonUnitalSchurStatement.{uA,uM}`.

## Source and conventions

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
is the governing source. The readable original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The relevant passages were read in full in preparing this branch: the initial
conventions (printed pp. 5–6 / PDF pp. 11–12), I.2.1 (printed p. 14 / PDF p. 20),
A.VI.3 (printed p. 263 / PDF p. 269), and B.II (printed p. 272 / PDF p. 278).

The initial convention permits nonunital rings and actions that need not be
unital even if the ring has a unit. A.VI.3 defines simple objects by nonzero
carriers and trivial subobjects. I.2.1 distinguishes additive intertwiners from
complex-linear intertwiners before scalar unitization. We therefore retain all
stable additive subgroups and all additive original-action endomorphisms.

B.II asserts that a simple module which is also a complex vector space has a
division endomorphism algebra; if the module has at most countable complex
dimension, its endomorphisms are the complex scalars. Countable dimension of
the algebra suffices. The proof first adjoins the scalar unit, then uses
kernel/image simplicity, a cyclic original action map, injective evaluation,
and B.I.

The supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp. 18–19, was also read. Its old-edition B.II correction adds the complex
vector-space hypothesis and scalar-unitization reduction. Both already occur
in the governing 2026 edition. No source-specific errata file was present in
the admitted Library when these passages were audited.

## Actual action and simplicity

The algebra `A : Type uA` has `[NonUnitalRing A] [Module ℂ A]`,
`[IsScalarTower ℂ A A]` and `[SMulCommClass ℂ A A]`; these express associative,
complex-bilinear multiplication without a unit. The independently sized carrier
`M : Type uM` has `[AddCommGroup M] [Module ℂ M]`. An actual
`ρ : A →ₙₐ[ℂ] Module.End ℂ M` specifies the compatible original action.

Each component explicitly binds this entire algebra and carrier telescope,
including the multiplication-compatibility instances.

Every premise of simplicity is exactly

```lean
letI := NonUnitalModule.ofLinearEndHom ρ;
Nontrivial M ∧ ∀ S : NonUnitalSubmodule A M,
  S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤
```

Thus every stable additive subgroup is tested. It is not silently restricted to
complex vector subspaces. Each component contains this premise inside its
proposition. No component assumes `ρ ≠ 0`, nondegeneracy, a unit, finite dimension
or a prescribed cyclic vector. The separately published simplicity-reduction
targets explain why complex additive simplicity implies a nonzero original
action and why scalar unitization then preserves the relevant simplicity and
endomorphisms. Their proof remains a separate obligation.

The zero module fails `Nontrivial M`. A zero original action on a nonzero
complex vector space fails additive simplicity: a nonzero vector's cyclic
integer subgroup is stable, nonzero and proper. This is why the cyclic and
algebra-countability conclusions require no extra nonzero-action hypothesis
in the complex setting.

## Statements

All component names below are in `Langlands.Renard`; each takes the same
actual action `ρ`.

1. `NonUnitalSchurEndDivisionStatement` states B.II a) using the actual ring
   `CategoryTheory.End (NonUnitalModuleCat.of A M)`: it is nontrivial and every
   nonzero element is a unit. This category's endomorphisms are exactly
   `NonUnitalModuleHom A M M`, its addition is pointwise, its multiplication is
   composition and its unit is the identity.
2. `NonUnitalSchurEndBijectiveStatement` states that every nonzero additive
   original-action endomorphism is bijective. This is the source's kernel/image
   step.
3. `NonUnitalSchurEndComparisonStatement` states that for each such additive
   endomorphism `f` there is a unique `g : CompatibleUnitization.centralizer ρ`
   with `(g : Module.End ℂ M) m = f m` for every `m`. This is a derived
   actual-map comparison for I.2.1 and B.II; it asserts the automatic complex
   linearity needed to interpret the whole additive endomorphism ring as the
   published complex endomorphism algebra. It assumes no scalar linearity of
   `f`.
4. `NonUnitalSchurCyclicMapSurjectiveStatement` states that for every `m ≠ 0`,
   the actual original map `fun a : A => ρ a m` is surjective. This retains the
   original algebra rather than replacing its orbit by a unitized orbit.
5. `NonUnitalSchurEvaluationInjectiveStatement` states that for each `m ≠ 0`,
   `fun g : centralizer ρ => (g : Module.End ℂ M) m` is injective. This is the
   actual evaluation function on the original-action centralizer.
6. `NonUnitalSchurModuleRankCountableStatement` transfers
   `Module.rank ℂ A ≤ Cardinal.aleph0` to
   `Module.rank ℂ M ≤ Cardinal.aleph0`.
7. `NonUnitalSchurEndRankCountableStatement` transfers
   `Module.rank ℂ M ≤ Cardinal.aleph0` to
   `Module.rank ℂ (centralizer ρ) ≤ Cardinal.aleph0`. The rank is taken on the
   already published complex algebra; no new scalar-module structure on
   `NonUnitalModuleHom A M M` is chosen or assumed.
8. `NonUnitalSchurScalarOfModuleRankCountableStatement` states B.II b). Under
   the module-rank bound it asserts both bijectivity of the actual
   `algebraMap ℂ (centralizer ρ)` and
   `∀ f : NonUnitalModuleHom A M M, ∃! z : ℂ, ∀ m : M, f m = z • m`.
   The latter conclusion includes every additive original endomorphism.
9. `NonUnitalSchurScalarOfAlgebraRankCountableStatement` has the same two
   conclusions under the original algebra-rank bound. This is B.II's final
   sentence.

The entry `NonUnitalSchurStatement` universally quantifies the full algebra,
carrier and actual action telescope, then conjoins all nine components.
Components 1, 8 and 9 are the theorem; components 2, 4–7 expose its proof
steps. Component 3 and the aggregate packaging are derived implementation
content, not separately printed theorems.

`centralizer ρ` is the published actual subalgebra of `Module.End ℂ M`
commuting with every `ρ a`. Its scalar algebra map sends `z` to `m ↦ z • m`.
The published `CompatibleUnitization.endAlgEquiv ρ` compares it with the
actual unitized module's endomorphism algebra and preserves this exact scalar
map. These statements therefore specify canonical scalarity, rather than
existence of an arbitrary equivalence with the complex numbers.

The ranks of `A`, `M` and `centralizer ρ` are bounded in their own universes by
`Cardinal.aleph0`. No cross-universe rank comparison or equality of `uA` and
`uM` is imposed. The countability hypothesis concerns basis cardinality; it
does not assert countability of the underlying complex vector space.

## Proof boundary and route

This is a statement contribution. The existing `SchurStatements` concerns the
unital core and remains unchanged. Its proof task and the independent
nonunital simplicity proof task retain their owners.

A later proof can derive unitized simplicity from original additive
simplicity, use the complex nonzero-action bridge and automatic scalar
linearity for component 3, then apply the unital Schur targets to the actual
`CompatibleUnitization.module ρ`. The published centralizer equivalence
preserves the actual maps. The original orbit comparison supplies component 4;
its orbit is complex-linear by the actual homomorphism `ρ`. Evaluation is
complex-linear on the centralizer by restriction of ordinary linear-map
evaluation. These maps supply the rank bounds without comparing ranks in
different universes. Alternatively the source's kernel/image argument works
directly on additive endomorphisms. No such proof is claimed here.

## Attribution

Worker 709 formulated these targets and their original additive endomorphism
interpretation. Worker 6 supplied the source-convention clarification and
the annihilator/original-orbit, automatic-linearity and cyclic-integer-subgroup
routes used to justify the separate simplicity bridges and the stated
nonunital reduction. Both are actual coauthors of this formulation.
