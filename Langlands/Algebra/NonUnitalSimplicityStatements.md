# Simplicity under the actual scalar unitization

`NonUnitalSimplicityStatements.lean` gives seven derived proposition targets for
Renard's nonunital reductions in I.2.1 and Appendix B.II–III. It keeps both the
original additive action and the separately specified vector-space structure.
The declarations are statements only: none of their conclusions is proved or
assumed in this module.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The relevant passages are:

- Initial ring/module conventions, printed pp. 5–6 / PDF pp. 11–12:
  rings and actions need not have a unit law, even when the ring has a unit.
- I.2.1, printed p. 14 / PDF p. 20: adjoining the scalar unit and the
  identification of unitized intertwiners with original intertwiners that are
  also complex-linear.
- A.VI.3, printed p. 263 / PDF p. 269: simplicity excludes the zero object and
  means that every subobject is zero or the whole object.
- B.II, printed p. 272 / PDF p. 278: the possibly nonunital Schur theorem and
  its opening reduction to a unital algebra acting unitally on the same
  complex vector space.
- B.III, printed p. 273 / PDF p. 279: the separating simple module, obtained
  after unitization, on which the specified original element acts nontrivially.

These passages were read in the source audit supporting this unit. The
registered 2010-edition *corrections et compléments*, PDF pp. 18–19, adds the
complex-vector-space hypothesis and the unitization reduction to B.II; both
already occur in the governing 2026 edition. At the source audit, no source-specific errata note
was present in the admitted Library. The older errata do not replace the
2026 text.

The seven targets are internal comparison statements. Renard does not print
this list of equivalences and implications. Their purpose is to make the
simplicity and Hom comparisons needed by those reductions explicit. The
field-general versions are derived extensions, not assertions attributed
verbatim to the complex source. In particular, I.2.1's intersection of Hom
sets alone does not identify all stable additive subgroups with stable vector
subspaces.

## Data, actions and universes

All names below belong to `Langlands.Algebra.CompatibleUnitization`. In the
first six targets, `k : Type uK` is a field, `A : Type uA` is an associative
possibly noncommutative nonunital ring with a `k`-module structure, and
`IsScalarTower k A A` and `SMulCommClass k A A` express bilinearity of its
multiplication. The additive group `M : Type uM` has its specified `Module k M`.
The action is the actual nonunital algebra homomorphism

```lean
ρ : A →ₙₐ[k] Module.End k M
```

The original action on the same additive group is the published local instance
`NonUnitalModule.ofLinearEndHom ρ`. Its stable additive subgroups are
`NonUnitalSubmodule A M`. The actual unital action on that same vector space
is the local instance `CompatibleUnitization.module ρ`, with

```text
(c, a) • m = c • m + ρ a m.
```

It restricts along `Unitization.inr` to precisely `ρ`. Neither instance is
installed globally. `CompatibleSubmodule ρ` means the original stable
`k`-vector subspaces, with the originally specified scalar structure.

The categorical comparison does not use the two multiplication-bilinearity
instances: its full declaration requires only the field, the nonunital ring,
the two module structures and the additive group, besides `ρ`. The other five
field-general declarations retain those bilinearity instances because they
use the actual scalar unitization.

The universes `uK`, `uA`, `uM` and the target-carrier universe `uN` are
independent. The last target fixes `k = ℂ` and retains independent `uA` and
`uM`. There are no countability, dimension, topology, group-origin or
nontrivial-algebra premises.

For clarity, write **additive simplicity** for the exact proposition

```lean
letI := NonUnitalModule.ofLinearEndHom ρ
Nontrivial M ∧ ∀ S : NonUnitalSubmodule A M,
  S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤
```

This abbreviation in the prose introduces no new Lean predicate. It quantifies
over every stable additive subgroup, without assuming scalar closure.
`Nontrivial M` is part of the proposition, not a silently omitted section
instance. In contrast, `IsSimpleOrder (CompatibleSubmodule ρ)` concerns stable
vector subspaces and includes distinct bottom and top. Likewise,
`IsSimpleModule (Unitization k A) M` excludes the zero module.

## The seven targets

| Declaration | Proposition and role |
| --- | --- |
| `CompatibleSimpleUnitizationStatement ρ` | Stable-vector-subspace simplicity is equivalent to `IsSimpleModule (Unitization k A) M` for `module ρ`. It uses the published carrier-preserving `submoduleOrderIso ρ`. |
| `AdditiveSimpleCategoricalStatement ρ` | Additive simplicity is equivalent to `CategoryTheory.Simple (NonUnitalModuleCat.of A M)` for the exact original action. The category has additive original-action intertwiners; it is not a category restricted to scalar-linear maps. |
| `AdditiveSimpleUnitizationStatement ρ` | Additive simplicity implies simplicity for `module ρ`. Every unitized submodule is an original stable additive subgroup. |
| `SimpleUnitizationRestrictionStatement ρ` | If `ρ ≠ 0`, simplicity for `module ρ` implies additive simplicity for the original action. |
| `SimpleUnitizationOrbitStatement ρ` | Under those same two premises, every `m ≠ 0` has a surjective actual orbit map `fun a : A => ρ a m`, with domain the original algebra `A`. |
| `SimpleUnitizationIntertwinerStatement ρ` | Under those same source premises, every additive original-action intertwiner to any compatible action `σ` on any `N : Type uN` satisfies `f (c • m) = c • f m` for all `c : k` and `m : M`. The target needs neither simplicity nor nonzero action. |
| `ComplexAdditiveSimpleActionNonzeroStatement` | For an original compatible action on a complex vector space, additive simplicity implies `ρ ≠ 0`. This is a conclusion to be proved, not an extra assumption added to B.II. |

`NonUnitalSimplicityReductionStatement.{uK,uA,uM,uN}` universally quantifies the
first six statements over their data and conjoins the seventh. All eight
names are `def`s returning `Prop`. A statement definition supplies no evidence
of the proposition it names.

## Mathematical rationale and zero cases

The following explains the proposed statements; it is not a formal proof.
The first comparison transports a simple order through the published
`submoduleOrderIso`. The second uses the published original-action subobject
correspondence `NonUnitalModuleCat.subobjectOrderIso`, together with the
nonzero-object condition. The third forgets scalar closure of a unitized
submodule and retains the explicit nontriviality of `M`.

For the restriction and orbit statements, the common annihilator
`{m | ∀ a, ρ a m = 0}` is a stable vector subspace. If the unitized module is
simple and `ρ ≠ 0`, that annihilator must be zero. For each nonzero `m`, the
image `A m = {ρ a m | a ∈ A}` is a nonzero stable vector subspace: addition,
scalar closure and stability follow from the algebra-homomorphism laws. Thus
`A m = M`. Any nonzero stable additive subgroup contains such an `m` and
therefore contains all of `M`, proving the intended additive restriction.

For automatic scalar linearity, fix a nonzero source vector `m₀`. The orbit
statement writes any `m` as `ρ a m₀`; then `c • m = ρ (c • a) m₀`.
Additivity and the original intertwining equation give
`f (c • m) = σ (c • a) (f m₀) = c • f m`. No property of the target beyond its
compatible action is used.

The nonzero-action premise cannot be omitted from the reverse comparison.
For example, let `A = ℂ`, let `M = ℂ` with its usual scalar structure, and let
`ρ = 0`. The unitized action factors through its scalar coordinate and is
simple, since `M` is one-dimensional over `ℂ`. The nonzero proper additive
subgroup generated by `1` is original-action stable. Thus additive simplicity
fails. The forward comparison and the stable-vector-subspace comparison still
apply correctly to zero actions.

For the last target, if the action on a nonzero complex vector space were
zero, the additive subgroup `ℤ m` generated by any nonzero `m` would be stable,
nonzero and proper: `(1/2) • m` cannot be an integer multiple of `m`.
This excludes zero action in the complex additively simple case without
adding a hypothesis to the source theorem. If `M` is zero, both simplicity
notions are false. If `A` is zero, every action is zero, so the three reverse
statements with premise `ρ ≠ 0` are vacuous, as intended.

## Scope, checking and attribution

The published `CompatibleUnitization` and `CompatibleUnitizationSubmodule`
constructions compare the actual unitized action, scalar-linear intertwiners,
stable vector subspaces, and restrictions and quotients. They do not already
supply these additive-simplicity and automatic-linearity conclusions.
`NonUnitalModuleSubobject` supplies the separate categorical subobject
correspondence for all original stable additive subgroups. These constructions
are imported unchanged.

The private declaration checks compare the full unapplied signatures of all
eight statement definitions and their complete bodies, including both chosen
local actions and independent universe parameters. The submitted entry is
checked as Prop-valued in the pinned Lean environment. These checks establish
typing; independent semantic review and later proofs remain required.

This unit does not prove the comparisons, Schur's lemma, countable-dimensional
scalarity, or the separating simple-module theorem. The separate unital
`SchurStatements` and `SeparationStatements` remain unchanged. Applying their
proofs to the source nonunital actions and identifying the actual original
endomorphism ring are further obligations.

Worker 709 formulated these statements, audited the distinctions between
additive and vector-subspace simplicity, and wrote the declaration checks and
documentation. Worker 6 supplied source-convention clarification and the
nonzero-action annihilator/orbit route, including the complex cyclic-subgroup
obstruction. Both are actual coauthors of this derived statement unit.
