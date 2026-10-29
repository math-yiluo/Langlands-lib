# The canonical compatible stable image of actual localization

Authors: Worker 709 and Worker 977. This is a statement-only internal
refinement of the stable-image conclusion of Renard's final C.II
proposition. It contains no proof. The two proposition definitions are
in namespace `Langlands.Renard.AlgebraActionLocalization`.

## Original source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, Appendix C.II, final proposition and proof,
printed p. 279 / PDF p. 285, concludes that the localization of an
endomorphism is isomorphic to its image at every positive stable power.
The proposition assumes a commutative Noetherian complex algebra, a
finitely generated source module and a finitely generated localization,
and first deduces eventual stability. The definition of stability and its
extension to complex-algebra modules are on printed p. 276 / PDF p. 282.
Appendix A.III.1, example 5, printed p. 252 / PDF p. 258, constructs the
endomorphism localization and extends it to algebra modules.

The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Worker 709 read these original passages and visually inspected PDF p. 285.
Worker 977 independently verified the source hash and reread PDF pp. 285,
282, 258–259 and 12.
The global conventions on printed p. 6 / PDF p. 12 allow nonunital rings
and actions, including actions of unital rings without a unit law. The
current project and Library have no separate errata note for this source.
PDF pp. 18–19 of the registered older supplementary source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were also read by both authors; Worker 977 verified that hash. They
contain no correction to the final C.II proposition or change to those
nonunital conventions. The 2026 text governs.

This unit isolates the identification once a positive stable power is
given. Its removal of finiteness and commutativity hypotheses, the
canonical normalization of the equivalence and its uniqueness are
**internal derived refinements**, not assertions quoted verbatim from
Renard. The ordinary unital-module statement
`Langlands.Renard.EndomorphismLocalization.StablePowerImageStatement`
already isolates this finiteness-free conclusion over arbitrary
commutative coefficient rings. The present target refines its complex
specialization to the actual compatible B-actions and actual compatible
kernel and range. It does not claim the source's eventual-stability
conclusion under its finiteness hypotheses.

## Data and actual constructions

The independent universes are `uB uV`. The parameterized definition
`CompatibleStablePowerImageAt` takes

```text
B : Type uB
[NonUnitalRing B] [Module ℂ B]
[IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
V : Type uV
[AddCommGroup V] [Module ℂ V]
ρ : B →ₙₐ[ℂ] Module.End ℂ V
f : LinearIntertwiner ρ ρ
n : ℕ.
```

The two compatibility classes on B express complex bilinearity of its
multiplication. B may be noncommutative and may have no unit. The action
ρ may be zero, may be degenerate and need not satisfy a unit law. V may
be zero or infinite dimensional. There is no finite-generation,
Noetherianity, finite-dimensionality or nontriviality premise.

Put `a = f.toLinearMap`. Its commutation proof is the actual equation
`ha b z = f.map_action' b z`. The action on the actual localization is
`σ = localizedAction a ρ ha`, from the published
`Langlands.Algebra.RenardAlgebraActionLocalization`. The carrier,
canonical map and localized operator are the published `Localized a`,
`iota a` and `localizedEnd a`, unchanged. No alternative localization
carrier, action or universal-property certificate is supplied.

Use only the following local powers:

```lean
letI := CompatibleUnitization.module ρ
let powers : ℕ → LinearIntertwiner ρ ρ := fun m =>
  CompatibleUnitization.toLinearIntertwiner
    ((CompatibleUnitization.ofLinearIntertwiner f) ^ m)
```

The published unitization supplies a unital module for this local
construction even when B or its action is nonunital. Its identity and
composition are those of the actual unitized module endomorphisms;
the power at zero is the identity. This introduces no global instance
or new power constructor. The expected underlying map is `a ^ m`;
this coherence is an intrinsic consequence of the public conversion
identities and composition laws, not an additional premise or an import
of any unreviewed power-chain statement.

Set `K = (powers n).ker` and `I = (powers n).range`, using the actual
`CompatibleSubmodule ρ` kernel and range. `I.toSubmodule` is its
underlying complex subspace, and `I.restrictAction` is the actual
restriction of ρ to it. These are the public constructions of
`Langlands.Algebra.CompatibleSubmodule`. The equivalence target is this
subspace with its inherited complex vector-space structure; no
identification of arbitrary additive invariant subgroups with complex
subspaces is made.

## Exact propositions

`CompatibleStablePowerImageAt ρ f n` asserts `IsCompl K I` in the actual
complete lattice of compatible submodules and unique existence of

```text
e : Localized a ≃ₗ[ℂ] I.toSubmodule
```

satisfying all three conditions:

1. For every `b : B` and `z : Localized a`,
   `e (σ b z) = I.restrictAction b (e z)`.
2. Writing `s = I.toSubmodule.subtype`, the actual complex-linear maps
   satisfy `s ∘ e ∘ localizedEnd a = a ∘ s ∘ e`.
3. `e.symm.toLinearMap = (iota a).comp I.toSubmodule.subtype`.

All three conditions are inside the `∃! e` predicate. The first makes
the complex-linear equivalence compatible with the B-actions; its inverse
then also respects them. The second records the restricted operator
without introducing a separate restricted-endomorphism constructor. The
third identifies the inverse with the restriction of the actual canonical
map to I and fixes the equivalence canonically. Uniqueness concerns
equivalences satisfying the conjunction of all three conditions.
`IsCompl K I` says that K and I have zero intersection and their sum is V
in the compatible lattice, so it records the B-stable direct
decomposition.

The parameterized definition is meaningful for every `n : ℕ` and assumes
no positivity or stability. It can fail at zero, for example for the zero
endomorphism on a nonzero space. Its existence is a proposition target,
not a constructed equivalence.

The closed proposition `CompatibleStablePowerImageStatement.{uB, uV}`
quantifies internally over all the displayed data and every `n : ℕ`. Its
only further premises are

```text
0 < n
Stable (f.toLinearMap ^ n).
```

It concludes `CompatibleStablePowerImageAt ρ f n` for every such n.
`Stable` is exactly the existing
`Langlands.LinearAlgebra.StableEndomorphism.Stable`: equality of the
kernel with the square's kernel and equality of the range with the
square's range. No desired complementarity, action equation, canonical
map surjectivity, equivalence or uniqueness is assumed.

## Reuse and remaining scope

The only project imports are the four public construction and stability
modules listed in the Lean file. No unreviewed criterion or power-chain
draft is imported. A later proof may transport the published ordinary
stable-image identification through the underlying power coherence,
reflect complementarity through the compatible-submodule lattice
embedding, and prove the action equation using the inverse normalization
and `localizedAction_iota`. This is a potential proof route, not a proof
provided by this unit.

The source's nonunital finite-generation and Noetherian conventions,
eventual stability from those hypotheses, and the full general
source-facing C.II proposition remain separate parent obligations. The
B-linear universal property with arbitrary targets, power-chain criteria
and quotient exact sequences are separate units. Neither this
statement-only refinement nor its compilation completes any of them or
the whole book.

## Development checks

Worker 709 compiled the canonical module in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with zero errors or warnings.
The closed target returns `Prop`, has independent level parameters
`uB uV`, and uses only `propext`, `Classical.choice` and `Quot.sound`.
A separate private diagnostic overlay printed both complete declaration
bodies and unapplied types, including the commutation proof and local
variable types, and checked both orders of distinct universe
instantiations. It confirmed that all three equations are inside unique
existence and that the closed statement has exactly the two premises
displayed above. The diagnostics are excluded from this unit.

Worker 977 independently rechecked the unchanged Lean file in the same
environment, with zero errors and zero warnings. The closed target
returns `Prop`, has level parameters `uB uV`, and uses only the three
axioms above. A second private diagnostic overlay printed both complete
bodies with proof terms and local variable types. It shows
`ha = fun b z => f.map_action' b z`, `σ = localizedAction a ρ ha`, the
powers formed by `toLinearIntertwiner` of monoid powers of
`ofLinearIntertwiner f` under the local unitized module, the actual
`LinearIntertwiner.ker` and `LinearIntertwiner.range`, and the actual
`CompatibleSubmodule.restrictAction`. All three equations appear inside a
single `ExistsUnique`. It also printed the unapplied types and
instantiated the closed target at the level pairs (0, 1), (1, 0), (2, 3)
and (3, 2). It checked by `Iff.rfl` that the closed target unfolds to the
displayed binder telescope with exactly the two premises. It also proved
that for every m the underlying map of `powers m` is `a ^ m`, which
confirms the intended power coherence. These overlays are excluded from
this unit.

These are author development checks, not independent semantic acceptance
or proof evidence.
