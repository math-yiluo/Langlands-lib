# Stability criteria for compatible nonunital algebra actions

This statement family connects the existing complex-linear stability predicate
to actual compatible algebra actions, their intertwiners, and their submodule
lattices. It concerns David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix C.II, Definition and
Lemma (i)–(iii), printed pages 276–278 / PDF pages 282–284.
It states propositions and supplies no proofs.

The governing registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Worker 709 prepared the original pair. Worker 345 independently read all three
cited PDF pages and visually checked both exact-row diagrams on PDF282–283
on 29 October 2026, then audited the complete component bodies against the
current imported Lean/Markdown pairs. Both are authors of this unit.

## Actual objects and source conventions

The algebra is `B : Type uB` with `[NonUnitalRing B] [Module ℂ B]`,
`[IsScalarTower ℂ B B]`, and `[SMulCommClass ℂ B B]`. These laws give an
associative complex algebra with bilinear multiplication. Multiplication need
not be commutative, and a multiplicative unit is not required. An action on a
complex vector space `V` is the actual nonunital algebra homomorphism
`ρ : B →ₙₐ[ℂ] Module.End ℂ V`. This is the published scalar-compatible
action interface of `Langlands.Algebra.CompatibleNonUnitalAction`, imported
through `Langlands.Algebra.CompatibleSubmodule`. Neither a unit action law
nor nondegeneracy of the action is assumed. Zero actions, zero algebras,
and zero vector spaces are included.

The source's opening C.II definition expressly extends stable and eventually
stable terminology to endomorphisms of complex-algebra modules. Its
Lemma (i)–(iii) is written for vector spaces. The present exact-row assertions
are internal specializations to maps intertwining actual compatible actions.
They use the same underlying complex-linear maps and the same source
hypotheses. This source correspondence does not identify additive invariant
subgroups with complex subspaces.

`LinearIntertwiner ρ σ` is the published type of complex-linear maps
intertwining the two actions. Its `toLinearMap`, `comp`, `ker`, and `range`
are reused without replacement. For a self-intertwiner `f`, `f.comp f`
is its actual square. The existing `ker_toSubmodule` and
`range_toSubmodule` identify the compatible kernel and range with the
ordinary kernel and range of the underlying complex-linear map.

`CompatibleSubmodule ρ` is the complete lattice of actual complex
subspaces stable under `ρ`. Its infimum and supremum are intersection and
sum of the underlying subspaces; its bottom and top are zero and the whole
space. Thus `IsCompl f.ker f.range` says that these compatible submodules
give the internal decomposition of `V` as kernel plus image, with zero
intersection. It introduces no chosen splitting, replacement carrier,
abstract exactness certificate, or categorical hypothesis.

`Stable` is exactly
`Langlands.LinearAlgebra.StableEndomorphism.Stable`, imported from the
published vector-space statement module. The adapter uses
`Stable f.toLinearMap`; it does not define a second stability predicate.
The existing `EventuallyStable` can likewise be applied to that underlying
endomorphism, but the present family makes no power-chain assertion.

There is no finite dimension, finite generation, Noetherianity, chain
condition, countability, topology, or nontriviality premise. Scalars are
exactly `ℂ`. The algebra universe `uB`, single-space universe `uV`, and
three exact-row carrier universes `uA`, `uM`, `uC` are independent.

## Declarations

All five definitions are closed propositions in the namespace
`Langlands.Algebra.CompatibleStability`. Each component binds all its
algebras, vector spaces, structures, actions, and maps internally.

| Declaration | Content and provenance |
| --- | --- |
| `StableKernelRangeStatement` | For every actual self-intertwiner `f`, `Stable f.toLinearMap` is equivalent to the conjunction `f.ker = (f.comp f).ker` and `f.range = (f.comp f).range`. This is an internal compatibility assertion for the source definition on printed276/PDF282. Both equalities are necessary. |
| `StableIffIsComplStatement` | For every such `f`, `Stable f.toLinearMap ↔ IsCompl f.ker f.range`. This is the compatible-submodule form of Lemma (i), printed276/PDF282, with proof on printed277/PDF283. |
| `StableOfRightExactStatement` | Given `phi : A → M` and `psi : M → C` as actual intertwiners, equality `phi.range = psi.ker`, surjectivity of `psi`, the two commuting-square equalities below, and stability of `fA` and `fM`, conclude stability of `fC`. This specializes Lemma (ii), printed276/PDF282, proved on printed277/PDF283. |
| `StableOfLeftExactStatement` | Given the same data, injectivity of `phi`, equality `phi.range = psi.ker`, the same square equalities, and stability of `fM` and `fC`, conclude stability of `fA`. This specializes Lemma (iii), printed277/PDF283, whose proof continues on printed278/PDF284. |
| `CompatibleStabilityStatements` | Internal conjunction of the preceding four closed propositions, in that order. Its universe order is `uB uV uA uM uC`. |

The exact rows are `A → M → C → 0` and `0 → A → M → C`,
respectively. Their middle exactness equality is in the actual lattice
`CompatibleSubmodule ρM`. Only the displayed endpoint surjectivity or
injectivity is required. The commuting-square equalities are equalities
of bundled intertwiners:

```text
fM.comp phi = phi.comp fA
fC.comp psi = psi.comp fM
```

They give precisely the source diagrams after passing to `toLinearMap`.
The letter `M` denotes the middle vector space so that `B` can continue
to denote the algebra. This change of letter changes no hypothesis.

## Errata, evidence and remaining obligations

Workers 709 and 345 independently read PDF18–19 of the registered supplementary source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`.
Its correction to the old proof of Lemma (iii) uses
`ker fC ∩ Im fC`; that correction is already present on 2026 PDF284.
The older list is supplementary evidence and does not replace the
governing 2026 edition. No project Renard errata note was found during
this preparation.

The family reuses published constructions and proposition definitions.
Compilation and proposition inspection establish elaboration only;
independent statement review and publication remain necessary. A later
proof may specialize the existing vector-space criteria and transport
submodule equalities and complementarity through the published
`CompatibleSubmodule.toSubmoduleHom` and its injectivity. That is a
proposed route, not a proof supplied here.

Power-chain stabilization, the source's auxiliary `E_k` and `F_k`
quotients and exact sequence, and the final C.II finite-localization
proposition remain separate obligations. In particular this unit
does not resolve the source's finite-generation or Noetherian conventions
for possibly nonunital algebra actions. It neither changes the existing
ordinary unital-module localization statement nor constructs new
unitizations, actions, kernels, ranges, or exact-sequence objects.
