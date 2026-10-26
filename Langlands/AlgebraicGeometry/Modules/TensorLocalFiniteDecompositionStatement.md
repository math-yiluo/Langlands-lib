# Local finite pure-tensor decompositions of sections

`Langlands.Scheme.Modules.TensorLocalFiniteDecompositionStatement` is a
Prop-valued definition, parameterized by an arbitrary
`X : AlgebraicGeometry.Scheme.{u}`. The universe `u` is unrestricted; the
module sheaves belong to Mathlib's actual category `X.Modules`.

For every pair `M N : X.Modules`, every open `U : X.Opens`, every section
`z` of `tensorObj M N` over `U`, and every point `x ∈ U`, the proposition
asserts the existence of an open neighborhood `V` of `x` contained in `U`,
a natural number `n`, and sections `s i ∈ M(V)` and `t i ∈ N(V)` indexed
by `Fin n`, such that

```text
η_V (∑ i : Fin n, s i ⊗ t i) = z|_V.
```

Here the algebraic tensors are over the section ring
`X.presheaf.obj (Opposite.op V)`. The map `η_V` is exactly
`((tensorSheafifyUnit M N).app (Opposite.op V)).hom`, the component of the
published module-sheafification unit from
`Langlands.AlgebraicGeometry.Modules.PullbackTensor`. Its source is the
sectionwise tensor product of `M.val` and `N.val`. Its target is the
underlying presheaf of the published actual sheaf tensor `tensorObj M N`
from `Langlands.AlgebraicGeometry.Modules.Tensor`.
The restriction on the right is precisely
`(tensorObj M N).val.map (CategoryTheory.homOfLE hVU).op z`, where
`hVU : V ≤ U`.

All tensor summands live over the same neighborhood `V`. The number `n`
may be zero, so the empty sum is permitted. The proposition assumes no
finite presentation, quasi-coherence, affineness, local freeness, tensor
inverse, or auxiliary pairing. It makes no claim that an arbitrary section
over the original open `U` has a global sectionwise tensor presentation.

## Source and derived scope

The source is the Stacks Project, Section 17.25, retained as the registered
source `stacks-local-freeness-invertibility-sections-2026-10-21`,
*Stacks Project - Locally free sheaves and invertible modules, Sections
17.14 and 17.25 (HTML snapshot 2026-10-21)*. The registered publication
folder has content SHA256
`6d1641a9deb284be889ee6e2630a2be6e57cc5985c80af2c9da7d17543ed0785`.
The exact file is `01CR.html`, SHA256
`406066717992b9748b50331e56fdf0573122a5cd23ffbd6f88608ce06c1f3e4e`.
The relevant locator is Lemma 17.25.2, second proof paragraph, following
Definition 17.25.1. These passages and Lemma 17.25.4 with its proof were
read in the retained original. No source-specific erratum was found in
the current published notes on 2026-10-26.

Definition 17.25.1 defines an invertible module by equivalence of the
tensor functor. Lemma 17.25.2 equates invertibility with existence of a
tensor inverse and deduces local finite projectivity and the dual
description of that inverse. In its second proof paragraph, given an
isomorphism `ψ : L ⊗ N ≅ 𝒪_X` and a point, it chooses finitely many
local pure tensors whose sum maps to the unit section. The source uses
a positive number of terms for that application.

The statement here is a **derived generalization of that local
finite-sum step**: it concerns any section of the tensor of any two module
sheaves, uses the actual sheafification unit, allows the empty sum, and
specializes the ambient ringed space to a scheme. The rationale is the
local representability of sections under sheafification, together with
finite pure-tensor presentations of algebraic tensors. This rationale is
not supplied as a Lean proof by this statement contribution.

Lemma 17.25.4 identifies locally free rank-one modules with invertible
modules when the stalk rings are local, and proves the forward implication
for arbitrary ringed spaces. That result supplies the broader application
context; this proposition asserts only the local finite decomposition.

## Formal status and attribution

This module supplies a statement, not a proof of it. A separate proof
successor must prove exactly
`Langlands.Scheme.Modules.TensorLocalFiniteDecompositionStatement`.
Statement publication alone establishes neither this decomposition theorem
nor the invertibility/local-rank-one implication in the host task.

Worker 124 supplied the intended interface and its role in the reverse
implication. Worker 339 implemented the Lean statement and this provenance
description. The pinned environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
