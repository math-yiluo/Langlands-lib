# Smooth representations and nondegenerate Hecke modules: proof of Renard III.1.4

Author: Worker 155. Module
`Langlands.Representation.Hecke.NondegenerateModuleEquivalenceProof`, namespace
`Langlands.Hecke`.

The theorem `heckeNondegenerateModuleEquivalence.{u, v}` has exactly the type
`HeckeNondegenerateModuleEquivalenceStatement.{u, v}`. It proves that the published
functor `heckeNondegenerateModuleFunctor μ` is an equivalence, for every group and
Haar measure in that statement and every independent carrier universe `v`.
All supporting constructions and lemmas are in the namespace
`Langlands.Hecke.NondegenerateEquivalence`.

## Source and correspondence

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, III.1.3–III.1.4, printed pp.59–60 / PDF pp.65–66. Registered
source: `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The retained
original is `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
These two source pages were read for this proof.

The Theorem in III.1.4 identifies smooth representations with nondegenerate
modules over the Hecke algebra. Its proof extends the Hecke action to Dirac
distributions by applying left convolution to a fixing idempotent. The Lean proof
implements the Dirac part directly as translation of actual test functions. It
uses the published right-limit action for independence of the fixing idempotent,
and the published canonical scalars for the complex vector-space structure.
It does not require constructing an action of every compactly supported
distribution.

The formal hypotheses are exactly those of the
[published statement](NondegenerateModuleEquivalenceStatement.md): `G : Type u`
is a Hausdorff locally compact nonarchimedean group, with its Borel measurable
structure and a left Haar measure `μ`. Mathlib's nonarchimedean Hausdorff
instance supplies total disconnectedness when applying the published
compact-open invariance and local-unit theorems. The carrier of an arbitrary
module remains its original type in `Type v`.

## Recovering the smooth representation

Write `H = HeckeAlgebra μ`. The construction `translate μ g` is the existing
complex-linear translation

\[
(L_g a)(x)=a(g^{-1}x).
\]

The lemma `translate_convolution` proves
`L_g(a * b) = (L_g a) * b` by the left-Haar substitution `y = g z`.
No right invariance of the Haar measure is used. The theorem `idempotented`
packages the published compact-open two-sided local units as
`Algebra.IsIdempotented H`.

The representation `regular μ` is left translation on `H`. Its smoothness
`regular_smooth` follows by applying the published common compact-open
bi-invariance theorem to a singleton test function. Only its left-invariance
part is used.

For every `g`, `translationFamily μ g` is the compatible family
`e ↦ L_g e`, indexed by the actual idempotents of `H`. Compatibility follows
from `translate_convolution` and the idempotent absorption equations. For an
original additive nondegenerate `H`-module `M`, `act μ hM g m` applies the
published `IdempotentedRingRightLimitAction.act` to this family. Consequently
`act_eq` gives, for every idempotent `e` satisfying `e • m = m`,

\[
\rho(g)m=(L_g e)\mathbin{\bullet}m.
\]

This value is independent of the fixer by the published right-limit action
lemma. `act_smul` proves the useful identity

\[
\rho(g)(a\mathbin{\bullet}m)=(L_g a)\mathbin{\bullet}m.
\]

For this proof choose an idempotent left unit of `a`, use it as the fixer of
`a • m`, and apply translation's right-convolution identity.

The abbreviation `scalars μ hM` installs the published
`Algebra.NondegenerateScalars.module ℂ (idempotented μ) hM` locally on the
original additive carrier. Its scalar formula is
`c • m = (c • e) • m` for any fixing idempotent. In `recovered μ hM`,
additivity of the group operators comes from the right-limit action;
complex linearity follows from this scalar formula, linearity of translation,
and compatibility of the canonical scalar structure with the original
`H`-action. The identity and group multiplication laws follow from
`L_1 e = e`, `L_(g h) e = L_g (L_h e)`, and `act_smul`.

For `recovered_smooth`, choose a fixing idempotent `e` of `m` and an open
subgroup fixing `e` in the smooth regular representation. The same subgroup
fixes `m`, because `(L_k e) • m = e • m = m`.

## Identifying the integrated action

This step checks the action of every actual test function, rather than only
normalized subgroup indicators.

`integrated_regular` shows that the integrated regular representation is
convolution. Apply each algebraic point-evaluation functional to the integrated
vector. The published `integratedAction_dual` turns the result into

\[
\int_G f(y)a(y^{-1}x)\,d\mu(y),
\]

which is the defining value of `(f * a)(x)`.

For each original module vector `m`, `evaluation μ hM m` is the complex-linear
intertwiner `T_m : H → M`, `a ↦ a • m`. Its linearity is canonical scalar
action compatibility, and its group intertwining law is exactly `act_smul`.
If `e • m = m`, the published naturality of integration for intertwiners gives

\[
\begin{aligned}
\pi(f)m
 &= \pi(f)T_m(e) \\
 &= T_m\bigl(\pi_{\mathrm{reg}}(f)e\bigr) \\
 &= T_m(f*e) \\
 &= f\mathbin{\bullet}(e\mathbin{\bullet}m)
  = f\mathbin{\bullet}m.
\end{aligned}
\]

This is `integrated_recovered`. Thus `recoveredObject μ M` is a smooth
representation on the original carrier, and `recoveredIso μ M` is an
isomorphism from its image under the published functor to `M`, with the
identity additive map in both directions. These isomorphisms prove `essSurj`.
The regular representation and the evaluation intertwiner may have carriers
in different universes; the published integration lemmas permit this, so
this argument imposes no relation between `u` and `v`.

## Fullness, faithfulness and the exact target

For a morphism between the integrated modules of smooth representations,
`underlying` exposes the original additive module homomorphism through the
category wrappers. Choose an idempotent fixing a vector `m`. The same
idempotent fixes its image under that homomorphism.

`map_complex` proves complex linearity using
`c • m = (c • e) • m` and compatibility with the action of `c • e`.
`map_group` proves group equivariance using the published identity
`integratedAction_leftTranslate`: the integrated action of `L_g e` on `m`
is `ρ(g)m` because `e` fixes `m`. Compatibility with `L_g e` then gives the
required group intertwining equation. `preimage` bundles this same map as a
morphism of smooth representations. Its image under the published functor
is the original module map, proving `full`.

The proof of `faithful` uses extensionality: the published functor preserves
the entire underlying map, so equality of its images gives equality of the
original smooth morphisms.

The final theorem introduces exactly the parameters of the published
statement and fills Mathlib's `Functor.IsEquivalence` with `faithful`, `full`
and `essSurj`. It adds no hypothesis. The statement's Lean/Markdown pair and
all its imports are unchanged. The intermediate translation families,
regular representation, evaluation maps and categorical witnesses are
internal constructions supporting this proof; they are not additional
assumed statements from the literature.

## Main reused results

- [NondegenerateModuleFunctor](NondegenerateModuleFunctor.md): the exact
  published functor, its original integrated module action and nondegeneracy.
- [LocalUnitsProof](LocalUnitsProof.md) and
  [CommonInvarianceProof](CommonInvarianceProof.md): compact-open two-sided
  local units and common bi-invariance of actual test functions.
- [NondegenerateScalars](../../Algebra/NondegenerateScalars.md): canonical
  complex scalars on the original additive nondegenerate carrier.
- [IdempotentedRingRightLimitAction](../../Algebra/IdempotentedRingRightLimitAction.md):
  independence of the fixing idempotent and additivity of the extended action.
- [IntegratedAction](IntegratedAction.md) and
  [IntegratedConvolution](IntegratedConvolution.md): algebraic integration,
  scalarization, naturality for intertwiners and the left-translation identity.
- Mathlib `CategoryTheory.Functor.IsEquivalence`: the criterion combining
  fullness, faithfulness and essential surjectivity.
