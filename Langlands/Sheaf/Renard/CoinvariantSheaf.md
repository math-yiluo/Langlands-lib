# Renard III.3.1: the actual coinvariant sheaf

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, III.3.1, printed p.83 / PDF p.89, the paragraph
following the Definition, constructing `F′` from the nondegenerate
`D(Y)`-module `F_c(X)_G`. The following Proposition is on the same page;
its proof continues on printed p.84 / PDF p.90. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

All declarations have prefix `Langlands.Sheaf.Renard.CoinvariantSheaf`.
This module constructs the sheaf and canonical maps. It asserts no
isomorphism or fibre formula.

The base spaces `X Y : Type` have explicit predicates `hX` and `hY`
expressing Hausdorffness and compact-open neighbourhood bases. The group
`G : Type uG` has a topology, acts jointly continuously on `X`, and has an
independent universe. `q : C(X,Y)` is the actual continuous map; its actual
invariance is `hq : ∀ g x, q(g • x)=q x`. Coefficients, original sheaf
section carriers, and original compact-section and quotient carriers are
universe-zero complex vector spaces. No smoothness, properness,
surjectivity, transitivity or sigma-compactness is required by these
construction declarations. Renard's t.d. topological group is a
specialization.

`sourceModules` first applies the actual
`CompactSectionActions.functor hX`, retaining every original compact
section and the original group operators. It then applies the published
`CoinvariantTestModule.sourceFunctor`: the same original carrier is a
nondegenerate target-test module by smooth pullback multipliers along `q`.
The pullback of a compact test on `Y` need not be compactly supported on
`X`; the existing construction uses the full locally constant multiplier
action and makes no such support assumption.

`modules` uses the same forward compact-section functor, followed by the
published `CoinvariantTestModule.functor q hq hY`. Its carrier is the
literal existing `Representation.Coinvariants` of the forward functor's
canonical-complex action. That action has the original compact-section
group operators and complex multiplication; the forward construction
proves their compatibility with the recovered complex structure. The
quotient and target-test action are those of `CoinvariantTestModule`,
with the original nondegeneracy proof. `quotient` is the existing natural
quotient transformation whiskered by the forward functor;
`quotient_apply` records its exact original representative formula.

`functor hX q hq hY` is Renard's `F ↦ F′`: it applies the published
`ProjectorVectorSheaf.functor hY` to this actual coinvariant module.
`functor_obj` states the exact original projector sheaf. The source and
target are the existing action-sheaf and ordinary complex-vector-sheaf
categories; all maps are compositions of the original functor maps.

`compactComparison` applies the published
`ModuleProjectorComparison.moduleComparisonNat` to the actual coinvariant
module. It is the canonical map from that module to the actual compact
sections of `F′`, sending a vector to the global compatible family whose
component at compact open `W` is its original `χ_W` projection. This is a
natural transformation of nondegenerate target-test modules. No
invertibility is supplied or assumed.

`compactQuotient` is the original quotient followed by that canonical
comparison. `compactQuotient_action` shows that it sends every original
translated compact section to the same image as the section, by the
published representation-coinvariant quotient equation and congruence
under the canonical comparison. Naturality is inherited from the two
actual transformations.

The claim that `compactComparison` is an isomorphism, the actual
closed-fibre restriction and canonical stalk comparison, the III.3.1
Proposition and the distribution Corollary remain separate statements and
proof obligations. This construction does not assume any of them.
