# Compact-coefficient classes under topological group equivalences

Worker 202 constructs the contravariant equivalence of the existing actual
compact-coefficient irreducible smooth representation classes. For a continuous
multiplicative equivalence `e : H ≃ₜ* G`, a representation `ρ` of `G` pulls back
to `ρ.comp e.toMonoidHom`, with action

\[
(e^*\rho)(h)v=\rho(e(h))v.
\]

The vector space, additive group, and complex module structure stay the same.
The groups have independent universes `uG` and `uH`; carriers have an independent
universe `uV`. Transported maps allow another independent carrier universe `uW`.
Only group and topology instances are needed: continuity of multiplication and
inversion on those groups is not assumed. The supplied equivalence is both
multiplicative and a homeomorphism. No admissibility or finite dimension is used.

## Algebraic dual, smoothness, coefficients, and irreducibility

The shared algebraic-dual and smoothness identities are imported from
[`Smooth.Transfer.GroupEquivalence`](../Smooth/Transfer/GroupEquivalence.md).
In namespace `Langlands`, `dual_comp_monoidHom` identifies the actual dual of a
pullback with the pullback of the dual, and
`isSmoothVector_comp_continuousMulEquiv_iff` and
`isSmoothVector_dual_comp_continuousMulEquiv_iff` identify the respective
smooth-vector conditions. They retain arbitrary carriers and independent group
universes.

`matrixCoefficient_comp_monoidHom` is the identity

\[
 c_{e^*\rho,\ell,v}=c_{\rho,\ell,v}\circ e.
\]

`hasCompactSmoothDualCoefficients_comp_continuousMulEquiv_iff` says
`HasCompactSmoothDualCoefficients (ρ.comp e.toMonoidHom) ↔
HasCompactSmoothDualCoefficients ρ`. In the direction from the original action,
the preceding smooth-dual equivalence makes its compact-support hypothesis
applicable, and Mathlib's `HasCompactSupport.comp_homeomorph` pulls that support
back through `e.toHomeomorph`. In the other direction, the same smooth-dual
equivalence supplies a smooth functional for the pulled-back dual. The resulting
coefficient is precomposed with `e.symm.toHomeomorph`; cancellation of `e` and
`e.symm` gives the original coefficient. The proof uses actual topological
compact support and actual smooth dual vectors throughout.

`isIrreducible_comp_continuousMulEquiv_iff` proves the analogous equivalence for
Mathlib's `Representation.IsIrreducible`. It reuses
`CuspidalSupport.isIrreducible_comp_of_surjective` for `e` and `e.symm` and again
cancels the successive pullbacks. Nonzeroness is retained as part of this
existing irreducibility predicate.

## Actual objects and maps

Within `Langlands.SmoothRep`:

- `pullbackMap` takes an actual intertwiner to an intertwiner of the pulled-back
  actions, preserving its linear map. `pullbackMap_toLinearMap` is the exact
  equality of underlying linear maps. Its proof of equivariance evaluates the
  original equivariance equation at `e h`.
- `pullbackEquiv` transports an actual equivariant linear equivalence, reusing
  `CuspidalSupport.equivComp`. `pullbackEquiv_toLinearEquiv` states that the
  underlying linear equivalence is unchanged. Both constructions allow
  independent source and target carrier universes.
- `pullback` bundles the pulled-back action with smoothness proved by the
  published `isSmooth_comp`. `pullback_representation` gives its actual action.
- `pullbackFunctor` maps the existing smooth categories using these objects and
  maps. Its identity and composition laws are definitional equalities.

Within `Langlands.IrreducibleCompactCoefficientRep`, `pullback` bundles the
smooth pullback with the two preservation results. `pullback_apply` states the
pointwise action `h ↦ ρ (e h)`. `pullbackIso` transports actual categorical
isomorphisms using the smooth pullback functor and the existing full-subcategory
inclusions. `isoOfEquiv` promotes an equivariant linear equivalence to an
isomorphism in this full subcategory.

The comparison isomorphisms `pullbackReflIso`, `pullbackTransIso`, and
`pullbackSymmIso` all have the identity linear map. The first compares identity
pullback with the original object; the second compares composed pullback with
two successive pullbacks; the third compares pullback followed by inverse
pullback with the original object. Their equivariance proofs are definitional
except for the inverse cancellation in `pullbackSymmIso`.

## The existing class quotient and its laws

All names below are in `Langlands.CompactCoefficientClass`.
`pullback` descends the actual representative construction through the existing
`isIsomorphicSetoid`. Its well-definedness proof transports an actual
isomorphism with `IrreducibleCompactCoefficientRep.pullbackIso` and applies
`ofRep_eq_iff`. `pullback_ofRep` is its definitional representative formula;
`pullback_ofRep_eq` records representative independence from equality of original
classes. Nothing chooses a representative or resizes a universe.

`pullbackEquiv e` is the actual equivalence

\[
 \operatorname{CompactCoefficientClass}^{u_G,u_V}(G)
 \simeq
 \operatorname{CompactCoefficientClass}^{u_H,u_V}(H).
\]

Its forward map is `pullback e` and its inverse is `pullback e.symm`.
`pullbackEquiv_ofRep` states exactly

```
pullbackEquiv e (ofRep A) =
  ofRep (IrreducibleCompactCoefficientRep.pullback e A).
```

`pullback_refl`, `pullback_trans`, and `pullback_symm_pullback` first prove the
class-level laws by quotient induction using the actual comparison
isomorphisms. The equivalence laws are `pullbackEquiv_refl`,
`pullbackEquiv_trans`, and `pullbackEquiv_symm`. Their direction is explicit:
for `f : J ≃ₜ* H` and `e : H ≃ₜ* G`,

\[
 (f\mathbin{\mathrm{.trans}}e)^*=f^*\circ e^*,
 \qquad (e^*)^{-1}=(e^{-1})^*.
\]

In Lean, the composition equality is
`pullbackEquiv (f.trans e) = (pullbackEquiv e).trans (pullbackEquiv f)`.
The third group universe `uJ` is also independent.

For every subgroup `K ≤ H`, `hasFixedVector_pullbackEquiv` proves

```
HasFixedVector K (pullbackEquiv e a) ↔
  HasFixedVector (K.comap e.symm.toMonoidHom) a.
```

The subgroup on the right is the image under `e`, written as inverse comap.
The proof reduces by quotient induction to the published exact equality
`fixedVectors_comp_mulEquiv` on actual submodules. No compactness or openness
of `K` is required. `mem_fixedStratum_pullbackEquiv` is the corresponding
membership law for the existing `fixedStratum` sets. It asserts no finiteness.

## Internal provenance and original motivation

This generic transport equivalence and its intrinsic construction laws are
internal constructions from the existing Library objects. They are not a
verbatim theorem attributed to the original literature. The motivation and
convention come from I. N. Bernshtein and A. V. Zelevinskii, *Representations of
the group GL(n,F), where F is a non-Archimedean local field*, Russian Mathematical
Surveys **31**:3 (1976), 1–68, English translation:

- Literature ID: `bernstein-zelevinsky-1976-representations-gln`.
- SHA256: `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
- Retained PDF: `/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.
- Read locators: §2.27, printed/PDF p.23, defines automorphism pullback on the
  same vector space in the direction used here; §§2.39–2.40, p.26, define matrix
  elements against the smooth dual and the compact-support condition; §4.17,
  pp.41–42, motivates the compact-coefficient class index through a projector
  sum on the determinant-unit subgroup.

The source calls these representations “finite,” meaning the compact-support
condition, not finite dimension. The coefficient convention is exactly that of
the imported `HasCompactSmoothDualCoefficients`: `g ↦ ℓ (ρ g v)`. The source
uses `g⁻¹`; their equivalence for topological groups is explained in the
published `Classes.md`. This module transports the existing predicate without
altering it. It claims no new extension of the source's representation-theoretic
theorems to arbitrary groups with a topology.

All mathematics is imported by Lean names from the current Library. Besides
`Classes`, the module imports `CuspidalSupport.GroupTransport` for smooth
pullback and subgroup transport, and `CuspidalTensorAssociationProof` to reuse
its general algebraic irreducibility and representation-equivalence pullback
lemmas. The shared dual and smoothness identities retain their original
statements and proofs in `Smooth.Transfer.GroupEquivalence`. This unit constructs no
isotypic projector, transports no intrinsic isotypic or annihilator subspace,
and proves no product-Levi decomposition or induction theorem from §2.27.
